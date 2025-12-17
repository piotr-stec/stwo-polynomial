use std::simd::u32x16;

use itertools::{Itertools, chain};
use num_traits::{One, Zero};
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use tracing::{Level, span};

use super::BlakeElements;
use crate::blake3::blake3;
use crate::blake3::round::{BlakeRoundInput, RoundElements};
use crate::blake3::{N_ROUND_INPUT_FELTS, N_ROUNDS, STATE_SIZE, to_felts};
use crate::fibonacci::ValueRelation;

#[derive(Copy, Clone, Default)]
pub struct BlakeInput {
    pub v: [u32x16; STATE_SIZE],
    pub m: [u32x16; STATE_SIZE],
}

#[derive(Clone)]
pub struct BlakeSchedulerLookupData {
    pub round_lookups: [[BaseColumn; N_ROUND_INPUT_FELTS]; N_ROUNDS],
    pub blake_lookups: [BaseColumn; N_ROUND_INPUT_FELTS],
}
impl BlakeSchedulerLookupData {
    fn new(log_size: u32) -> Self {
        Self {
            round_lookups: std::array::from_fn(|_| {
                std::array::from_fn(|_| unsafe { BaseColumn::uninitialized(1 << log_size) })
            }),
            blake_lookups: std::array::from_fn(|_| unsafe {
                BaseColumn::uninitialized(1 << log_size)
            }),
        }
    }
}

pub fn prepare_blake_input_from_u32(value: u32) -> BlakeInput {
    // Pad to 64 bytes
    let mut padded = [0u8; 64];
    padded[..4].copy_from_slice(&value.to_le_bytes());

    // Convert to message
    let message: [u32; 16] = std::array::from_fn(|i| {
        u32::from_le_bytes([
            padded[i * 4],
            padded[i * 4 + 1],
            padded[i * 4 + 2],
            padded[i * 4 + 3],
        ])
    });

    // Blake3 IV
    const IV: [u32; 8] = [
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB,
        0x5BE0CD19,
    ];

    // Initialize state
    let mut v = [0u32; 16];
    v[0..8].copy_from_slice(&IV);
    v[8..12].copy_from_slice(&IV[0..4]);
    v[12] = 0; // counter_low
    v[13] = 0; // counter_high  
    v[14] = 4; // block_len (4 bytes for u32)
    v[15] = 0b1011; // CHUNK_START | CHUNK_END | ROOT

    // Convert to SIMD
    BlakeInput {
        v: v.map(u32x16::splat),
        m: message.map(u32x16::splat),
    }
}

pub fn gen_trace(
    log_size: u32,
    fibonacci_value: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    BlakeSchedulerLookupData,
    Vec<BlakeRoundInput>,
) {
    let blake_input = prepare_blake_input_from_u32(fibonacci_value);
    let inputs = vec![blake_input; 1 << (log_size - LOG_N_LANES)];

    let _span = span!(Level::INFO, "Scheduler Generation").entered();
    let mut lookup_data = BlakeSchedulerLookupData::new(log_size);
    let mut round_inputs = Vec::with_capacity(inputs.len() * N_ROUNDS);

    // Calculate number of columns:
    // 16*2 (messages) + 16*2 (initial_v) + 7*16*2 (v after each round)
    // = 32 + 32 + 224 = 288 columns
    let n_cols = STATE_SIZE * 2 + STATE_SIZE * 2 + N_ROUNDS * STATE_SIZE * 2;

    let mut trace = (0..n_cols)
        .map(|_| unsafe { BaseColumn::uninitialized(1 << log_size) })
        .collect_vec();

    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let mut col_index = 0; // Start from column 0

        let mut write_u32_array = |x: [u32x16; STATE_SIZE], col_index: &mut usize| {
            x.iter().for_each(|x| {
                to_felts(x).iter().for_each(|x| {
                    trace[*col_index].data[vec_row] = *x;
                    *col_index += 1;
                });
            });
        };

        let BlakeInput { mut v, m } = inputs.get(vec_row).copied().unwrap_or_default();
        let initial_v = v;

        write_u32_array(m, &mut col_index);
        write_u32_array(v, &mut col_index);

        // Blake3 permutes message BETWEEN rounds using MSG_SCHEDULE
        let mut m_current = m;

        for r in 0..N_ROUNDS {
            let prev_v = v;
            blake3::round(&mut v, m_current, r);
            write_u32_array(v, &mut col_index);

            // Pass current message state to round_inputs
            round_inputs.push(BlakeRoundInput {
                v: prev_v,
                m: m_current,
            });

            chain![
                prev_v.iter().flat_map(to_felts),
                v.iter().flat_map(to_felts),
                m_current.iter().flat_map(to_felts)
            ]
            .enumerate()
            .for_each(|(i, val)| lookup_data.round_lookups[r][i].data[vec_row] = val);

            // Permute message for next round
            m_current = blake3::MSG_SCHEDULE.map(|i| m_current[i as usize]);
        }

        chain![
            initial_v.iter().flat_map(to_felts),
            v.iter().flat_map(to_felts),
            m.iter().flat_map(to_felts)
        ]
        .enumerate()
        .for_each(|(i, val)| lookup_data.blake_lookups[i].data[vec_row] = val);
    }

    println!(
        "Blake scheduler total vec_rows: {}",
        1 << (log_size - LOG_N_LANES)
    );

    let domain = CanonicCoset::new(log_size).circle_domain();
    let trace = trace
        .into_iter()
        .map(|eval| CircleEvaluation::new(domain, eval))
        .collect();

    (trace, lookup_data, round_inputs)
}

pub fn gen_interaction_trace(
    log_size: u32,
    lookup_data: BlakeSchedulerLookupData,
    round_lookup_elements: &RoundElements,
    blake_lookup_elements: &BlakeElements,
    input_trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    preprocessed: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    value_relation: &ValueRelation,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let _span = span!(Level::INFO, "Generate scheduler interaction trace").entered();

    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // First, generate round pair columns (will be at beginning to match evaluate order)
    for [l0, l1] in lookup_data.round_lookups.array_chunks::<2>() {
        let mut col_gen = logup_gen.new_col();

        #[allow(clippy::needless_range_loop)]
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let p0: PackedSecureField =
                round_lookup_elements.combine(&l0.each_ref().map(|l| l.data[vec_row]));
            let p1: PackedSecureField =
                round_lookup_elements.combine(&l1.each_ref().map(|l| l.data[vec_row]));
            #[allow(clippy::eq_op)]
            col_gen.write_frac(vec_row, p0 + p1, p0 * p1);
        }

        col_gen.finalize_col();
    }

    // Last pair (round6 + blake) - this matches the pairing in eval_blake_scheduler_constraints
    {
        let mut col_gen = logup_gen.new_col();
        #[allow(clippy::needless_range_loop)]
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let p_blake: PackedSecureField = blake_lookup_elements.combine(
                &lookup_data
                    .blake_lookups
                    .each_ref()
                    .map(|l| l.data[vec_row]),
            );
            if N_ROUNDS % 2 == 1 {
                let p_round: PackedSecureField = round_lookup_elements.combine(
                    &lookup_data.round_lookups[N_ROUNDS - 1]
                        .each_ref()
                        .map(|l| l.data[vec_row]),
                );
                col_gen.write_frac(vec_row, p_blake, p_round * p_blake);
            } else {
                col_gen.write_frac(vec_row, PackedSecureField::zero(), p_blake);
            }
        }
        col_gen.finalize_col();
    }

    {
        let mut col_gen = logup_gen.new_col();

        let m0_col = &input_trace[0];
        let is_first_col = &preprocessed[0]; // First preprocessed column is is_first

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let m0_packed = m0_col.values.data[vec_row];
            let is_first_packed = is_first_col.values.data[vec_row];

            let denom = value_relation.combine(&[PackedSecureField::from(m0_packed)]);
            let numerator = PackedSecureField::from(is_first_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}
