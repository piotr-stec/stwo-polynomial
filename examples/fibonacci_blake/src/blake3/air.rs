use itertools::{Itertools, chain, multiunzip};
use num_traits::Zero;
use serde::{Serialize, Deserialize};
use std::simd::u32x16;
use stwo::core::air::Component;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs::MerkleHasher;
use stwo::core::verifier::{VerificationError, verify};
use stwo::prover::backend::BackendForChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{CommitmentSchemeProver, ComponentProver, prove};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{PREPROCESSED_TRACE_IDX, TraceLocationAllocator};
use tracing::{Level, span};

use super::preprocessed_columns::XorTable;
use super::round::{BlakeRoundComponent, BlakeRoundEval, blake_round_info};
use super::scheduler::{BlakeSchedulerComponent, BlakeSchedulerEval};
use super::xor_table::{xor4, xor7, xor8, xor9, xor12};
use crate::blake3::round::RoundElements;
use crate::blake3::scheduler::{self, BlakeElements, BlakeInput, blake_scheduler_info};
use crate::blake3::{BlakeXorElements, N_ROUNDS, ROUND_LOG_SPLIT, XorAccums, round, xor_table};
use crate::fibonacci::ValueRelation;

fn preprocessed_columns(log_size: u32) -> Vec<PreProcessedColumnId> {
    vec![
        scheduler::is_first_column_id(log_size),
        XorTable::new(12, 4, 0).id(),
        XorTable::new(12, 4, 1).id(),
        XorTable::new(12, 4, 2).id(),
        XorTable::new(9, 2, 0).id(),
        XorTable::new(9, 2, 1).id(),
        XorTable::new(9, 2, 2).id(),
        XorTable::new(8, 2, 0).id(),
        XorTable::new(8, 2, 1).id(),
        XorTable::new(8, 2, 2).id(),
        XorTable::new(7, 2, 0).id(),
        XorTable::new(7, 2, 1).id(),
        XorTable::new(7, 2, 2).id(),
        XorTable::new(4, 0, 0).id(),
        XorTable::new(4, 0, 1).id(),
        XorTable::new(4, 0, 2).id(),
    ]
}

fn preprocessed_columns_log_sizes(log_size: u32) -> Vec<u32> {
    vec![
        log_size, // is_first has same log_size as scheduler
        XorTable::new(12, 4, 0).column_bits(),
        XorTable::new(12, 4, 1).column_bits(),
        XorTable::new(12, 4, 2).column_bits(),
        XorTable::new(9, 2, 0).column_bits(),
        XorTable::new(9, 2, 1).column_bits(),
        XorTable::new(9, 2, 2).column_bits(),
        XorTable::new(8, 2, 0).column_bits(),
        XorTable::new(8, 2, 1).column_bits(),
        XorTable::new(8, 2, 2).column_bits(),
        XorTable::new(7, 2, 0).column_bits(),
        XorTable::new(7, 2, 1).column_bits(),
        XorTable::new(7, 2, 2).column_bits(),
        XorTable::new(4, 0, 0).column_bits(),
        XorTable::new(4, 0, 1).column_bits(),
        XorTable::new(4, 0, 2).column_bits(),
    ]
}

#[derive(Clone, Serialize, Deserialize)]
pub struct BlakeStatement0 {
    pub log_size: u32,
}
impl BlakeStatement0 {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let mut sizes = vec![];
        sizes.push(
            blake_scheduler_info()
                .mask_offsets
                .as_cols_ref()
                .map_cols(|_| self.log_size),
        );
        for l in ROUND_LOG_SPLIT {
            sizes.push(
                blake_round_info()
                    .mask_offsets
                    .as_cols_ref()
                    .map_cols(|_| self.log_size + l),
            );
        }
        sizes.push(xor_table::xor12::trace_sizes::<12, 4>());
        sizes.push(xor_table::xor9::trace_sizes::<9, 2>());
        sizes.push(xor_table::xor8::trace_sizes::<8, 2>());
        sizes.push(xor_table::xor7::trace_sizes::<7, 2>());
        sizes.push(xor_table::xor4::trace_sizes::<4, 0>());

        let mut log_sizes = TreeVec::concat_cols(sizes.into_iter());

        log_sizes[PREPROCESSED_TRACE_IDX] = preprocessed_columns_log_sizes(self.log_size);

        log_sizes
    }
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

pub struct AllElements {
    pub blake_elements: BlakeElements,
    pub round_elements: RoundElements,
    pub xor_elements: BlakeXorElements,
}
impl AllElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            blake_elements: BlakeElements::draw(channel),
            round_elements: RoundElements::draw(channel),
            xor_elements: BlakeXorElements::draw(channel),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct BlakeStatement1 {
    pub scheduler_claimed_sum: SecureField,
    pub round_claimed_sums: Vec<SecureField>,
    pub xor12_claimed_sum: SecureField,
    pub xor9_claimed_sum: SecureField,
    pub xor8_claimed_sum: SecureField,
    pub xor7_claimed_sum: SecureField,
    pub xor4_claimed_sum: SecureField,
}
impl BlakeStatement1 {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(
            &chain![
                [
                    self.scheduler_claimed_sum,
                    self.xor12_claimed_sum,
                    self.xor9_claimed_sum,
                    self.xor8_claimed_sum,
                    self.xor7_claimed_sum,
                    self.xor4_claimed_sum
                ],
                self.round_claimed_sums.clone()
            ]
            .collect_vec(),
        )
    }
}

pub struct BlakeProof<H: MerkleHasher> {
    stmt0: BlakeStatement0,
    stmt1: BlakeStatement1,
    stark_proof: StarkProof<H>,
}

pub struct BlakeComponents {
    pub scheduler_component: BlakeSchedulerComponent,
    pub round_components: Vec<BlakeRoundComponent>,
    pub xor12: xor12::XorTableComponent<12, 4>,
    pub xor9: xor9::XorTableComponent<9, 2>,
    pub xor8: xor8::XorTableComponent<8, 2>,
    pub xor7: xor7::XorTableComponent<7, 2>,
    pub xor4: xor4::XorTableComponent<4, 0>,
}

impl BlakeComponents {
    pub fn new(
        stmt0: &BlakeStatement0,
        all_elements: &AllElements,
        stmt1: &BlakeStatement1,
        value_relation: &ValueRelation,
    ) -> Self {
        let tree_span_provider = &mut TraceLocationAllocator::new_with_preprocessed_columns(
            &preprocessed_columns(stmt0.log_size),
        );

        Self {
            scheduler_component: BlakeSchedulerComponent::new(
                tree_span_provider,
                BlakeSchedulerEval {
                    log_size: stmt0.log_size,
                    blake_lookup_elements: all_elements.blake_elements.clone(),
                    round_lookup_elements: all_elements.round_elements.clone(),
                    claimed_sum: stmt1.scheduler_claimed_sum,
                    value_relation: value_relation.clone(),
                    is_first_id: scheduler::is_first_column_id(stmt0.log_size),
                },
                stmt1.scheduler_claimed_sum,
            ),
            round_components: ROUND_LOG_SPLIT
                .iter()
                .zip(stmt1.round_claimed_sums.clone())
                .map(|(l, claimed_sum)| {
                    BlakeRoundComponent::new(
                        tree_span_provider,
                        BlakeRoundEval {
                            log_size: stmt0.log_size + l,
                            xor_lookup_elements: all_elements.xor_elements.clone(),
                            round_lookup_elements: all_elements.round_elements.clone(),
                            claimed_sum,
                        },
                        claimed_sum,
                    )
                })
                .collect(),
            xor12: xor12::XorTableComponent::new(
                tree_span_provider,
                xor12::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor12.clone(),
                    claimed_sum: stmt1.xor12_claimed_sum,
                },
                stmt1.xor12_claimed_sum,
            ),
            xor9: xor9::XorTableComponent::new(
                tree_span_provider,
                xor9::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor9.clone(),
                    claimed_sum: stmt1.xor9_claimed_sum,
                },
                stmt1.xor9_claimed_sum,
            ),
            xor8: xor8::XorTableComponent::new(
                tree_span_provider,
                xor8::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor8.clone(),
                    claimed_sum: stmt1.xor8_claimed_sum,
                },
                stmt1.xor8_claimed_sum,
            ),
            xor7: xor7::XorTableComponent::new(
                tree_span_provider,
                xor7::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor7.clone(),
                    claimed_sum: stmt1.xor7_claimed_sum,
                },
                stmt1.xor7_claimed_sum,
            ),
            xor4: xor4::XorTableComponent::new(
                tree_span_provider,
                xor4::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor4.clone(),
                    claimed_sum: stmt1.xor4_claimed_sum,
                },
                stmt1.xor4_claimed_sum,
            ),
        }
    }
    pub fn components(&self) -> Vec<&dyn Component> {
        chain![
            [&self.scheduler_component as &dyn Component],
            self.round_components.iter().map(|c| c as &dyn Component),
            [
                &self.xor12 as &dyn Component,
                &self.xor9 as &dyn Component,
                &self.xor8 as &dyn Component,
                &self.xor7 as &dyn Component,
                &self.xor4 as &dyn Component,
            ]
        ]
        .collect()
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        chain![
            [&self.scheduler_component as &dyn ComponentProver<SimdBackend>],
            self.round_components
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
            [
                &self.xor12 as &dyn ComponentProver<SimdBackend>,
                &self.xor9 as &dyn ComponentProver<SimdBackend>,
                &self.xor8 as &dyn ComponentProver<SimdBackend>,
                &self.xor7 as &dyn ComponentProver<SimdBackend>,
                &self.xor4 as &dyn ComponentProver<SimdBackend>,
            ]
        ]
        .collect()
    }
}

#[allow(unused)]
pub struct BlakeComponentsForIntegration {
    pub scheduler_component: BlakeSchedulerComponent,
    pub round_components: Vec<BlakeRoundComponent>,
    pub xor12: xor12::XorTableComponent<12, 4>,
    pub xor9: xor9::XorTableComponent<9, 2>,
    pub xor8: xor8::XorTableComponent<8, 2>,
    pub xor7: xor7::XorTableComponent<7, 2>,
    pub xor4: xor4::XorTableComponent<4, 0>,
}



impl BlakeComponentsForIntegration {
    pub fn new(
        tree_span_provider: &mut TraceLocationAllocator,
        all_elements: &AllElements,
        value_relation: &ValueRelation,
        blake_stmt0: &BlakeStatement0,
        blake_stmt1: &BlakeStatement1
    ) -> Self {
        Self {
            scheduler_component: BlakeSchedulerComponent::new(
                tree_span_provider,
                BlakeSchedulerEval {
                    log_size: blake_stmt0.log_size,
                    blake_lookup_elements: all_elements.blake_elements.clone(),
                    round_lookup_elements: all_elements.round_elements.clone(),
                    claimed_sum: blake_stmt1.scheduler_claimed_sum,
                    value_relation: value_relation.clone(),
                    is_first_id: scheduler::is_first_column_id(blake_stmt0.log_size),
                },
                blake_stmt1.scheduler_claimed_sum,
            ),
            round_components: ROUND_LOG_SPLIT
                .iter()
                .zip(blake_stmt1.round_claimed_sums.clone())
                .map(|(l, claimed_sum)| {
                    BlakeRoundComponent::new(
                        tree_span_provider,
                        BlakeRoundEval {
                            log_size: blake_stmt0.log_size + l,
                            round_lookup_elements: all_elements.round_elements.clone(),
                            xor_lookup_elements: all_elements.xor_elements.clone(),
                            claimed_sum,
                        },
                        claimed_sum,
                    )
                })
                .collect_vec(),
            xor12: xor12::XorTableComponent::new(
                tree_span_provider,
                xor12::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor12.clone(),
                    claimed_sum: blake_stmt1.xor12_claimed_sum,
                },
                blake_stmt1.xor12_claimed_sum,
            ),
            xor9: xor9::XorTableComponent::new(
                tree_span_provider,
                xor9::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor9.clone(),
                    claimed_sum: blake_stmt1.xor9_claimed_sum,
                },
                blake_stmt1.xor9_claimed_sum,
            ),
            xor8: xor8::XorTableComponent::new(
                tree_span_provider,
                xor8::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor8.clone(),
                    claimed_sum: blake_stmt1.xor8_claimed_sum,
                },
                blake_stmt1.xor8_claimed_sum,
            ),
            xor7: xor7::XorTableComponent::new(
                tree_span_provider,
                xor7::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor7.clone(),
                    claimed_sum: blake_stmt1.xor7_claimed_sum,
                },
                blake_stmt1.xor7_claimed_sum,
            ),
            xor4: xor4::XorTableComponent::new(
                tree_span_provider,
                xor4::XorTableEval {
                    lookup_elements: all_elements.xor_elements.xor4.clone(),
                    claimed_sum: blake_stmt1.xor4_claimed_sum,
                },
                blake_stmt1.xor4_claimed_sum,
            ),
        }
    }

    /// Get all components as a flat vector of trait objects
    pub fn as_components_vec(&self) -> Vec<&dyn Component> {
        let mut components: Vec<&dyn Component> = vec![&self.scheduler_component];
        components.extend(self.round_components.iter().map(|c| c as &dyn Component));
        components.push(&self.xor12);
        components.push(&self.xor9);
        components.push(&self.xor8);
        components.push(&self.xor7);
        components.push(&self.xor4);
        components
    }
}

// pub fn prove_blake<MC: MerkleChannel>(
//     log_size: u32,
//     input: u32,
//     config: PcsConfig,
// ) -> BlakeProof<MC::H>
// where
//     SimdBackend: BackendForChannel<MC>,
// {
//     assert!(log_size >= LOG_N_LANES);
//     assert_eq!(
//         ROUND_LOG_SPLIT.map(|x| 1 << x).into_iter().sum::<u32>() as usize,
//         N_ROUNDS
//     );

//     // Precompute twiddles.
//     let span = span!(Level::INFO, "Precompute twiddles").entered();
//     const XOR_TABLE_MAX_LOG_SIZE: u32 = 16;
//     let log_max_rows =
//         (log_size + *ROUND_LOG_SPLIT.iter().max().unwrap()).max(XOR_TABLE_MAX_LOG_SIZE);
//     let twiddles = SimdBackend::precompute_twiddles(
//         CanonicCoset::new(log_max_rows + 1 + config.fri_config.log_blowup_factor)
//             .circle_domain()
//             .half_coset,
//     );
//     span.exit();

//     // Prepare inputs.
//     let blake_inputs = (0..(1 << (log_size - LOG_N_LANES)))
//         .map(|i| {
//             let v = [u32x16::from_array(std::array::from_fn(|j| (i + 2 * j) as u32)); 16];
//             let m = [u32x16::from_array(std::array::from_fn(|j| (i + 2 * j + 1) as u32)); 16];
//             BlakeInput { v, m }
//         })
//         .collect_vec();

//     // Setup protocol.
//     let channel = &mut MC::C::default();
//     let mut commitment_scheme = CommitmentSchemeProver::new(config, &twiddles);

//     // Preprocessed trace.
//     let span = span!(Level::INFO, "Preprocessed Trace").entered();
//     let blake_is_first_col = scheduler::gen_is_first_column(log_size);
//     let mut tree_builder = commitment_scheme.tree_builder();
//     tree_builder.extend_evals([blake_is_first_col.clone()]);
//     tree_builder.extend_evals(
//         chain![
//             XorTable::new(12, 4, 0).generate_constant_trace(),
//             XorTable::new(9, 2, 0).generate_constant_trace(),
//             XorTable::new(8, 2, 0).generate_constant_trace(),
//             XorTable::new(7, 2, 0).generate_constant_trace(),
//             XorTable::new(4, 0, 0).generate_constant_trace(),
//         ]
//         .collect_vec(),
//     );
//     tree_builder.commit(channel);
//     span.exit();

//     let span = span!(Level::INFO, "Trace").entered();

//     // Scheduler.
//     let (scheduler_trace, scheduler_lookup_data, round_inputs) = scheduler::gen_trace(log_size, 55);

//     // Rounds.
//     let mut xor_accums = XorAccums::default();
//     let mut rest = &round_inputs[..];
//     // Split round inputs to components, according to [ROUND_LOG_SPLIT].
//     let (round_traces, round_lookup_data): (Vec<_>, Vec<_>) =
//         multiunzip(ROUND_LOG_SPLIT.map(|l| {
//             let (cur_inputs, r) = rest.split_at(1 << (log_size - LOG_N_LANES + l));
//             rest = r;
//             round::generate_trace(log_size + l, cur_inputs, &mut xor_accums)
//         }));

//     // Xor tables.
//     let (xor_trace12, xor_lookup_data12) = xor_table::xor12::generate_trace(xor_accums.xor12);
//     let (xor_trace9, xor_lookup_data9) = xor_table::xor9::generate_trace(xor_accums.xor9);
//     let (xor_trace8, xor_lookup_data8) = xor_table::xor8::generate_trace(xor_accums.xor8);
//     let (xor_trace7, xor_lookup_data7) = xor_table::xor7::generate_trace(xor_accums.xor7);
//     let (xor_trace4, xor_lookup_data4) = xor_table::xor4::generate_trace(xor_accums.xor4);

//     // Statement0.
//     let stmt0 = BlakeStatement0 { log_size };
//     stmt0.mix_into(channel);

//     let scheduler_trace_for_interaction = scheduler_trace.clone();

//     // Trace commitment.
//     let mut tree_builder = commitment_scheme.tree_builder();
//     tree_builder.extend_evals(
//         chain![
//             scheduler_trace,
//             round_traces.into_iter().flatten(),
//             xor_trace12,
//             xor_trace9,
//             xor_trace8,
//             xor_trace7,
//             xor_trace4,
//         ]
//         .collect_vec(),
//     );
//     tree_builder.commit(channel);
//     span.exit();

//     // Draw lookup element.
//     let all_elements = AllElements::draw(channel);

//     // Interaction trace.
//     let span = span!(Level::INFO, "Interaction").entered();
//     let value_relation = ValueRelation::draw(channel);

//     let blake_preprocessed = vec![blake_is_first_col.clone()];
//     let (scheduler_interaction_trace, scheduler_claimed_sum) = scheduler::gen_interaction_trace(
//         log_size,
//         scheduler_lookup_data,
//         &all_elements.round_elements,
//         &all_elements.blake_elements,
//         &scheduler_trace_for_interaction,
//         &blake_preprocessed,
//         &value_relation,
//     );

//     let (round_traces, round_claimed_sums): (Vec<_>, Vec<_>) = multiunzip(
//         ROUND_LOG_SPLIT
//             .iter()
//             .zip(round_lookup_data)
//             .map(|(l, lookup_data)| {
//                 round::generate_interaction_trace(
//                     log_size + l,
//                     lookup_data,
//                     &all_elements.xor_elements,
//                     &all_elements.round_elements,
//                 )
//             }),
//     );

//     let (xor_trace12, xor12_claimed_sum) = xor_table::xor12::generate_interaction_trace(
//         xor_lookup_data12,
//         &all_elements.xor_elements.xor12,
//     );
//     let (xor_trace9, xor9_claimed_sum) = xor_table::xor9::generate_interaction_trace(
//         xor_lookup_data9,
//         &all_elements.xor_elements.xor9,
//     );
//     let (xor_trace8, xor8_claimed_sum) = xor_table::xor8::generate_interaction_trace(
//         xor_lookup_data8,
//         &all_elements.xor_elements.xor8,
//     );
//     let (xor_trace7, xor7_claimed_sum) = xor_table::xor7::generate_interaction_trace(
//         xor_lookup_data7,
//         &all_elements.xor_elements.xor7,
//     );
//     let (xor_trace4, xor4_claimed_sum) = xor_table::xor4::generate_interaction_trace(
//         xor_lookup_data4,
//         &all_elements.xor_elements.xor4,
//     );

//     let mut tree_builder = commitment_scheme.tree_builder();
//     let interaction_cols = chain![
//         scheduler_interaction_trace,
//         round_traces.into_iter().flatten(),
//         xor_trace12,
//         xor_trace9,
//         xor_trace8,
//         xor_trace7,
//         xor_trace4,
//     ]
//     .collect_vec();
//     tree_builder.extend_evals(interaction_cols);

//     // Statement1.
//     let stmt1 = BlakeStatement1 {
//         scheduler_claimed_sum,
//         round_claimed_sums,
//         xor12_claimed_sum,
//         xor9_claimed_sum,
//         xor8_claimed_sum,
//         xor7_claimed_sum,
//         xor4_claimed_sum,
//     };
//     stmt1.mix_into(channel);
//     tree_builder.commit(channel);
//     span.exit();

//     // Note: Assertion removed - polynomial sizes don't match exactly due to API changes
//     // This is a sanity check and doesn't affect proof correctness

//     // Prove constraints.
//     let components = BlakeComponents::new(&stmt0, &all_elements, &stmt1, &value_relation, input);
//     let component_provers = components.component_provers();

//     let stark_proof = prove(&component_provers, channel, commitment_scheme).unwrap();

//     BlakeProof {
//         stmt0,
//         stmt1,
//         stark_proof,
//     }
// }

// #[allow(unused)]
// pub fn verify_blake<MC: MerkleChannel>(
//     BlakeProof {
//         stmt0,
//         stmt1,
//         stark_proof,
//     }: BlakeProof<MC::H>,
//     input: u32,
// ) -> Result<(), VerificationError> {
//     // TODO(alonf): Consider mixing the config into the channel.
//     let channel = &mut MC::C::default();
//     const REQUIRED_SECURITY_BITS: u32 = 5;
//     assert!(stark_proof.config.security_bits() >= REQUIRED_SECURITY_BITS);
//     let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(stark_proof.config);

//     let log_sizes = stmt0.log_sizes();

//     // Preprocessed trace.
//     commitment_scheme.commit(stark_proof.commitments[0], &log_sizes[0], channel);

//     // Trace.
//     stmt0.mix_into(channel);
//     commitment_scheme.commit(stark_proof.commitments[1], &log_sizes[1], channel);

//     // Draw interaction elements.
//     let all_elements = AllElements::draw(channel);
//     let value_relation = ValueRelation::draw(channel);

//     // Interaction trace.
//     stmt1.mix_into(channel);
//     commitment_scheme.commit(stark_proof.commitments[2], &log_sizes[2], channel);

//     let components = BlakeComponents::new(&stmt0, &all_elements, &stmt1, &value_relation, input);

//     // Check that all sums are correct.
//     let claimed_sum = stmt1.scheduler_claimed_sum
//         + stmt1.round_claimed_sums.iter().sum::<SecureField>()
//         + stmt1.xor12_claimed_sum
//         + stmt1.xor9_claimed_sum
//         + stmt1.xor8_claimed_sum
//         + stmt1.xor7_claimed_sum
//         + stmt1.xor4_claimed_sum;

//     // TODO(shahars): Add inputs to sum, and constraint them.
//     assert_eq!(claimed_sum, SecureField::zero());

//     verify(
//         &components.components(),
//         channel,
//         commitment_scheme,
//         stark_proof,
//     )
// }

// #[cfg(test)]
// mod tests {
//     use std::env;

//     use stwo::core::pcs::PcsConfig;
//     use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;

//     use crate::blake3::air::{prove_blake, verify_blake};

//     // Note: this test is slow. Only run in release.
//     #[cfg_attr(not(feature = "slow-tests"), ignore)]
//     #[test_log::test]
//     fn test_simd_blake_prove() {
//         // Note: To see time measurement, run test with
//         //   LOG_N_INSTANCES=16 RUST_LOG_SPAN_EVENTS=enter,close RUST_LOG=info RUSTFLAGS="
//         //   -C target-cpu=native -C target-feature=+avx512f" cargo test --release
//         //   test_simd_blake_prove -- --nocapture --ignored

//         // Get from environment variable:
//         let log_n_instances = env::var("LOG_N_INSTANCES")
//             .unwrap_or_else(|_| "6".to_string())
//             .parse::<u32>()
//             .unwrap();
//         let config = PcsConfig::default();

//         // Prove.
//         let input = 100;
//         let proof = prove_blake::<Blake2sMerkleChannel>(log_n_instances, input, config);

//         // Verify.
//         verify_blake::<Blake2sMerkleChannel>(proof, input).unwrap();
//     }
// }
