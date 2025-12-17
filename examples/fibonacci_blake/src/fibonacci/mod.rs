mod computing;
mod trace_gen;

pub use computing::{FibComponent, FibEval};
use itertools::{Itertools, chain};
use num_traits::One;
use stwo::core::channel::Channel;
use stwo::core::fields::qm31::SecureField;
pub use trace_gen::{gen_fib_interaction_trace, gen_fib_trace};

use stwo::core::fields::m31::BaseField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkEval, relation};

pub const LOG_CONSTRAINT_DEGREE: u32 = 1;
pub const VALUE_RELATION_SIZE: usize = 1;  // Connection between Fibonacci output and Blake input
relation!(ValueRelation, VALUE_RELATION_SIZE);

pub const PUBLIC_INPUT_RELATION_SIZE: usize = 2;  // For (a, b) pairs - initial values
relation!(FibPublicInputRelation, PUBLIC_INPUT_RELATION_SIZE);

pub const PUBLIC_OUTPUT_RELATION_SIZE: usize = 1;  // For target value output
relation!(FibPublicOutputRelation, PUBLIC_OUTPUT_RELATION_SIZE);

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct FibStatement0 {
    pub log_size: u32,
    pub fibonacci_index: usize,
    // Public inputs (initial values in first row):
    pub initial_a: u32,
    pub initial_b: u32,
    // Public output (value at fibonacci_index):
    pub expected_value: u32,
}

impl FibStatement0 {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.fibonacci_index as u64);
        // Mix public inputs and output
        channel.mix_u64(self.initial_a as u64);
        channel.mix_u64(self.initial_b as u64);
        channel.mix_u64(self.expected_value as u64);
    }

    pub fn log_sizes(&self) -> stwo::core::pcs::TreeVec<Vec<u32>> {
        use stwo::core::pcs::TreeVec;
        use stwo_constraint_framework::PREPROCESSED_TRACE_IDX;

        let info = fib_info();
        let sizes = vec![
            info.mask_offsets.as_cols_ref().map_cols(|_| self.log_size),
        ];

        let mut log_sizes = TreeVec::concat_cols(sizes.into_iter());

        log_sizes[PREPROCESSED_TRACE_IDX] = vec![self.log_size; 2];

        log_sizes
    }
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct FibStatement1 {
    pub fib_claimed_sum: SecureField
}

impl FibStatement1 {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(
            &chain![
                [
                    self.fib_claimed_sum
                ],
            ]
            .collect_vec(),
        );
    }
}


pub fn gen_is_first_column(
    log_size: u32,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_rows = 1 << log_size;
    let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);

    col.set(0, BaseField::from_u32_unchecked(1));

    bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());

    CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)
}

pub fn is_first_column_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_first_{}", log_size),
    }
}

pub fn gen_is_target_column(
    log_size: u32,
    index: usize,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_rows = 1 << log_size;

    assert!(
        index < n_rows,
        "fibonacci_index ({}) must be less than n_rows (2^{} = {})",
        index,
        log_size,
        n_rows
    );

    let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);
    col.set(index, BaseField::one());

    bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());

    CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)
}

pub fn is_target_column_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_target_{}", log_size),
    }
}

pub fn fib_info() -> stwo_constraint_framework::InfoEvaluator {
    use stwo_constraint_framework::InfoEvaluator;

    let component = FibEval {
        log_n_rows: 1,
        is_first_id: is_first_column_id(1),
        is_target_id: is_target_column_id(1),
        value_relation: ValueRelation::dummy(),
        public_input_relation: FibPublicInputRelation::dummy(),
        public_output_relation: FibPublicOutputRelation::dummy(),
    };
    component.evaluate(InfoEvaluator::empty())
}
