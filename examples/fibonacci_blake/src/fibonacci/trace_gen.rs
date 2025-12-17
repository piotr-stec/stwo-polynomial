use num_traits::{One, Zero};
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use super::{ValueRelation, FibPublicInputRelation, FibPublicOutputRelation};

pub fn gen_fib_trace(
    log_size: u32,
    fibonacci_index: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    u32,
) {
    let n_rows = 1 << log_size;

    assert!(
        fibonacci_index < n_rows,
        "fibonacci_index ({}) must be less than n_rows ({})",
        fibonacci_index,
        n_rows
    );

    let mut col_a = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_b = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_c = Col::<SimdBackend, BaseField>::zeros(n_rows);

    let mut a = BaseField::zero();
    let mut b = BaseField::one();
    let mut target_value = 0u32;

    for row in 0..n_rows {
        let c = a + b;

        col_a.set(row, a);
        col_b.set(row, b);
        col_c.set(row, c);

        if row == fibonacci_index {
            target_value = a.0;
        }

        a = b;
        b = c;
    }

    bit_reverse_coset_to_circle_domain_order(col_a.as_mut_slice());
    bit_reverse_coset_to_circle_domain_order(col_b.as_mut_slice());
    bit_reverse_coset_to_circle_domain_order(col_c.as_mut_slice());

    let domain = CanonicCoset::new(log_size).circle_domain();

    (
        vec![
            CircleEvaluation::new(domain.clone(), col_a),
            CircleEvaluation::new(domain.clone(), col_b),
            CircleEvaluation::new(domain.clone(), col_c),
        ],
        target_value,
    )
}

pub fn gen_fib_interaction_trace(
    main_trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    preprocessed: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    value_relation: &ValueRelation,
    public_input_relation: &FibPublicInputRelation,
    public_output_relation: &FibPublicOutputRelation,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = main_trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let a_col = &main_trace[0];
    let b_col = &main_trace[1];
    let is_first_col = &preprocessed[0];
    let is_target_col = &preprocessed[1];

    {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let a_packed = a_col.values.data[vec_row];
            let b_packed = b_col.values.data[vec_row];
            let is_first_packed = is_first_col.values.data[vec_row];

            let denom = public_input_relation.combine(&[
                PackedSecureField::from(a_packed),
                PackedSecureField::from(b_packed),
            ]);
            let numerator = -PackedSecureField::from(is_first_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
    }

    {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let a_packed = a_col.values.data[vec_row];
            let is_target_packed = is_target_col.values.data[vec_row];

            let denom = public_output_relation.combine(&[PackedSecureField::from(a_packed)]);
            let numerator = -PackedSecureField::from(is_target_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
    }

    {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let a_packed = a_col.values.data[vec_row];
            let is_target_packed = is_target_col.values.data[vec_row];

            let denom = value_relation.combine(&[PackedSecureField::from(a_packed)]);
            let numerator = -PackedSecureField::from(is_target_packed);

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}
