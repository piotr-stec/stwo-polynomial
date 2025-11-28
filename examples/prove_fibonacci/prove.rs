use std::fs;

use num_traits::Zero;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::CommitmentSchemeProver;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_polynomial::prove::prove;

#[derive(Clone)]
pub struct FibonacciEval {
    pub log_n_rows: u32, // 2^N -> N
}

impl FrameworkEval for FibonacciEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1 // constraints -> Polynomial N stopnia  N = 4 2^4 = 16, 2^5 = 32
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Read three consecutive values: a, b, c
        let a = eval.next_trace_mask(); // f(n-2)
        let b = eval.next_trace_mask(); // f(n-1)
        let c = eval.next_trace_mask(); // f(n)
 

        // Constraint: f(n) = f(n-1) + f(n-2)
        // This is an intra-row constraint (checks values in the same row)
        // Padding with zeros works: 0 = 0 + 0 ✓
        eval.add_constraint(c - (a + b));

        eval
    }
}

pub type FibonacciComponent = FrameworkComponent<FibonacciEval>;

/// Calculate the minimum log_size needed to compute f(target_n)
pub fn calculate_log_size(target_n: usize) -> u32 {
    // We need at least target_n - 1 rows to compute f(target_n)
    // (row 0 has f(2), row 1 has f(3), ..., row target_n-2 has f(target_n))
    let min_rows = target_n.saturating_sub(1).max(1);

    // Round up to next power of 2
    let log_size = (min_rows as f64).log2().ceil() as u32;

    // STARK/FRI requires minimum log_size = 2 (4 rows)
    log_size.max(2)
}

/// Generate trace for simple fibonacci sequence up to f(target_n)
/// Remaining rows are padded with zeros
///
/// Structure: 3 columns
/// - Column 0: f(n-2)
/// - Column 1: f(n-1)
/// - Column 2: f(n)
///
/// Returns: (trace, actual_value, log_size_used)
pub fn gen_fibonacci_trace(
    target_n: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    BaseField,
    u32,
) {
    let log_size = calculate_log_size(target_n);
    let n_rows = 1 << log_size;

    // Create 3 columns
    let mut col_a = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_b = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_c = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let initial_a = 0;
    let initial_b = 1;
    let mut a = BaseField::from_u32_unchecked(initial_a);
    let mut b = BaseField::from_u32_unchecked(initial_b);

    // Track the target value
    let mut target_value = BaseField::from_u32_unchecked(0);

    // Compute Fibonacci up to target_n
    // Row i contains: [f(i), f(i+1), f(i+2)]
    let compute_rows = (target_n - 1).min(n_rows);

    for row in 0..compute_rows {
        let c = a + b;

        col_a.set(row, a);
        col_b.set(row, b);
        col_c.set(row, c);

        // Check if this row contains our target
        let current_index = row + 2;
        if current_index == target_n {
            target_value = c;
        }

        // Shift for next row
        a = b;
        b = c;
    }

    // Remaining rows are already zeros (padding)
    // Constraint 0 = 0 + 0 is satisfied ✓

    // Convert to CircleEvaluation
    let domain = CanonicCoset::new(log_size).circle_domain();

    let trace = vec![
        CircleEvaluation::new(domain, col_a),
        CircleEvaluation::new(domain, col_b),
        CircleEvaluation::new(domain, col_c),
    ];

    (trace, target_value, log_size)
}

fn main() {
    let target_n = 50;

    let (trace, _target_value, log_size) = gen_fibonacci_trace(target_n);

    let config = PcsConfig::default();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
    // Commit preprocessed (empty for this simple circuit)
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![]);
    tree_builder.commit(channel);

    // Commit trace
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);

    // Create component
    let component = FibonacciComponent::new(
        &mut TraceLocationAllocator::default(),
        FibonacciEval {
            log_n_rows: log_size,
        },
        SecureField::zero(),
    );

    let (proof, composition_polynomial) = prove(&[&component], channel, commitment_scheme).unwrap();

    // Serialize proof and composition polynomial to JSON files
    let proof_json = serde_json::to_string_pretty(&proof).unwrap();
    fs::write("proof.json", &proof_json).expect("Failed to write proof.json");

    let metadata = serde_json::json!({
        "target_n": target_n,
        "log_size": log_size,
    });
    
    fs::write(
        "proof_metadata.json",
        serde_json::to_string_pretty(&metadata).unwrap(),
    ).expect("Failed to write proof_metadata.json");

    let composition_polynomial_to_serialize: Vec<Vec<u32>> = composition_polynomial
        .into_coordinate_polys()
        .iter()
        .map(|poly| {
            let mut layer = Vec::new();
            for coeff in &poly.coeffs.data {
                let coeff_as_u32: Vec<u32> = coeff.to_array().iter().map(|m| m.0).collect();
                layer.extend_from_slice(&coeff_as_u32);
            }
            layer
        })
        .collect();

    let composition_polynomial_serializable =
        serde_json::to_value(&composition_polynomial_to_serialize).unwrap();
    fs::write(
        "composition_polynomial.json",
        serde_json::to_string_pretty(&composition_polynomial_serializable).unwrap(),
    )
    .expect("Failed to write compostion polynomial");
}
