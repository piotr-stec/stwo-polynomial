use std::fs;

use num_traits::Zero;
use serde_json::Value;
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::CommitmentSchemeVerifier;
use stwo::core::proof::StarkProof;
use stwo::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CirclePoly;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_polynomial::verify::verify;
use stwo::prover::poly::circle::SecureCirclePoly;


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

fn main() {
    // DESERIALIZATOION FROM JSON FILES
    let metadata_str = fs::read_to_string("proof_metadata.json")
        .expect("Failed to read proof_metadata.json. Make sure to run the prover first!");

    let metadata: Value =
        serde_json::from_str(&metadata_str).expect("Failed to parse proof metadata");
    let _target_n = metadata["target_n"].as_u64().unwrap() as usize;
    let log_size = metadata["log_size"].as_u64().unwrap() as u32;

    let proof_json = fs::read_to_string("proof.json")
        .expect("Failed to read proof.json. Make sure to run the prover first!");

    let proof: StarkProof<Blake2sMerkleHasher> =
        serde_json::from_str(&proof_json).expect("Failed to deserialize proof");

    let composition_polynomial_json = fs::read_to_string("composition_polynomial.json")
        .expect("Failed to read composition_polynomial.json. Make sure to run the prover first!");
    let composition_polynomial_vec: Vec<Vec<u32>> =
        serde_json::from_str(&composition_polynomial_json)
            .expect("Failed to deserialize composition polynomial");
    let polys: [CirclePoly<SimdBackend>; 4] = composition_polynomial_vec
        .into_iter()
        .map(|layer| {
            CirclePoly::<SimdBackend>::new(layer.into_iter().map(BaseField::from_u32_unchecked).collect())
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    
    let composition_polynomial = SecureCirclePoly(polys);

    let component = FibonacciComponent::new(
        &mut TraceLocationAllocator::default(),
        FibonacciEval {
            log_n_rows: log_size,
        },
        SecureField::zero(),
    );
    
    let channel = &mut Blake2sChannel::default();
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(proof.config);
    // Commit preprocessed
    commitment_scheme.commit(
        proof.commitments[0],
        &component.trace_log_degree_bounds()[0],
        channel,
    );

    // Commit trace
    commitment_scheme.commit(
        proof.commitments[1],
        &component.trace_log_degree_bounds()[1],
        channel,
    );

    // Verify!
    verify(&[&component], channel, commitment_scheme, proof, composition_polynomial).unwrap();
    println!("Proof verified successfully!");
}
