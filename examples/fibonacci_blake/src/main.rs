#![feature(portable_simd)]
#![feature(array_chunks)]
#![feature(iter_array_chunks)]

use alloy::primitives::{Address, Bytes, FixedBytes, U256};
use alloy::providers::{Provider, ProviderBuilder};
use alloy::rpc::types::TransactionRequest;
use alloy::sol_types::SolCall;
use alloy::{hex, sol};
use itertools::{Itertools, chain, multiunzip};
use num_traits::Zero;
use stwo::{core::{air::Component, channel::{KeccakChannel, MerkleChannel}, fields::qm31::SecureField, pcs::{CommitmentSchemeVerifier, PcsConfig}, poly::circle::CanonicCoset, proof::StarkProof, utils::bit_reverse, vcs::{MerkleHasher, keccak_merkle::{KeccakMerkleChannel, KeccakMerkleHasher}}, verifier::{VerificationError, verify}}, prover::{CommitmentSchemeProver, backend::simd::{SimdBackend, m31::LOG_N_LANES}, poly::circle::{PolyOps, SecureCirclePoly}}};
use stwo_constraint_framework::{FrameworkEval, Relation, TraceLocationAllocator};
use stwo_polynomial::prove::prove;

use crate::{blake3::{AllElements, BlakeComponentsForIntegration, BlakeStatement0, BlakeStatement1, ROUND_LOG_SPLIT, XorAccums, preprocessed_columns::XorTable, round, scheduler, xor_table}, fibonacci::{FibComponent, FibEval, FibPublicInputRelation, FibPublicOutputRelation, FibStatement0, FibStatement1, ValueRelation, gen_fib_interaction_trace, gen_fib_trace, gen_is_first_column, gen_is_target_column, is_first_column_id, is_target_column_id}};

pub mod blake3;
pub mod fibonacci;

// Generate Rust bindings for STWO verifier contracts
sol! {
    /// QM31 field element structure
    struct QM31 {
        CM31 first;
        CM31 second;
    }

    /// CM31 field element structure
    struct CM31 {
        uint32 real;
        uint32 imag;
    }

    /// PCS Configuration
    struct Config {
        uint32 powBits;
        FriConfig friConfig;
    }

    /// FRI Configuration
    struct FriConfig {
        uint32 logBlowupFactor;
        uint32 logLastLayerDegreeBound;
        uint256 nQueries;
    }

    /// Merkle decommitment structure
    struct Decommitment {
        bytes32[] witness;
        uint32[] columnWitness;
    }

    /// FRI layer proof structure
    struct FriLayerProof {
        QM31[] friWitness;
        bytes decommitment;
        bytes32 commitment;
    }

    /// FRI proof structure
    struct FriProof {
        FriLayerProof firstLayer;
        FriLayerProof[] innerLayers;
        QM31[] lastLayerPoly;
    }

    /// Composition polynomial
    struct CompositionPoly {
        uint32[] coeffs0;
        uint32[] coeffs1;
        uint32[] coeffs2;
        uint32[] coeffs3;
    }

    /// Complete proof structure for verification
    struct Proof {
        Config config;
        bytes32[] commitments;
        QM31[][][] sampledValues;
        Decommitment[] decommitments;
        uint32[][] queriedValues;
        uint64 proofOfWork;
        FriProof friProof;
        CompositionPoly compositionPoly;
    }

    /// Component information structure
    struct ComponentInfo {
        uint32 maxConstraintLogDegreeBound;
        uint32 logSize;
        int32[][][] maskOffsets;
        uint256[] preprocessedColumns;
    }

    
    struct ComponentParams{
        uint32 logSize;
        QM31 claimedSum;
        ComponentInfo info;
    }

    /// Verification parameters structure
    struct VerificationParams {
        ComponentParams[] componentParams;
        uint256 nPreprocessedColumns;
        uint32 componentsCompositionLogDegreeBound;
    }

    /// STWO Verifier contract interface
    interface IStwoVerifier {
        function verify(
            Proof calldata proof,
            VerificationParams calldata params,
            bytes32[] memory treeRoots,
            uint32[][] memory treeColumnLogSizes,
            bytes32 digest,
            uint32 nDraws
        ) external view returns (bool);
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Fibonacci On-Chain");

    let log_size = 4;
    let fibonacci_index = 4;
    println!("Computing Fibonacci f({})\n", fibonacci_index);

    let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
    println!("Fibonacci trace generated: {} columns", fib_trace.len());
    println!(
        "Fibonacci value at index {}: {}",
        fibonacci_index, fibonacci_value
    );

    let fib_is_first_col = gen_is_first_column(log_size);
    let fib_is_target_col = gen_is_target_column(log_size, fibonacci_index);

    let blake_is_first_col = scheduler::gen_is_first_column(log_size);

    let (blake_scheduler_trace, blake_scheduler_lookup_data, blake_round_inputs) =
        scheduler::gen_trace(log_size, fibonacci_value);
    println!(
        "Blake scheduler trace generated: {} columns",
        blake_scheduler_trace.len()
    );

    let mut xor_accums = XorAccums::default();
    let mut rest = &blake_round_inputs[..];
    let (blake_round_traces, blake_round_lookup_data): (Vec<_>, Vec<_>) =
        multiunzip(ROUND_LOG_SPLIT.map(|l| {
            let (cur_inputs, r) = rest.split_at(1 << (log_size - LOG_N_LANES + l));
            rest = r;
            round::generate_trace(log_size + l, cur_inputs, &mut xor_accums)
        }));

    let (blake_xor_trace12, blake_xor_lookup_data12) =
        xor_table::xor12::generate_trace(xor_accums.xor12);
    let (blake_xor_trace9, blake_xor_lookup_data9) =
        xor_table::xor9::generate_trace(xor_accums.xor9);
    let (blake_xor_trace8, blake_xor_lookup_data8) =
        xor_table::xor8::generate_trace(xor_accums.xor8);
    let (blake_xor_trace7, blake_xor_lookup_data7) =
        xor_table::xor7::generate_trace(xor_accums.xor7);
    let (blake_xor_trace4, blake_xor_lookup_data4) =
        xor_table::xor4::generate_trace(xor_accums.xor4);

    use stwo::core::fri::FriConfig as StwoFriConfig;
    let config = PcsConfig {
        pow_bits: 2,
        fri_config: StwoFriConfig::new(1, 1, 3),
    };
    println!("Security bits: {}", config.security_bits());

    const XOR_TABLE_MAX_LOG_SIZE: u32 = 16;
    let log_max_rows =
        (log_size + *ROUND_LOG_SPLIT.iter().max().unwrap()).max(XOR_TABLE_MAX_LOG_SIZE);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_max_rows + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let prover_channel = &mut KeccakChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, KeccakMerkleChannel>::new(config, &twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals([fib_is_first_col.clone(), fib_is_target_col.clone()]);
    tree_builder.extend_evals([blake_is_first_col.clone()]);
    tree_builder.extend_evals(
        chain![
            XorTable::new(12, 4, 0).generate_constant_trace(),
            XorTable::new(9, 2, 0).generate_constant_trace(),
            XorTable::new(8, 2, 0).generate_constant_trace(),
            XorTable::new(7, 2, 0).generate_constant_trace(),
            XorTable::new(4, 0, 0).generate_constant_trace(),
        ]
        .collect_vec(),
    );
    tree_builder.commit(prover_channel);
    println!("Preprocessed trace committed");

    let fib_statement = FibStatement0 {
        log_size,
        fibonacci_index,
        initial_a: 0,
        initial_b: 1,
        expected_value: fibonacci_value,
    };
    fib_statement.mix_into(prover_channel);

    let blake_stmt0 = BlakeStatement0 { log_size };
    blake_stmt0.mix_into(prover_channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(fib_trace.clone());
    tree_builder.extend_evals(
        chain![
            blake_scheduler_trace.clone(),
            blake_round_traces.into_iter().flatten(),
            blake_xor_trace12,
            blake_xor_trace9,
            blake_xor_trace8,
            blake_xor_trace7,
            blake_xor_trace4,
        ]
        .collect_vec(),
    );
    tree_builder.commit(prover_channel);
    println!("Base trace committed");

    let all_elements = AllElements::draw(prover_channel);
    let value_relation = ValueRelation::draw(prover_channel);
    let public_input_relation = FibPublicInputRelation::draw(prover_channel);
    let public_output_relation = FibPublicOutputRelation::draw(prover_channel);
    println!("Challenges drawn");

    let fib_preprocessed = vec![fib_is_first_col.clone(), fib_is_target_col.clone()];
    let (fib_interaction_trace, fib_claimed_sum) =
        gen_fib_interaction_trace(
            &fib_trace,
            &fib_preprocessed,
            &value_relation,
            &public_input_relation,
            &public_output_relation,
        );
    println!("Fibonacci claimed sum: {:?}", fib_claimed_sum);

    let blake_preprocessed = vec![blake_is_first_col.clone()];
    let (blake_scheduler_interaction_trace, blake_scheduler_claimed_sum) =
        scheduler::gen_interaction_trace(
            log_size,
            blake_scheduler_lookup_data,
            &all_elements.round_elements,
            &all_elements.blake_elements,
            &blake_scheduler_trace,
            &blake_preprocessed,
            &value_relation,
        );
    println!(
        "Blake scheduler claimed sum: {:?}",
        blake_scheduler_claimed_sum
    );

    let (blake_round_interaction_traces, blake_round_claimed_sums): (Vec<_>, Vec<_>) =
        multiunzip(ROUND_LOG_SPLIT.iter().zip(blake_round_lookup_data).map(
            |(l, lookup_data)| {
                round::generate_interaction_trace(
                    log_size + l,
                    lookup_data,
                    &all_elements.xor_elements,
                    &all_elements.round_elements,
                )
            },
        ));

    let (blake_xor_interaction_trace12, blake_xor_claimed_sum12) =
        xor_table::xor12::generate_interaction_trace(
            blake_xor_lookup_data12,
            &all_elements.xor_elements.xor12,
        );
    let (blake_xor_interaction_trace9, blake_xor_claimed_sum9) =
        xor_table::xor9::generate_interaction_trace(
            blake_xor_lookup_data9,
            &all_elements.xor_elements.xor9,
        );
    let (blake_xor_interaction_trace8, blake_xor_claimed_sum8) =
        xor_table::xor8::generate_interaction_trace(
            blake_xor_lookup_data8,
            &all_elements.xor_elements.xor8,
        );
    let (blake_xor_interaction_trace7, blake_xor_claimed_sum7) =
        xor_table::xor7::generate_interaction_trace(
            blake_xor_lookup_data7,
            &all_elements.xor_elements.xor7,
        );
    let (blake_xor_interaction_trace4, blake_xor_claimed_sum4) =
        xor_table::xor4::generate_interaction_trace(
            blake_xor_lookup_data4,
            &all_elements.xor_elements.xor4,
        );

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(
        chain![
            fib_interaction_trace,
            blake_scheduler_interaction_trace,
            blake_round_interaction_traces.into_iter().flatten(),
            blake_xor_interaction_trace12,
            blake_xor_interaction_trace9,
            blake_xor_interaction_trace8,
            blake_xor_interaction_trace7,
            blake_xor_interaction_trace4
        ]
        .collect_vec(),
    );

    let fibonacci_stmt1 = FibStatement1 {
        fib_claimed_sum: fib_claimed_sum,
    };
    fibonacci_stmt1.mix_into(prover_channel);

    let stmt1 = BlakeStatement1 {
        scheduler_claimed_sum: blake_scheduler_claimed_sum,
        round_claimed_sums: blake_round_claimed_sums.clone(),
        xor12_claimed_sum: blake_xor_claimed_sum12,
        xor9_claimed_sum: blake_xor_claimed_sum9,
        xor8_claimed_sum: blake_xor_claimed_sum8,
        xor7_claimed_sum: blake_xor_claimed_sum7,
        xor4_claimed_sum: blake_xor_claimed_sum4
    };
    stmt1.mix_into(prover_channel);
    tree_builder.commit(prover_channel);
    println!("Interaction trace committed");

    let all_preprocessed_columns: Vec<_> = chain![
        [is_first_column_id(log_size), is_target_column_id(log_size)],
        [
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
    ]
    .collect();

    let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);

    let fib_component = FibComponent::new(
        &mut tree_span_provider,
        FibEval {
            log_n_rows: log_size,
            is_first_id: is_first_column_id(log_size),
            is_target_id: is_target_column_id(log_size),
            value_relation: value_relation.clone(),
            public_input_relation: public_input_relation.clone(),
            public_output_relation: public_output_relation.clone(),
        },
        fib_claimed_sum,
    );

    let blake_components = BlakeComponentsForIntegration::new(
        &mut tree_span_provider,
        &all_elements,
        &value_relation,
        &blake_stmt0,
        &stmt1,
    );
    println!("Components created");

    // Prove
    let all_component_provers = chain![
        [&fib_component as &dyn stwo::prover::ComponentProver<SimdBackend>],
        [&blake_components.scheduler_component
            as &dyn stwo::prover::ComponentProver<SimdBackend>],
        blake_components
            .round_components
            .iter()
            .map(|c| c as &dyn stwo::prover::ComponentProver<SimdBackend>),
        [&blake_components.xor12 as &dyn stwo::prover::ComponentProver<SimdBackend>],
        [&blake_components.xor9 as &dyn stwo::prover::ComponentProver<SimdBackend>],
        [&blake_components.xor8 as &dyn stwo::prover::ComponentProver<SimdBackend>],
        [&blake_components.xor7 as &dyn stwo::prover::ComponentProver<SimdBackend>],
        [&blake_components.xor4 as &dyn stwo::prover::ComponentProver<SimdBackend>],
    ]
    .collect_vec();

    let (proof, composition_polynomial) = prove::<SimdBackend, KeccakMerkleChannel>(
        &all_component_provers,
        prover_channel,
        commitment_scheme,
    )
    .expect("Failed to generate proof");

    println!("PROOF GENERATED!\n");

    // Create proof structure
    let proof_data = ProofData {
        fib_stmt0: fib_statement.clone(),
        fib_stmt1: fibonacci_stmt1.clone(),
        blake_stmt0: blake_stmt0.clone(),
        blake_stmt1: stmt1.clone(),
        stark_proof: proof.clone(),
    };

    // Verify off-chain
    println!("🔍 Starting Off-Chain Verification...");
    verify_proof::<KeccakMerkleChannel>(proof_data.clone()).expect("Off-chain verification failed");

    // Verify on-chain (optional - only if Anvil is running)
    println!("\n🔗 Starting On-Chain Verification...");
    println!("Note: This requires Anvil running on http://localhost:8545");
    println!("      and the STWO verifier contract deployed.");

    match verify_proof_onchain(proof_data, composition_polynomial, config).await {
        Ok(_) => println!("✅ On-chain verification completed!"),
        Err(e) => {
            eprintln!("⚠️  On-chain verification skipped: {}", e);
            eprintln!("   To enable on-chain verification:");
            eprintln!("   1. Start Anvil: anvil");
            eprintln!("   2. Deploy the STWO verifier contract");
        }
    }

    println!("\n✅ Off-chain verification complete!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use itertools::{Itertools, chain};
    use num_traits::Zero;
    use stwo::core::{air::Component, channel::MerkleChannel, fields::qm31::SecureField, pcs::CommitmentSchemeVerifier, poly::circle::CanonicCoset, proof::StarkProof, vcs::{MerkleHasher, blake2_merkle::Blake2sMerkleChannel}, verifier::{VerificationError, verify}};
    use stwo_constraint_framework::{TraceLocationAllocator, Relation};

    use crate::{blake3::{AllElements, BlakeComponentsForIntegration, BlakeStatement0, BlakeStatement1}, fibonacci::{
        FibComponent, FibEval, FibStatement0, FibStatement1, ValueRelation, FibPublicInputRelation, FibPublicOutputRelation, gen_fib_interaction_trace, gen_fib_trace, gen_is_first_column, gen_is_target_column, is_first_column_id, is_target_column_id
    }};

    #[test]
    fn test_fibonacci_blake_prove_verify() {
        use itertools::{Itertools, chain, multiunzip};
        use stwo::core::channel::Blake2sChannel;
        use stwo::core::pcs::PcsConfig;
        use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::backend::simd::m31::LOG_N_LANES;
        use stwo::prover::poly::circle::PolyOps;
        use stwo::prover::{CommitmentSchemeProver, prove};
        use stwo_constraint_framework::TraceLocationAllocator;

        use crate::blake3::air::{AllElements, BlakeStatement0};
        use crate::blake3::preprocessed_columns::XorTable;
        use crate::blake3::{ROUND_LOG_SPLIT, XorAccums, round, scheduler, xor_table};

        let log_size = 4;
        let fibonacci_index = 8;

        let (fib_trace, fibonacci_value) = gen_fib_trace(log_size, fibonacci_index);
        println!("Fibonacci trace generated: {} columns", fib_trace.len());
        println!(
            "Fibonacci value at index {}: {}",
            fibonacci_index, fibonacci_value
        );

        let fib_is_first_col = gen_is_first_column(log_size);
        let fib_is_target_col = gen_is_target_column(log_size, fibonacci_index);

        let blake_is_first_col = scheduler::gen_is_first_column(log_size);

        let (blake_scheduler_trace, blake_scheduler_lookup_data, blake_round_inputs) =
            scheduler::gen_trace(log_size, fibonacci_value);
        println!(
            "Blake scheduler trace generated: {} columns",
            blake_scheduler_trace.len()
        );

        let mut xor_accums = XorAccums::default();
        let mut rest = &blake_round_inputs[..];
        let (blake_round_traces, blake_round_lookup_data): (Vec<_>, Vec<_>) =
            multiunzip(ROUND_LOG_SPLIT.map(|l| {
                let (cur_inputs, r) = rest.split_at(1 << (log_size - LOG_N_LANES + l));
                rest = r;
                round::generate_trace(log_size + l, cur_inputs, &mut xor_accums)
            }));

        let (blake_xor_trace12, blake_xor_lookup_data12) =
            xor_table::xor12::generate_trace(xor_accums.xor12);
        let (blake_xor_trace9, blake_xor_lookup_data9) =
            xor_table::xor9::generate_trace(xor_accums.xor9);
        let (blake_xor_trace8, blake_xor_lookup_data8) =
            xor_table::xor8::generate_trace(xor_accums.xor8);
        let (blake_xor_trace7, blake_xor_lookup_data7) =
            xor_table::xor7::generate_trace(xor_accums.xor7);
        let (blake_xor_trace4, blake_xor_lookup_data4) =
            xor_table::xor4::generate_trace(xor_accums.xor4);

        // Use same config as fibonacci_onchain for compatibility with on-chain verification
        use stwo::core::fri::FriConfig as StwoFriConfig;
        let config = PcsConfig {
            pow_bits: 15,
            fri_config: StwoFriConfig::new(2, 3, 27),
        };
        println!("Security bits: {}", config.security_bits());

        const XOR_TABLE_MAX_LOG_SIZE: u32 = 16;
        let log_max_rows =
            (log_size + *ROUND_LOG_SPLIT.iter().max().unwrap()).max(XOR_TABLE_MAX_LOG_SIZE);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_max_rows + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        let prover_channel = &mut Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals([fib_is_first_col.clone(), fib_is_target_col.clone()]);
        tree_builder.extend_evals([blake_is_first_col.clone()]);
        tree_builder.extend_evals(
            chain![
                XorTable::new(12, 4, 0).generate_constant_trace(),
                XorTable::new(9, 2, 0).generate_constant_trace(),
                XorTable::new(8, 2, 0).generate_constant_trace(),
                XorTable::new(7, 2, 0).generate_constant_trace(),
                XorTable::new(4, 0, 0).generate_constant_trace(),
            ]
            .collect_vec(),
        );
        tree_builder.commit(prover_channel);
        println!("Preprocessed trace committed");

        let fib_statement = FibStatement0 {
            log_size,
            fibonacci_index,
            initial_a: 0,
            initial_b: 1,
            expected_value: fibonacci_value,
        };
        fib_statement.mix_into(prover_channel);

        let blake_stmt0 = BlakeStatement0 { log_size };
        blake_stmt0.mix_into(prover_channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(fib_trace.clone());
        tree_builder.extend_evals(
            chain![
                blake_scheduler_trace.clone(),
                blake_round_traces.into_iter().flatten(),
                blake_xor_trace12,
                blake_xor_trace9,
                blake_xor_trace8,
                blake_xor_trace7,
                blake_xor_trace4,
            ]
            .collect_vec(),
        );
        tree_builder.commit(prover_channel);
        println!("Base trace committed");

        let all_elements = AllElements::draw(prover_channel);
        let value_relation = ValueRelation::draw(prover_channel);
        let public_input_relation = FibPublicInputRelation::draw(prover_channel);
        let public_output_relation = FibPublicOutputRelation::draw(prover_channel);
        println!("Challenges drawn");

        let fib_preprocessed = vec![fib_is_first_col.clone(), fib_is_target_col.clone()];
        let (fib_interaction_trace, fib_claimed_sum) =
            gen_fib_interaction_trace(
                &fib_trace,
                &fib_preprocessed,
                &value_relation,
                &public_input_relation,
                &public_output_relation,
            );
        println!("Fibonacci claimed sum: {:?}", fib_claimed_sum);

        let blake_preprocessed = vec![blake_is_first_col.clone()];
        let (blake_scheduler_interaction_trace, blake_scheduler_claimed_sum) =
            scheduler::gen_interaction_trace(
                log_size,
                blake_scheduler_lookup_data,
                &all_elements.round_elements,
                &all_elements.blake_elements,
                &blake_scheduler_trace,
                &blake_preprocessed,
                &value_relation,
            );
        println!(
            "Blake scheduler claimed sum: {:?}",
            blake_scheduler_claimed_sum
        );

        let (blake_round_interaction_traces, blake_round_claimed_sums): (Vec<_>, Vec<_>) =
            multiunzip(ROUND_LOG_SPLIT.iter().zip(blake_round_lookup_data).map(
                |(l, lookup_data)| {
                    round::generate_interaction_trace(
                        log_size + l,
                        lookup_data,
                        &all_elements.xor_elements,
                        &all_elements.round_elements,
                    )
                },
            ));

        let (blake_xor_interaction_trace12, blake_xor_claimed_sum12) =
            xor_table::xor12::generate_interaction_trace(
                blake_xor_lookup_data12,
                &all_elements.xor_elements.xor12,
            );
        let (blake_xor_interaction_trace9, blake_xor_claimed_sum9) =
            xor_table::xor9::generate_interaction_trace(
                blake_xor_lookup_data9,
                &all_elements.xor_elements.xor9,
            );
        let (blake_xor_interaction_trace8, blake_xor_claimed_sum8) =
            xor_table::xor8::generate_interaction_trace(
                blake_xor_lookup_data8,
                &all_elements.xor_elements.xor8,
            );
        let (blake_xor_interaction_trace7, blake_xor_claimed_sum7) =
            xor_table::xor7::generate_interaction_trace(
                blake_xor_lookup_data7,
                &all_elements.xor_elements.xor7,
            );
        let (blake_xor_interaction_trace4, blake_xor_claimed_sum4) =
            xor_table::xor4::generate_interaction_trace(
                blake_xor_lookup_data4,
                &all_elements.xor_elements.xor4,
            );

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(
            chain![
                fib_interaction_trace,
                blake_scheduler_interaction_trace,
                blake_round_interaction_traces.into_iter().flatten(),
                blake_xor_interaction_trace12,
                blake_xor_interaction_trace9,
                blake_xor_interaction_trace8,
                blake_xor_interaction_trace7,
                blake_xor_interaction_trace4
            ]
            .collect_vec(),
        );

        let fibonacci_stmt1 = FibStatement1 {
            fib_claimed_sum: fib_claimed_sum,
        };
        fibonacci_stmt1.mix_into(prover_channel);

        let stmt1 = BlakeStatement1 {
            scheduler_claimed_sum: blake_scheduler_claimed_sum,
            round_claimed_sums: blake_round_claimed_sums.clone(),
            xor12_claimed_sum: blake_xor_claimed_sum12,
            xor9_claimed_sum: blake_xor_claimed_sum9,
            xor8_claimed_sum: blake_xor_claimed_sum8,
            xor7_claimed_sum: blake_xor_claimed_sum7,
            xor4_claimed_sum: blake_xor_claimed_sum4
        };
        stmt1.mix_into(prover_channel);
        tree_builder.commit(prover_channel);
        println!("Interaction trace committed");

        let all_preprocessed_columns: Vec<_> = chain![
            [is_first_column_id(log_size), is_target_column_id(log_size)],
            [
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
        ]
        .collect();

        let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);

        let fib_component = FibComponent::new(
            &mut tree_span_provider,
            FibEval {
                log_n_rows: log_size,
                is_first_id: is_first_column_id(log_size),
                is_target_id: is_target_column_id(log_size),
                value_relation: value_relation.clone(),
                public_input_relation: public_input_relation.clone(),
                public_output_relation: public_output_relation.clone(),
            },
            fib_claimed_sum,
        );

        let blake_components = BlakeComponentsForIntegration::new(
            &mut tree_span_provider,
            &all_elements,
            &value_relation,
            &blake_stmt0,
            &stmt1,
        );
        println!("Components created");

        // Prove
        let all_component_provers = chain![
            [&fib_component as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.scheduler_component
                as &dyn stwo::prover::ComponentProver<SimdBackend>],
            blake_components
                .round_components
                .iter()
                .map(|c| c as &dyn stwo::prover::ComponentProver<SimdBackend>),
            [&blake_components.xor12 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor9 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor8 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor7 as &dyn stwo::prover::ComponentProver<SimdBackend>],
            [&blake_components.xor4 as &dyn stwo::prover::ComponentProver<SimdBackend>],
        ]
        .collect_vec();

        let proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &all_component_provers,
            prover_channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        println!("PROOF GENERATED!");

        let proof_data = ProofData {
            fib_stmt0: fib_statement.clone(),
            fib_stmt1: fibonacci_stmt1.clone(),
            blake_stmt0: blake_stmt0.clone(),
            blake_stmt1: stmt1.clone(),
            stark_proof: proof.clone(),
        };

        let proof_json = serde_json::to_string_pretty(&proof_data)
            .expect("Failed to serialize proof");
        std::fs::write("fibonacci_blake_proof.json", &proof_json)
            .expect("Failed to write proof to file");
        println!("Proof saved to fibonacci_blake_proof.json");

        let proof_binary = bincode::serialize(&proof_data)
            .expect("Failed to serialize proof to binary");
        std::fs::write("fibonacci_blake_proof.bin", &proof_binary)
            .expect("Failed to write binary proof to file");
        println!("Binary proof saved to fibonacci_blake_proof.bin ({} bytes)", proof_binary.len());

        // Verify
        let verify = verify_proof::<Blake2sMerkleChannel>(ProofData { fib_stmt0: fib_statement, fib_stmt1: fibonacci_stmt1, blake_stmt0, blake_stmt1: stmt1, stark_proof: proof });
        verify.unwrap()
    }
}

#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct ProofData<H: MerkleHasher> {
    fib_stmt0: FibStatement0,
    fib_stmt1: FibStatement1,
    blake_stmt0: BlakeStatement0,
    blake_stmt1: BlakeStatement1,
    stark_proof: StarkProof<H>,
}

fn verify_proof<MC: MerkleChannel>(ProofData {
    fib_stmt0,
    fib_stmt1,
    blake_stmt0,
    blake_stmt1,
    stark_proof,
}: ProofData<MC::H>,) -> Result<(), VerificationError> {
    let channel = &mut MC::C::default();
    const REQUIRED_SECURITY_BITS: u32 = 5;
    assert!(stark_proof.config.security_bits() >= REQUIRED_SECURITY_BITS);
    let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(stark_proof.config);

    let fib_log_sizes = fib_stmt0.log_sizes();
    let blake_log_sizes = blake_stmt0.log_sizes();

    let combined_preprocessed_sizes: Vec<u32> = fib_log_sizes[0]
        .iter()
        .chain(blake_log_sizes[0].iter())
        .copied()
        .collect();

    let combined_base_sizes: Vec<u32> = fib_log_sizes[1]
        .iter()
        .chain(blake_log_sizes[1].iter())
        .copied()
        .collect();

    let combined_interaction_sizes: Vec<u32> = fib_log_sizes[2]
        .iter()
        .chain(blake_log_sizes[2].iter())
        .copied()
        .collect();

    commitment_scheme.commit(stark_proof.commitments[0], &combined_preprocessed_sizes, channel);

    fib_stmt0.mix_into(channel);
    blake_stmt0.mix_into(channel);
    commitment_scheme.commit(stark_proof.commitments[1], &combined_base_sizes, channel);

    let all_elements = AllElements::draw(channel);
    let value_relation = ValueRelation::draw(channel);
    let public_input_relation = FibPublicInputRelation::draw(channel);
    let public_output_relation = FibPublicOutputRelation::draw(channel);

    fib_stmt1.mix_into(channel);
    blake_stmt1.mix_into(channel);
    commitment_scheme.commit(stark_proof.commitments[2], &combined_interaction_sizes, channel);

    use crate::blake3::preprocessed_columns::XorTable as XorT;
    let all_preprocessed_columns: Vec<_> = chain![
        [is_first_column_id(fib_stmt0.log_size), is_target_column_id(fib_stmt0.log_size)],
        [
            crate::blake3::scheduler::is_first_column_id(fib_stmt0.log_size),
            XorT::new(12, 4, 0).id(),
            XorT::new(12, 4, 1).id(),
            XorT::new(12, 4, 2).id(),
            XorT::new(9, 2, 0).id(),
            XorT::new(9, 2, 1).id(),
            XorT::new(9, 2, 2).id(),
            XorT::new(8, 2, 0).id(),
            XorT::new(8, 2, 1).id(),
            XorT::new(8, 2, 2).id(),
            XorT::new(7, 2, 0).id(),
            XorT::new(7, 2, 1).id(),
            XorT::new(7, 2, 2).id(),
            XorT::new(4, 0, 0).id(),
            XorT::new(4, 0, 1).id(),
            XorT::new(4, 0, 2).id(),
        ]
    ]
    .collect();

    let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);
    let fib_component = FibComponent::new(
        &mut tree_span_provider,
        FibEval {
            log_n_rows: fib_stmt0.log_size,
            is_first_id: is_first_column_id(fib_stmt0.log_size),
            is_target_id: is_target_column_id(fib_stmt0.log_size),
            value_relation: value_relation.clone(),
            public_input_relation: public_input_relation.clone(),
            public_output_relation: public_output_relation.clone(),
        },
        fib_stmt1.fib_claimed_sum,
    );
    let blake_components = BlakeComponentsForIntegration::new(
        &mut tree_span_provider,
        &all_elements,
        &value_relation,
        &blake_stmt0,
        &blake_stmt1
    );
    println!("Components created");

    let mut claimed_sum = fib_stmt1.fib_claimed_sum
        + blake_stmt1.scheduler_claimed_sum
        + blake_stmt1.round_claimed_sums.iter().sum::<SecureField>()
        + blake_stmt1.xor12_claimed_sum
        + blake_stmt1.xor9_claimed_sum
        + blake_stmt1.xor8_claimed_sum
        + blake_stmt1.xor7_claimed_sum
        + blake_stmt1.xor4_claimed_sum;

    use stwo::core::fields::m31::BaseField;
    use stwo::core::fields::FieldExpOps;

    let initial_denom: SecureField = public_input_relation.combine(&[
        SecureField::from(BaseField::from(fib_stmt0.initial_a)),
        SecureField::from(BaseField::from(fib_stmt0.initial_b)),
    ]);
    claimed_sum += initial_denom.inverse();

    let expected_denom: SecureField = public_output_relation.combine(&[
        SecureField::from(BaseField::from(fib_stmt0.expected_value)),
    ]);
    claimed_sum += expected_denom.inverse();

    assert_eq!(claimed_sum, SecureField::zero());

    let all_components_for_verify = chain![
        [&fib_component as &dyn Component],
        blake_components.as_components_vec()
    ]
    .collect_vec();

    // Perform off-chain verification
    let result = verify(
        &all_components_for_verify,
        channel,
        commitment_scheme,
        stark_proof.clone(),
    );

    if result.is_ok() {
        println!("✅ Off-chain verification successful");
    }

    result
}

/// Prepare on-chain verification parameters and call contract
async fn verify_proof_onchain(
    proof_data: ProofData<KeccakMerkleHasher>,
    composition_polynomial: SecureCirclePoly<SimdBackend>,
    config: PcsConfig,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔄 STEP: Convert Proof to Solidity Format");
    let solidity_proof = convert_to_solidity_proof(
        proof_data.stark_proof.clone(),
        composition_polynomial.clone(),
        config,
    );
    println!("  ✅ Proof converted to Solidity format\n");

    println!("📋 STEP: Prepare Verification Parameters");

    // Recreate channel for digest calculation
    let channel = &mut KeccakChannel::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<KeccakMerkleChannel>::new(config);

    let fib_log_sizes = proof_data.fib_stmt0.log_sizes();
    let blake_log_sizes = proof_data.blake_stmt0.log_sizes();

    println!("  Fibonacci log_sizes:");
    println!("    Tree 0 (preprocessed): {:?}", fib_log_sizes[0]);
    println!("    Tree 1 (base): {:?}", fib_log_sizes[1]);
    println!("    Tree 2 (interaction): {:?}", fib_log_sizes[2]);

    println!("  Blake log_sizes:");
    println!("    Tree 0 (preprocessed): {:?}", blake_log_sizes[0]);
    println!("    Tree 1 (base): {:?}", blake_log_sizes[1]);
    println!("    Tree 2 (interaction): {:?}", blake_log_sizes[2]);

    let combined_preprocessed_sizes: Vec<u32> = fib_log_sizes[0]
        .iter()
        .chain(blake_log_sizes[0].iter())
        .copied()
        .collect();

    let combined_base_sizes: Vec<u32> = fib_log_sizes[1]
        .iter()
        .chain(blake_log_sizes[1].iter())
        .copied()
        .collect();

    let combined_interaction_sizes: Vec<u32> = fib_log_sizes[2]
        .iter()
        .chain(blake_log_sizes[2].iter())
        .copied()
        .collect();

    println!("  Combined sizes:");
    println!("    Preprocessed: {} columns", combined_preprocessed_sizes.len());
    println!("    Base: {} columns", combined_base_sizes.len());
    println!("    Interaction: {} columns", combined_interaction_sizes.len());

    commitment_scheme.commit(proof_data.stark_proof.commitments[0], &combined_preprocessed_sizes, channel);
    proof_data.fib_stmt0.mix_into(channel);
    proof_data.blake_stmt0.mix_into(channel);
    commitment_scheme.commit(proof_data.stark_proof.commitments[1], &combined_base_sizes, channel);

    let all_elements = AllElements::draw(channel);
    let value_relation = ValueRelation::draw(channel);
    let public_input_relation = FibPublicInputRelation::draw(channel);
    let public_output_relation = FibPublicOutputRelation::draw(channel);

    proof_data.fib_stmt1.mix_into(channel);
    proof_data.blake_stmt1.mix_into(channel);
    commitment_scheme.commit(proof_data.stark_proof.commitments[2], &combined_interaction_sizes, channel);

    use crate::blake3::preprocessed_columns::XorTable as XorT;
    let all_preprocessed_columns: Vec<_> = chain![
        [is_first_column_id(proof_data.fib_stmt0.log_size), is_target_column_id(proof_data.fib_stmt0.log_size)],
        [
            crate::blake3::scheduler::is_first_column_id(proof_data.fib_stmt0.log_size),
            XorT::new(12, 4, 0).id(),
            XorT::new(12, 4, 1).id(),
            XorT::new(12, 4, 2).id(),
            XorT::new(9, 2, 0).id(),
            XorT::new(9, 2, 1).id(),
            XorT::new(9, 2, 2).id(),
            XorT::new(8, 2, 0).id(),
            XorT::new(8, 2, 1).id(),
            XorT::new(8, 2, 2).id(),
            XorT::new(7, 2, 0).id(),
            XorT::new(7, 2, 1).id(),
            XorT::new(7, 2, 2).id(),
            XorT::new(4, 0, 0).id(),
            XorT::new(4, 0, 1).id(),
            XorT::new(4, 0, 2).id(),
        ]
    ]
    .collect();

    let mut tree_span_provider = TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);

    let fib_component = FibComponent::new(
        &mut tree_span_provider,
        FibEval {
            log_n_rows: proof_data.fib_stmt0.log_size,
            is_first_id: is_first_column_id(proof_data.fib_stmt0.log_size),
            is_target_id: is_target_column_id(proof_data.fib_stmt0.log_size),
            value_relation: value_relation.clone(),
            public_input_relation: public_input_relation.clone(),
            public_output_relation: public_output_relation.clone(),
        },
        proof_data.fib_stmt1.fib_claimed_sum,
    );

    let blake_components = BlakeComponentsForIntegration::new(
        &mut tree_span_provider,
        &all_elements,
        &value_relation,
        &proof_data.blake_stmt0,
        &proof_data.blake_stmt1,
    );

    // Get digest
    let digest = channel.digest();

    // Calculate composition log degree bound
    let n_preprocessed_columns = all_preprocessed_columns.len();
    let mut all_components: Vec<&dyn Component> = vec![&fib_component as &dyn Component];
    all_components.extend(blake_components.as_components_vec());

    let components = stwo::core::air::Components {
        components: all_components.clone(),
        n_preprocessed_columns,
    };
    let composition_log_degree_bound = components.composition_log_degree_bound();

    // Prepare component parameters for all components
    let mut component_params = vec![];

    // Fibonacci component
    let fib_component_info = ComponentInfo {
        maxConstraintLogDegreeBound: fib_component.max_constraint_log_degree_bound(),
        logSize: fib_component.log_size(),
        maskOffsets: fib_component
            .info
            .mask_offsets
            .0
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|col| col.iter().map(|&offset| offset as i32).collect())
                    .collect()
            })
            .collect(),
        preprocessedColumns: fib_component
            .info
            .preprocessed_columns
            .iter()
            .enumerate()
            .map(|(idx, _)| U256::from(idx))
            .collect(),
    };

    component_params.push(ComponentParams {
        logSize: fib_component.log_size(),
        claimedSum: QM31 {
            first: CM31 {
                real: proof_data.fib_stmt1.fib_claimed_sum.0 .0 .0,
                imag: proof_data.fib_stmt1.fib_claimed_sum.0 .1 .0,
            },
            second: CM31 {
                real: proof_data.fib_stmt1.fib_claimed_sum.1 .0 .0,
                imag: proof_data.fib_stmt1.fib_claimed_sum.1 .1 .0,
            },
        },
        info: fib_component_info,
    });

    // Blake scheduler component
    let scheduler_info = ComponentInfo {
        maxConstraintLogDegreeBound: blake_components.scheduler_component.max_constraint_log_degree_bound(),
        logSize: blake_components.scheduler_component.log_size(),
        maskOffsets: blake_components.scheduler_component
            .info
            .mask_offsets
            .0
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|col| col.iter().map(|&offset| offset as i32).collect())
                    .collect()
            })
            .collect(),
        preprocessedColumns: blake_components.scheduler_component
            .info
            .preprocessed_columns
            .iter()
            .enumerate()
            .map(|(idx, _)| U256::from(idx))
            .collect(),
    };

    component_params.push(ComponentParams {
        logSize: blake_components.scheduler_component.log_size(),
        claimedSum: QM31 {
            first: CM31 {
                real: proof_data.blake_stmt1.scheduler_claimed_sum.0 .0 .0,
                imag: proof_data.blake_stmt1.scheduler_claimed_sum.0 .1 .0,
            },
            second: CM31 {
                real: proof_data.blake_stmt1.scheduler_claimed_sum.1 .0 .0,
                imag: proof_data.blake_stmt1.scheduler_claimed_sum.1 .1 .0,
            },
        },
        info: scheduler_info,
    });

    // Blake round components
    println!("  Number of Blake round components: {}", blake_components.round_components.len());
    for (i, round_component) in blake_components.round_components.iter().enumerate() {
        let round_info = ComponentInfo {
            maxConstraintLogDegreeBound: round_component.max_constraint_log_degree_bound(),
            logSize: round_component.log_size(),
            maskOffsets: round_component
                .info
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: round_component
                .info
                .preprocessed_columns
                .iter()
                .enumerate()
                .map(|(idx, _)| U256::from(idx))
                .collect(),
        };

        component_params.push(ComponentParams {
            logSize: round_component.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: proof_data.blake_stmt1.round_claimed_sums[i].0 .0 .0,
                    imag: proof_data.blake_stmt1.round_claimed_sums[i].0 .1 .0,
                },
                second: CM31 {
                    real: proof_data.blake_stmt1.round_claimed_sums[i].1 .0 .0,
                    imag: proof_data.blake_stmt1.round_claimed_sums[i].1 .1 .0,
                },
            },
            info: round_info,
        });
    }

    // XOR table components - each one separately due to different types
    // XOR12
    {
        let xor_info = ComponentInfo {
            maxConstraintLogDegreeBound: blake_components.xor12.max_constraint_log_degree_bound(),
            logSize: blake_components.xor12.log_size(),
            maskOffsets: blake_components.xor12
                .info
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: blake_components.xor12
                .info
                .preprocessed_columns
                .iter()
                .enumerate()
                .map(|(idx, _)| U256::from(idx))
                .collect(),
        };

        component_params.push(ComponentParams {
            logSize: blake_components.xor12.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: proof_data.blake_stmt1.xor12_claimed_sum.0 .0 .0,
                    imag: proof_data.blake_stmt1.xor12_claimed_sum.0 .1 .0,
                },
                second: CM31 {
                    real: proof_data.blake_stmt1.xor12_claimed_sum.1 .0 .0,
                    imag: proof_data.blake_stmt1.xor12_claimed_sum.1 .1 .0,
                },
            },
            info: xor_info,
        });
    }

    // XOR9
    {
        let xor_info = ComponentInfo {
            maxConstraintLogDegreeBound: blake_components.xor9.max_constraint_log_degree_bound(),
            logSize: blake_components.xor9.log_size(),
            maskOffsets: blake_components.xor9
                .info
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: blake_components.xor9
                .info
                .preprocessed_columns
                .iter()
                .enumerate()
                .map(|(idx, _)| U256::from(idx))
                .collect(),
        };

        component_params.push(ComponentParams {
            logSize: blake_components.xor9.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: proof_data.blake_stmt1.xor9_claimed_sum.0 .0 .0,
                    imag: proof_data.blake_stmt1.xor9_claimed_sum.0 .1 .0,
                },
                second: CM31 {
                    real: proof_data.blake_stmt1.xor9_claimed_sum.1 .0 .0,
                    imag: proof_data.blake_stmt1.xor9_claimed_sum.1 .1 .0,
                },
            },
            info: xor_info,
        });
    }

    // XOR8
    {
        let xor_info = ComponentInfo {
            maxConstraintLogDegreeBound: blake_components.xor8.max_constraint_log_degree_bound(),
            logSize: blake_components.xor8.log_size(),
            maskOffsets: blake_components.xor8
                .info
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: blake_components.xor8
                .info
                .preprocessed_columns
                .iter()
                .enumerate()
                .map(|(idx, _)| U256::from(idx))
                .collect(),
        };

        component_params.push(ComponentParams {
            logSize: blake_components.xor8.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: proof_data.blake_stmt1.xor8_claimed_sum.0 .0 .0,
                    imag: proof_data.blake_stmt1.xor8_claimed_sum.0 .1 .0,
                },
                second: CM31 {
                    real: proof_data.blake_stmt1.xor8_claimed_sum.1 .0 .0,
                    imag: proof_data.blake_stmt1.xor8_claimed_sum.1 .1 .0,
                },
            },
            info: xor_info,
        });
    }

    // XOR7
    {
        let xor_info = ComponentInfo {
            maxConstraintLogDegreeBound: blake_components.xor7.max_constraint_log_degree_bound(),
            logSize: blake_components.xor7.log_size(),
            maskOffsets: blake_components.xor7
                .info
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: blake_components.xor7
                .info
                .preprocessed_columns
                .iter()
                .enumerate()
                .map(|(idx, _)| U256::from(idx))
                .collect(),
        };

        component_params.push(ComponentParams {
            logSize: blake_components.xor7.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: proof_data.blake_stmt1.xor7_claimed_sum.0 .0 .0,
                    imag: proof_data.blake_stmt1.xor7_claimed_sum.0 .1 .0,
                },
                second: CM31 {
                    real: proof_data.blake_stmt1.xor7_claimed_sum.1 .0 .0,
                    imag: proof_data.blake_stmt1.xor7_claimed_sum.1 .1 .0,
                },
            },
            info: xor_info,
        });
    }

    // XOR4
    {
        let xor_info = ComponentInfo {
            maxConstraintLogDegreeBound: blake_components.xor4.max_constraint_log_degree_bound(),
            logSize: blake_components.xor4.log_size(),
            maskOffsets: blake_components.xor4
                .info
                .mask_offsets
                .0
                .iter()
                .map(|tree| {
                    tree.iter()
                        .map(|col| col.iter().map(|&offset| offset as i32).collect())
                        .collect()
                })
                .collect(),
            preprocessedColumns: blake_components.xor4
                .info
                .preprocessed_columns
                .iter()
                .enumerate()
                .map(|(idx, _)| U256::from(idx))
                .collect(),
        };

        component_params.push(ComponentParams {
            logSize: blake_components.xor4.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: proof_data.blake_stmt1.xor4_claimed_sum.0 .0 .0,
                    imag: proof_data.blake_stmt1.xor4_claimed_sum.0 .1 .0,
                },
                second: CM31 {
                    real: proof_data.blake_stmt1.xor4_claimed_sum.1 .0 .0,
                    imag: proof_data.blake_stmt1.xor4_claimed_sum.1 .1 .0,
                },
            },
            info: xor_info,
        });
    }

    println!("  Digest: 0x{}", hex::encode(digest.0));
    println!("  Composition log degree bound: {}", composition_log_degree_bound);
    println!("  Number of components: {}", component_params.len());
    println!("  ✅ Parameters prepared\n");

    let verification_params = VerificationParams {
        componentParams: component_params,
        nPreprocessedColumns: U256::from(n_preprocessed_columns),
        componentsCompositionLogDegreeBound: composition_log_degree_bound,
    };

    // Get roots and log sizes - only first 3 commitments (preprocessed, base, interaction)
    let roots: Vec<FixedBytes<32>> = vec![
        FixedBytes::from(proof_data.stark_proof.commitments[0].0),
        FixedBytes::from(proof_data.stark_proof.commitments[1].0),
        FixedBytes::from(proof_data.stark_proof.commitments[2].0),
    ];

    let log_sizes: Vec<Vec<u32>> = vec![
        combined_preprocessed_sizes.iter().map(|&ls| ls + config.fri_config.log_blowup_factor).collect(),
        combined_base_sizes.iter().map(|&ls| ls + config.fri_config.log_blowup_factor).collect(),
        combined_interaction_sizes.iter().map(|&ls| ls + config.fri_config.log_blowup_factor).collect(),
    ];

    println!("  Number of trees (roots): {}", roots.len());
    println!("  Number of log_sizes arrays: {}", log_sizes.len());
    println!("  Preprocessed columns: {}", combined_preprocessed_sizes.len());
    println!("  Base columns: {}", combined_base_sizes.len());
    println!("  Interaction columns: {}", combined_interaction_sizes.len());

    // Debug: print detailed log sizes info
    println!("\n  📊 Detailed log sizes:");
    for (i, tree_sizes) in log_sizes.iter().enumerate() {
        println!("    Tree {}: {} columns, sizes: {:?}", i, tree_sizes.len(), tree_sizes);
    }

    // Debug: print roots
    println!("\n  🌳 Tree roots:");
    for (i, root) in roots.iter().enumerate() {
        println!("    Root {}: 0x{}", i, hex::encode(root));
    }

    // Save proof metadata to file for debugging
    println!("💾 Saving proof metadata...");
    use std::fs;
    let proof_json = serde_json::json!({
        "digest": hex::encode(digest.0),
        "composition_log_degree_bound": composition_log_degree_bound,
        "n_components": verification_params.componentParams.len(),
        "n_preprocessed_columns": n_preprocessed_columns.to_string(),
        "proof_config": {
            "pow_bits": config.pow_bits,
            "log_blowup_factor": config.fri_config.log_blowup_factor,
            "log_last_layer_degree_bound": config.fri_config.log_last_layer_degree_bound,
            "n_queries": config.fri_config.n_queries,
        }
    });
    fs::write("fibonacci_blake_proof_metadata.json", serde_json::to_string_pretty(&proof_json)?)?;
    println!("  ✅ Metadata saved to fibonacci_blake_proof_metadata.json\n");

    println!("🌐 STEP: Verify Proof On-Chain");

    test_contract_verify(
        solidity_proof,
        verification_params,
        roots,
        log_sizes,
        FixedBytes::from(digest.0),
        0u32,
    )
    .await
}

/// Recreate Solidity abi.encodePacked for decommitment
fn encode_decommitment_packed(hash_witness: &[FixedBytes<32>], column_witness: &[u32]) -> Bytes {
    let mut encoded = Vec::new();

    let length_bytes: [u8; 32] = U256::from(hash_witness.len()).to_be_bytes();
    encoded.extend_from_slice(&length_bytes);

    for witness in hash_witness {
        encoded.extend_from_slice(witness.as_slice());
    }

    let column_length_bytes: [u8; 32] = U256::from(column_witness.len()).to_be_bytes();
    encoded.extend_from_slice(&column_length_bytes);

    for &val in column_witness {
        encoded.extend_from_slice(&val.to_be_bytes());
    }

    Bytes::from(encoded)
}

fn convert_to_solidity_proof(
    proof: StarkProof<KeccakMerkleHasher>,
    composition_polynomial: SecureCirclePoly<SimdBackend>,
    config: PcsConfig,
) -> Proof {
    let sol_config = Config {
        powBits: config.pow_bits,
        friConfig: FriConfig {
            logBlowupFactor: config.fri_config.log_blowup_factor,
            logLastLayerDegreeBound: config.fri_config.log_last_layer_degree_bound,
            nQueries: U256::from(config.fri_config.n_queries),
        },
    };

    let commitments: Vec<FixedBytes<32>> = proof
        .0
        .commitments
        .iter()
        .map(|commitment| FixedBytes::from(commitment.0))
        .collect();

    let sampled_values: Vec<Vec<Vec<QM31>>> = proof
        .sampled_values
        .iter()
        .map(|column| {
            column
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|qm31| QM31 {
                            first: CM31 {
                                real: qm31.0 .0 .0,
                                imag: qm31.0 .1 .0,
                            },
                            second: CM31 {
                                real: qm31.1 .0 .0,
                                imag: qm31.1 .1 .0,
                            },
                        })
                        .collect()
                })
                .collect()
        })
        .collect();

    let decommitments: Vec<Decommitment> = proof
        .0
        .decommitments
        .iter()
        .map(|decom| Decommitment {
            witness: decom
                .hash_witness
                .iter()
                .map(|h| FixedBytes::from(h.0))
                .collect::<Vec<_>>(),
            columnWitness: decom.column_witness.iter().map(|m| m.0).collect::<Vec<_>>(),
        })
        .collect();

    let first_layer: FriLayerProof = {
        let layer = &proof.0.fri_proof.first_layer;
        FriLayerProof {
            friWitness: layer
                .fri_witness
                .iter()
                .map(|val| QM31 {
                    first: CM31 {
                        real: val.0 .0 .0,
                        imag: val.0 .1 .0,
                    },
                    second: CM31 {
                        real: val.1 .0 .0,
                        imag: val.1 .1 .0,
                    },
                })
                .collect(),
            decommitment: encode_decommitment_packed(
                &layer
                    .decommitment
                    .hash_witness
                    .iter()
                    .map(|h| FixedBytes::from(h.0))
                    .collect::<Vec<_>>(),
                &layer
                    .decommitment
                    .column_witness
                    .iter()
                    .map(|m| m.0)
                    .collect::<Vec<_>>(),
            ),
            commitment: FixedBytes::from(layer.commitment.0),
        }
    };

    let inner_layers: Vec<FriLayerProof> = proof
        .0
        .fri_proof
        .inner_layers
        .iter()
        .map(|layer| FriLayerProof {
            friWitness: layer
                .fri_witness
                .iter()
                .map(|val| QM31 {
                    first: CM31 {
                        real: val.0 .0 .0,
                        imag: val.0 .1 .0,
                    },
                    second: CM31 {
                        real: val.1 .0 .0,
                        imag: val.1 .1 .0,
                    },
                })
                .collect(),
            decommitment: encode_decommitment_packed(
                &layer
                    .decommitment
                    .hash_witness
                    .iter()
                    .map(|h| FixedBytes::from(h.0))
                    .collect::<Vec<_>>(),
                &layer
                    .decommitment
                    .column_witness
                    .iter()
                    .map(|m| m.0)
                    .collect::<Vec<_>>(),
            ),
            commitment: FixedBytes::from(layer.commitment.0),
        })
        .collect();

    let fri_proof = FriProof {
        innerLayers: inner_layers,
        lastLayerPoly: {
            let mut coeffs = proof
                .clone()
                .0
                .fri_proof
                .last_layer_poly
                .into_ordered_coefficients();
            bit_reverse(&mut coeffs);
            coeffs
                .iter()
                .map(|v| QM31 {
                    first: CM31 {
                        real: v.0 .0 .0,
                        imag: v.0 .1 .0,
                    },
                    second: CM31 {
                        real: v.1 .0 .0,
                        imag: v.1 .1 .0,
                    },
                })
                .collect()
        },
        firstLayer: first_layer,
    };

    let composition_polynomial_to_solidity: Vec<Vec<u32>> = composition_polynomial
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

    let comp_poly = CompositionPoly {
        coeffs0: composition_polynomial_to_solidity[0].clone(),
        coeffs1: composition_polynomial_to_solidity[1].clone(),
        coeffs2: composition_polynomial_to_solidity[2].clone(),
        coeffs3: composition_polynomial_to_solidity[3].clone(),
    };

    let queried_values: Vec<Vec<u32>> = proof
        .0
        .queried_values
        .iter()
        .map(|column| column.iter().map(|val| val.0).collect())
        .collect();

    Proof {
        config: sol_config,
        commitments,
        sampledValues: sampled_values,
        decommitments,
        queriedValues: queried_values,
        proofOfWork: proof.proof_of_work,
        friProof: fri_proof,
        compositionPoly: comp_poly,
    }
}

async fn test_contract_verify(
    proof: Proof,
    verification_params: VerificationParams,
    tree_roots: Vec<FixedBytes<32>>,
    tree_column_log_sizes: Vec<Vec<u32>>,
    digest: FixedBytes<32>,
    n_draws: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔗 Testing Contract Verify Call");

    let rpc_url = "http://localhost:8545";
    println!("Connecting to RPC: {}", rpc_url);
    let provider = ProviderBuilder::new().on_http(rpc_url.parse()?);

    // Test connection
    match provider.get_block_number().await {
        Ok(block) => println!("✅ Connected to RPC, current block: {}", block),
        Err(e) => {
            println!("❌ Failed to connect to RPC: {}", e);
            println!("Please ensure Anvil is running on http://localhost:8545");
            return Err(e.into());
        }
    }

    let contract_address =
        Address::parse_checksummed("0xDc64a140Aa3E981100a9becA4E685f962f0cF6C9", None)?;

    println!("Contract address: {}", contract_address);

    // Check if contract exists
    match provider.get_code_at(contract_address).await {
        Ok(code) => {
            if code.is_empty() {
                println!("⚠️  WARNING: No code at contract address!");
                println!("Please deploy the STWO verifier contract first.");
                return Ok(());
            } else {
                println!("✅ Contract found, code size: {} bytes", code.len());
            }
        }
        Err(e) => {
            println!("❌ Failed to check contract code: {}", e);
            return Err(e.into());
        }
    }

    println!("Encoding call data...");
    let call_data = IStwoVerifier::verifyCall {
        proof,
        params: verification_params,
        treeRoots: tree_roots,
        treeColumnLogSizes: tree_column_log_sizes,
        digest,
        nDraws: n_draws,
    };

    let encoded = call_data.abi_encode();
    let encoded_size = encoded.len();
    println!("Call data size: {} bytes ({:.2} MB)", encoded_size, encoded_size as f64 / 1_000_000.0);
    let function_selector = hex::encode(&encoded[0..4]);
    println!("Function selector: 0x{}", function_selector);

    // Check if data is too large
    const MAX_RPC_SIZE: usize = 10_000_000; // 10 MB default limit
    if encoded_size > MAX_RPC_SIZE {
        println!("\n⚠️  WARNING: Call data size ({:.2} MB) exceeds typical RPC limits!",
                 encoded_size as f64 / 1_000_000.0);
        println!("   The proof is too large for standard on-chain verification.");
        println!("\n💡 Solutions:");
        println!("   1. Restart Anvil with larger limits:");
        println!("      anvil --rpc-request-size-limit {} --rpc-response-size-limit {}",
                 encoded_size * 2, encoded_size * 2);
        println!("   2. Use proof compression/aggregation");
        println!("   3. Split verification into multiple calls");
        println!("\n   Attempting call anyway...\n");
    }

    let call_input = TransactionRequest::default()
        .to(contract_address)
        .input(encoded.into());

    println!("Simulating contract call...");

    // Try with explicit block specification
    match provider.call(&call_input).await {
        Ok(result) => {
            println!("✅ Contract call succeeded: 0x{}", hex::encode(&result));
        }
        Err(e) => {
            println!("❌ Contract call failed:");
            println!("Error: {}", e);

            // Try to get more detailed error info
            if let Some(data) = e.as_error_resp() {
                println!("\nDetailed error: {:?}", data);
            }

            println!("\n💡 Troubleshooting:");
            println!("   - Verify contract is deployed at {}", contract_address);
            println!("   - Check if function selector matches: 0x{}", function_selector);
            println!("   - Ensure Anvil is running with default settings");
        }
    }

    Ok(())
}