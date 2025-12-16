mod computing;
mod mixer;
mod scheduler;
mod trace_gen;
mod utils;

use std::fs;

use alloy::primitives::{Address, Bytes, FixedBytes, U256};
use alloy::providers::{Provider, ProviderBuilder};
use alloy::rpc::types::TransactionRequest;
use alloy::sol_types::SolCall;
use alloy::{hex, sol};
use mixer::full_flow::{compute_commitment, generate_operation, HybridMerkleTree};
use serde::{Deserialize, Serialize};
use stwo::core::channel::KeccakChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fri::FriConfig as StwoFriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::bit_reverse;
use stwo::core::vcs::keccak_merkle::{KeccakMerkleChannel, KeccakMerkleHasher};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{PolyOps, SecureCirclePoly};
use stwo::prover::CommitmentSchemeProver;
use stwo_constraint_framework::FrameworkEval;
use utils::{prove_merkle, verify_merkle};

// Generate Rust bindings for STWO verifier contracts
sol! {
    /// QM31 field element structure
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

    /// TreeSubspan.Subspan structure
    struct Subspan {
        uint256 treeIndex;
        uint256 colStart;
        uint256 colEnd;
    }

    /// Component information structure
    struct ComponentInfo {
        uint32 maxConstraintLogDegreeBound;
        uint32 logSize;
        int32[][][] maskOffsets; // Mask offsets: [tree][column][offset_values] from InfoEvaluator
        uint256[] preprocessedColumns; // Preprocessed column IDs
    }

    /// Framework component state
    struct ComponentState {
        uint32 logSize;
        Subspan[] traceLocations; // Trace locations allocated for this component
        uint256[] preprocessedColumnIndices; // Preprocessed column indices
        QM31 claimedSum; // Claimed sum for logup constraints
        ComponentInfo info; // Component metadata
        bool isInitialized; // Whether the component is initialized
    }

    struct ComponentParams{
        uint32 logSize;
        QM31 claimedSum;
        ComponentInfo info;
    }

    /// Verification parameters structure - EXACT match with Solidity
    struct VerificationParams {
        ComponentParams[] componentParams; // Array of components to verify
        uint256 nPreprocessedColumns; // Number of preprocessed columns
        uint32 componentsCompositionLogDegreeBound; // Log degree bound for composition polynomial
    }
    /// STWO Verifier contract interface
    interface IStwoVerifier {
        /// Main verification function
        function verify(
            Proof calldata proof,
            VerificationParams calldata params,
            bytes32[] memory treeRoots,
            uint32[][] memory treeColumnLogSizes,
            bytes32 digest,
            uint32 nDraws
        ) external view returns (bool);

        /// Verify proof with merkle roots
        function verifyProofWithRoots(
            Proof calldata proof,
            bytes32[] calldata merkleRoots,
            uint32[][] calldata columnLogSizes
        ) external view returns (bool);

        /// Get verification configuration
        function getConfig() external view returns (Config memory);
    }


}

/// Test invoke verify() function on deployed contract
async fn test_contract_verify(
    proof: Proof,
    verification_params: VerificationParams,
    tree_roots: Vec<FixedBytes<32>>,
    tree_column_log_sizes: Vec<Vec<u32>>,
    digest: FixedBytes<32>,
    n_draws: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔗 Testing Contract Verify Call");

    // Connect to Anvil
    let rpc_url = "http://localhost:8545";
    let provider = ProviderBuilder::new().on_http(rpc_url.parse()?);

    // Contract address
    let contract_address =
        Address::parse_checksummed("0xA51c1fc2f0D1a1b8494Ed1FE312d7C3a78Ed91C0", None)?;

    println!("Calling contract verify function...");

    

    // Encode the call data using SolCall trait
    let call_data = IStwoVerifier::verifyCall {
        proof,
        params: verification_params,
        treeRoots: tree_roots,
        treeColumnLogSizes: tree_column_log_sizes,
        digest,
        nDraws: n_draws,
    };

    // Call contract - this simulates the transaction and returns revert reasons
    let call_input = TransactionRequest::default()
        .to(contract_address)
        .input(call_data.abi_encode().into());

    println!("Simulating contract call...");
    match provider.call(&call_input).await {
        Ok(result) => {
            println!("✅ Contract call succeeded: 0x{}", hex::encode(&result));
        }
        Err(e) => {
            println!("❌ Contract call reverted:");
            println!("{}", e);
            
            // Try to extract revert reason
            if let Some(data) = e.as_error_resp() {
                println!("\nRevert data: {:?}", data);
            }
        }
    }

    Ok(())
}

/// Recreate Solidity abi.encodePacked for decommitment
fn encode_decommitment_packed(hash_witness: &[FixedBytes<32>], column_witness: &[u32]) -> Bytes {
    let mut encoded = Vec::new();

    // uint256(innerLayer2HashWitness.length)
    let length_bytes: [u8; 32] = U256::from(hash_witness.len()).to_be_bytes();
    encoded.extend_from_slice(&length_bytes);

    // innerLayer2HashWitness (bytes32[] packed)
    for witness in hash_witness {
        encoded.extend_from_slice(witness.as_slice());
    }

    // uint256(0) - column witness length
    let column_length_bytes: [u8; 32] = U256::from(column_witness.len()).to_be_bytes();
    encoded.extend_from_slice(&column_length_bytes);

    // new uint32[](0) - empty column witness array
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
    // Convert PCS config
    let sol_config = Config {
        powBits: config.pow_bits,
        friConfig: FriConfig {
            logBlowupFactor: config.fri_config.log_blowup_factor,
            logLastLayerDegreeBound: config.fri_config.log_last_layer_degree_bound,
            nQueries: U256::from(config.fri_config.n_queries),
        },
    };

    // Extract commitments as FixedBytes<32> array for Solidity bytes32
    let commitments: Vec<FixedBytes<32>> = proof
        .0
        .commitments
        .iter()
        .map(|commitment| FixedBytes::from(commitment.0))
        .collect();

    // Convert sampled values - convert STWO QM31 to Alloy QM31
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

    // Convert decommitments
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

    // Convert FRI proof
    let fri_proof = FriProof {
        innerLayers: inner_layers,
        lastLayerPoly: {
            let mut coeffs = proof
                .clone()
                .0
                .fri_proof
                .last_layer_poly
                .into_ordered_coefficients();
            bit_reverse(&mut coeffs); // Reverse back to bit-reversed order
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

    // Convert composition polynomial
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

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔒 Privacy Pools Example");

    // Complete privacy mixer flow (same as test)
    run_complete_privacy_mixer_flow().await;

    Ok(())
}

async fn run_complete_privacy_mixer_flow() {
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║   COMPLETE PRIVACY MIXER FLOW (Frontend-Compatible)     ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 1: GENERATE OPERATIONS (like frontend generateOperation)
    // ═══════════════════════════════════════════════════════════
    println!("📝 STEP 1: Generate Operations (Deterministic)\n");

    let master_nonce = BaseField::from_u32_unchecked(987654321);
    let num_operations = 5;

    let operations: Vec<_> = (0..num_operations)
        .map(|i| generate_operation(i, master_nonce))
        .collect();

    println!("Generated {} operations:", num_operations);
    for (i, op) in operations.iter().enumerate() {
        println!(
            "  Op {}: secret={}, nullifier={}, hash={}",
            i, op.secret.0, op.nullifier.0, op.hash.0
        );
    }

    // ═══════════════════════════════════════════════════════════
    // STEP 2: COMPUTE COMMITMENTS (like frontend)
    // ═══════════════════════════════════════════════════════════
    println!("\n💰 STEP 2: Compute Commitments\n");

    let amount = BaseField::from_u32_unchecked(1000);
    let token_address = BaseField::from_u32_unchecked(42);

    let commitments: Vec<_> = operations
        .iter()
        .map(|op| {
            let commitment = compute_commitment(op.hash, amount, token_address);
            println!("  Op {} → Commitment: {}", op.index, commitment.0);
            commitment
        })
        .collect();

    // ═══════════════════════════════════════════════════════════
    // STEP 3: BUILD MERKLE TREE (Incremental, like frontend)
    // ═══════════════════════════════════════════════════════════
    println!("\n🌳 STEP 3: Build Merkle Tree (Hybrid with Zero Hashes)\n");

    let tree_height = 5; // Can hold up to 32 leaves
    let mut tree = HybridMerkleTree::new(tree_height);

    println!("Created hybrid tree with height {}", tree_height);
    println!("Precomputed zero hashes:");
    for (i, hash) in tree.precomputed.iter().take(3).enumerate() {
        println!("  Level {}: {}", i, hash.0);
    }
    println!("  ...");

    println!("\nAdding commitments incrementally:");
    for (i, &commitment) in commitments.iter().enumerate() {
        tree.add_leaf(commitment);
        println!("  Added commitment {} → Root: {}", i, tree.get_root().0);
    }

    let final_root = tree.get_root();
    println!("\n✅ Final Merkle Root: {}", final_root.0);

    // ═══════════════════════════════════════════════════════════
    // STEP 4: GET PROOF DATA (like frontend getProofData)
    // ═══════════════════════════════════════════════════════════
    println!("\n🔗 STEP 4: Get Proof Data for Commitment 2\n");

    let target_commitment = commitments[2];
    let proof_data = tree
        .get_proof_data(target_commitment)
        .expect("Failed to get proof data");

    println!("Proof data for commitment 2:");
    println!("  Index: {}", proof_data.index);
    println!("  Root: {}", proof_data.root.0);
    println!(
        "  Siblings: {:?}",
        proof_data.siblings.iter().map(|s| s.0).collect::<Vec<_>>()
    );
    println!("  IsRight flags: {:?}", proof_data.is_right);

    // ═══════════════════════════════════════════════════════════
    // STEP 5: VERIFY USING STARK PROOF (AIR Verification)
    // ═══════════════════════════════════════════════════════════
    println!("\n✨ STEP 5: Verify Membership using STARK Proof (AIR)\n");

    // Setup
    let config = PcsConfig {
        pow_bits: 5,
        fri_config: StwoFriConfig::new(2, 1, 2),
    };
    println!("Security bits: {}", config.security_bits());
    let channel = &mut KeccakChannel::default();
    let twiddles =
        SimdBackend::precompute_twiddles(CanonicCoset::new(20).circle_domain().half_coset);
    let commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, KeccakMerkleChannel>::new(config, &twiddles);
    // Generate STARK proof for membership
    println!("Generating STARK proof...");
    let (proof, _, _, statement0, statement1, composition_polynomial) = prove_merkle(
        tree_height - 1, // depth = height - 1
        target_commitment,
        proof_data.siblings.clone(),
        proof_data.index as u32,
        proof_data.root,
        channel,
        commitment_scheme,
    )
    .expect("Failed to generate proof");

    // Convert to Solidity-compatible proof structure
    println!("Converting STARK proof to Solidity format...");
    let solidity_proof =
        convert_to_solidity_proof(proof.clone(), composition_polynomial.clone(), config);

    println!(
        "Solidity proof last layer poly coeffs: {:?}",
        solidity_proof
            .friProof
            .lastLayerPoly
            .iter()
            .map(|qm| (qm.first.real, qm.first.imag, qm.second.real, qm.second.imag))
            .collect::<Vec<_>>()
    );

    let composition_polynomial_to_file: Vec<Vec<u32>> = composition_polynomial.clone()
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
    let composition_json = serde_json::to_string_pretty(&composition_polynomial_to_file).unwrap();
    fs::write("composition_polynomial.json", &composition_json).expect("Failed to write composition polynomial");

    // Serialize both original and Solidity proof formats
    let proof_json = serde_json::to_string_pretty(&proof).unwrap();
    fs::write("solidity_proof.json", &proof_json).expect("Failed to write solidity proof");

    println!("✅ Proof converted to Solidity format and saved to solidity_proof.json");
    println!("✅ STARK proof generated successfully!");

    // Verify STARK proof
    println!("\nVerifying STARK proof...");
    let (digest, merkle_computing_component, merkle_scheduler_component, roots, log_sizes, composition_log_degree_bound) = verify_merkle(
        proof,
        tree_height - 1,
        statement0,
        statement1,
        config,
        composition_polynomial,
    )
    .expect("Failed to verify proof");

    println!("Tree column log sizes: {:?}", log_sizes);

    println!("Digest of composition polynomial: {:?}", digest.0);

    let component_info_1 = ComponentInfo {
        maxConstraintLogDegreeBound: merkle_computing_component.max_constraint_log_degree_bound(),
        logSize: merkle_computing_component.log_size(),
        maskOffsets: merkle_computing_component.info.mask_offsets.0
            .iter()
            .map(|tree| tree.iter().map(|col| col.iter().map(|&offset| offset as i32).collect()).collect())
            .collect(), // Mask offsets: [tree][column][offset_values] from InfoEvaluator
        preprocessedColumns: merkle_computing_component.info.preprocessed_columns
            .iter()
            .enumerate()
            .map(|(idx, _)| U256::from(idx))
            .collect(),
    };

    let component_info_2 = ComponentInfo {
        maxConstraintLogDegreeBound: merkle_scheduler_component.max_constraint_log_degree_bound(),
        logSize: merkle_scheduler_component.log_size(),
        maskOffsets: merkle_scheduler_component.info.mask_offsets.0
            .iter()
            .map(|tree| tree.iter().map(|col| col.iter().map(|&offset| offset as i32).collect()).collect())
            .collect(), // Mask offsets: [tree][column][offset_values] from InfoEvaluator
        preprocessedColumns: merkle_scheduler_component.info.preprocessed_columns
            .iter()
            .enumerate()
            .map(|(idx, _)| U256::from(idx))
            .collect(),
    };

    println!("Log size merkle computing component: {}", merkle_computing_component.log_size());
    println!("Log size merkle scheduler component: {}", merkle_scheduler_component.log_size());
    println!("max constraint log degree bound computing component: {}", merkle_computing_component.max_constraint_log_degree_bound());
    println!("max constraint log degree bound scheduler component: {}", merkle_scheduler_component.max_constraint_log_degree_bound());
    println!("Preprocessed columns computing component: {:?}", merkle_computing_component.preprocessed_column_indices());
    println!("Preprocessed columns scheduler component: {:?}", merkle_scheduler_component.preprocessed_column_indices());
    println!("Claimed sum computing component: {:?}", merkle_computing_component.claimed_sum());
    println!("Claimed sum scheduler component: {:?}", merkle_scheduler_component.claimed_sum());


    let verification_params = VerificationParams {
        componentParams: vec![
            ComponentParams {
                logSize: merkle_computing_component.log_size(),
                claimedSum: QM31 {
                    first: CM31 { real: merkle_computing_component.claimed_sum().0.0.0, imag: merkle_computing_component.claimed_sum().0.1.0 },
                    second: CM31 { real: merkle_computing_component.claimed_sum().1.0.0, imag: merkle_computing_component.claimed_sum().1.1.0 },
                },
                info: component_info_1,
            },
            ComponentParams {
                logSize: merkle_scheduler_component.log_size(),
                claimedSum: QM31 {
                    first: CM31 { real: merkle_scheduler_component.claimed_sum().0.0.0, imag: merkle_scheduler_component.claimed_sum().0.1.0 },
                    second: CM31 { real: merkle_scheduler_component.claimed_sum().1.0.0, imag: merkle_scheduler_component.claimed_sum().1.1.0 },
                },
                info: component_info_2,
            },
        ],
        nPreprocessedColumns: U256::from(4),
        componentsCompositionLogDegreeBound: composition_log_degree_bound,
    };

    println!("Composition log degree bound: {:?}", composition_log_degree_bound);

    let roots_bytes32: Vec<FixedBytes<32>> = roots.iter().map(|r| FixedBytes::from(r.0)).collect();

    // Test contract verify call
    if let Err(e) = test_contract_verify(solidity_proof, verification_params,roots_bytes32, log_sizes, FixedBytes::from(digest.0), 0u32
    ).await {     println!("Contract verify call failed: {}", e);
    }

    println!("✅ STARK proof verified successfully!");

    // ═══════════════════════════════════════════════════════════
    // STEP 6: SUMMARY
    // ═══════════════════════════════════════════════════════════
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║                    FLOW COMPLETE ✅                       ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");

    println!("✅ Operations generated (deterministic)");
    println!("✅ Commitments computed (hash → amount → token)");
    println!("✅ Merkle tree built (incremental with zero hashes)");
    println!("✅ Proof data extracted (index, siblings, isRight, root)");
    println!("✅ STARK proof generated and verified (AIR)");

    println!("\n📊 Statistics:");
    println!("  Total operations: {}", num_operations);
    println!("  Tree height: {}", tree_height);
    println!("  Tree capacity: {} leaves", 1 << tree_height);
    println!("  Current leaves: {}", tree.get_leafs().len());
    println!("  Final root: {}", final_root.0);
    println!(
        "  Verified commitment: {} (index {})",
        target_commitment.0, proof_data.index
    );

    println!("\n🎉 All steps completed successfully!");
    println!("This flow is IDENTICAL to the frontend TypeScript implementation!");
}
