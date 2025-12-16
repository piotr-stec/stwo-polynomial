use alloy::primitives::{Address, Bytes, FixedBytes, U256};
use alloy::providers::{Provider, ProviderBuilder};
use alloy::rpc::types::TransactionRequest;
use alloy::sol_types::SolCall;
use alloy::{hex, sol};
use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::KeccakChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fri::FriConfig as StwoFriConfig;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::bit_reverse;
use stwo::core::vcs::keccak_merkle::{KeccakMerkleChannel, KeccakMerkleHasher};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps, SecureCirclePoly};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::CommitmentSchemeProver;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};
use stwo_polynomial::prove::prove;
use stwo_polynomial::verify::verify;

// Generate Rust bindings for STWO verifier contracts (same as privacy_pools)
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

#[derive(Clone)]
pub struct FibonacciEval {
    pub log_n_rows: u32,
}

impl FrameworkEval for FibonacciEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a = eval.next_trace_mask(); // f(n-2)
        let b = eval.next_trace_mask(); // f(n-1)
        let c = eval.next_trace_mask(); // f(n)

        eval.add_constraint(c - (a + b));

        eval
    }
}

pub type FibonacciComponent = FrameworkComponent<FibonacciEval>;

/// Calculate the minimum log_size needed to compute f(target_n)
pub fn calculate_log_size(target_n: usize) -> u32 {
    let min_rows = target_n.saturating_sub(1).max(1);
    let log_size = (min_rows as f64).log2().ceil() as u32;
    log_size.max(2)
}

/// Generate trace for fibonacci sequence
pub fn gen_fibonacci_trace(
    target_n: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    BaseField,
    u32,
) {
    let log_size = calculate_log_size(target_n);
    let n_rows = 1 << log_size;

    let mut col_a = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_b = Col::<SimdBackend, BaseField>::zeros(n_rows);
    let mut col_c = Col::<SimdBackend, BaseField>::zeros(n_rows);

    let mut a = BaseField::from_u32_unchecked(0);
    let mut b = BaseField::from_u32_unchecked(1);
    let mut target_value = BaseField::from_u32_unchecked(0);

    let compute_rows = (target_n - 1).min(n_rows);

    for row in 0..compute_rows {
        let c = a + b;

        col_a.set(row, a);
        col_b.set(row, b);
        col_c.set(row, c);

        let current_index = row + 2;
        if current_index == target_n {
            target_value = c;
        }

        a = b;
        b = c;
    }

    let domain = CanonicCoset::new(log_size).circle_domain();

    let trace = vec![
        CircleEvaluation::new(domain, col_a),
        CircleEvaluation::new(domain, col_b),
        CircleEvaluation::new(domain, col_c),
    ];

    (trace, target_value, log_size)
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
    let provider = ProviderBuilder::new().on_http(rpc_url.parse()?);

    let contract_address =
        Address::parse_checksummed("0x0DCd1Bf9A1b36cE34237eEaFef220932846BCD82", None)?;

    println!("Calling contract verify function...");

    let call_data = IStwoVerifier::verifyCall {
        proof,
        params: verification_params,
        treeRoots: tree_roots,
        treeColumnLogSizes: tree_column_log_sizes,
        digest,
        nDraws: n_draws,
    };

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

            if let Some(data) = e.as_error_resp() {
                println!("\nRevert data: {:?}", data);
            }
        }
    }

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔢 Fibonacci On-Chain Verification Example");
    println!("════════════════════════════════════════════\n");

    // Configuration
    let target_n = 10; // Compute f(10) = 55
    println!("📝 Computing Fibonacci f({}) using STARK proof\n", target_n);

    // ═══════════════════════════════════════════════════════════
    // STEP 1: GENERATE FIBONACCI TRACE
    // ═══════════════════════════════════════════════════════════
    println!("📊 STEP 1: Generate Fibonacci Trace");
    let (trace, target_value, log_size) = gen_fibonacci_trace(target_n);
    println!("  Trace size: 2^{} = {} rows", log_size, 1 << log_size);
    println!("  Target value f({}) = {}", target_n, target_value.0);
    println!("  ✅ Trace generated\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 2: GENERATE STARK PROOF
    // ═══════════════════════════════════════════════════════════
    println!("🔐 STEP 2: Generate STARK Proof");

    let config = PcsConfig {
        pow_bits: 15,
        fri_config: StwoFriConfig::new(2, 3, 27),
    };
    println!("  Security bits: {}", config.security_bits());

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut KeccakChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, KeccakMerkleChannel>::new(config, &twiddles);

    // Commit preprocessed (empty for Fibonacci)
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

    let (proof, composition_polynomial) = prove(&[&component], channel, commitment_scheme)?;
    println!("  ✅ STARK proof generated\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 3: VERIFY PROOF (OFF-CHAIN)
    // ═══════════════════════════════════════════════════════════
    println!("✅ STEP 3: Verify Proof (Off-Chain)");

    let verify_channel = &mut KeccakChannel::default();
    let mut verify_commitment_scheme =
        CommitmentSchemeVerifier::<KeccakMerkleChannel>::new(config);

    // Commit preprocessed
    verify_commitment_scheme.commit(
        proof.commitments[0],
        &component.trace_log_degree_bounds()[0],
        verify_channel,
    );

    // Commit trace
    verify_commitment_scheme.commit(
        proof.commitments[1],
        &component.trace_log_degree_bounds()[1],
        verify_channel,
    );

    // Get digest before verification
    let digest = verify_channel.digest();

    // Verify the proof
    verify(
        &[&component],
        verify_channel,
        &mut verify_commitment_scheme,
        proof.clone(),
        composition_polynomial.clone(),
    )?;

    // Calculate composition log degree bound
    let n_preprocessed_columns = verify_commitment_scheme.trees[0].column_log_sizes.len();
    let components_vec: Vec<&dyn Component> = vec![&component as &dyn Component];
    let components = stwo::core::air::Components {
        components: components_vec,
        n_preprocessed_columns,
    };
    let composition_log_degree_bound = components.composition_log_degree_bound();

    // Get roots and log sizes
    let roots = vec![proof.commitments[0], proof.commitments[1]];
    let log_sizes: Vec<Vec<u32>> = component
        .trace_log_degree_bounds()
        .iter()
        .map(|tree| tree.iter().map(|&ls| ls + config.fri_config.log_blowup_factor).collect())
        .collect();

    println!("  Digest: 0x{}", hex::encode(digest.0));
    println!("  Composition log degree bound: {}", composition_log_degree_bound);
    println!("  ✅ Off-chain verification successful\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 4: CONVERT TO SOLIDITY FORMAT
    // ═══════════════════════════════════════════════════════════
    println!("🔄 STEP 4: Convert Proof to Solidity Format");

    let solidity_proof = convert_to_solidity_proof(proof, composition_polynomial, config);
    println!("  ✅ Proof converted to Solidity format\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 5: PREPARE VERIFICATION PARAMETERS
    // ═══════════════════════════════════════════════════════════
    println!("📋 STEP 5: Prepare Verification Parameters");

    let component_info = ComponentInfo {
        maxConstraintLogDegreeBound: component.max_constraint_log_degree_bound(),
        logSize: component.log_size(),
        maskOffsets: component
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
        preprocessedColumns: component
            .info
            .preprocessed_columns
            .iter()
            .enumerate()
            .map(|(idx, _)| U256::from(idx))
            .collect(),
    };

    let verification_params = VerificationParams {
        componentParams: vec![ComponentParams {
            logSize: component.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: component.claimed_sum().0 .0 .0,
                    imag: component.claimed_sum().0 .1 .0,
                },
                second: CM31 {
                    real: component.claimed_sum().1 .0 .0,
                    imag: component.claimed_sum().1 .1 .0,
                },
            },
            info: component_info,
        }],
        nPreprocessedColumns: U256::from(0),
        componentsCompositionLogDegreeBound: composition_log_degree_bound,
    };

    let roots_bytes32: Vec<FixedBytes<32>> =
        roots.iter().map(|r| FixedBytes::from(r.0)).collect();

    println!("  Component log size: {}", component.log_size());
    println!(
        "  Max constraint log degree bound: {}",
        component.max_constraint_log_degree_bound()
    );
    println!("  ✅ Parameters prepared\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 6: VERIFY ON-CHAIN
    // ═══════════════════════════════════════════════════════════
    println!("🌐 STEP 6: Verify Proof On-Chain");

    if let Err(e) = test_contract_verify(
        solidity_proof,
        verification_params,
        roots_bytes32,
        log_sizes,
        FixedBytes::from(digest.0),
        0u32,
    )
    .await
    {
        println!("Contract verify call failed: {}", e);
    }

    // ═══════════════════════════════════════════════════════════
    // SUMMARY
    // ═══════════════════════════════════════════════════════════
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║              FIBONACCI ON-CHAIN COMPLETE ✅               ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");

    println!("📊 Summary:");
    println!("  Target: f({}) = {}", target_n, target_value.0);
    println!("  Trace size: 2^{} = {} rows", log_size, 1 << log_size);
    println!("  Security bits: {}", config.security_bits());
    println!("  ✅ Off-chain verification: PASSED");
    println!("  ✅ On-chain verification: CHECK ABOVE");

    println!("\n🎉 Fibonacci STARK proof generated and verified!");

    Ok(())
}
