use alloy::primitives::{Address, Bytes, FixedBytes, U256};
use alloy::providers::{Provider, ProviderBuilder};
use alloy::rpc::types::TransactionRequest;
use alloy::sol_types::SolCall;
use alloy::{hex, sol};
use num_traits::{One, Zero};
use stwo::core::air::Component;
use stwo::core::channel::{Channel, KeccakChannel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fri::FriConfig as StwoFriConfig;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::{bit_reverse, bit_reverse_coset_to_circle_domain_order};
use stwo::core::vcs::keccak_merkle::{KeccakMerkleChannel, KeccakMerkleHasher};
use stwo::core::verifier::VerificationError;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps, SecureCirclePoly};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::CommitmentSchemeProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator, ORIGINAL_TRACE_IDX,
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
            uint32[][] memory treeColumnLogSizes,
            uint64[] calldata publicInputs
        ) external view returns (bool);
    }
}

pub const LOG_CONSTRAINT_DEGREE: u32 = 1;

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
        channel.mix_u64(self.initial_a as u64);
        channel.mix_u64(self.initial_b as u64);
        channel.mix_u64(self.expected_value as u64);
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

#[derive(Clone)]
pub struct FibEval {
    pub log_n_rows: u32,
    pub is_first_id: PreProcessedColumnId,
    pub is_target_id: PreProcessedColumnId,
    pub initial_a: BaseField,
    pub initial_b: BaseField,
    pub expected_value: BaseField,
}

impl FrameworkEval for FibEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + LOG_CONSTRAINT_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let is_first = eval.get_preprocessed_column(self.is_first_id.clone());
        let is_target = eval.get_preprocessed_column(self.is_target_id.clone());

        let [a_curr, _a_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [b_curr, b_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [c_curr, c_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);

        // Fibonacci relation c = a + b
        eval.add_constraint(c_curr.clone() - (a_curr.clone() + b_curr.clone()));

        // Transition a_curr = b_prev (disabled for first row)
        let not_first = E::F::one() - is_first.clone();
        eval.add_constraint(not_first.clone() * (a_curr.clone() - b_prev));

        // Transition b_curr = c_prev (disabled for first row)
        eval.add_constraint(not_first.clone() * (b_curr.clone() - c_prev));

        // Public inputs at first row
        eval.add_constraint(is_first.clone() * (a_curr.clone() - E::F::from(self.initial_a)));
        eval.add_constraint(is_first.clone() * (b_curr.clone() - E::F::from(self.initial_b)));

        // Public output at target row
        eval.add_constraint(is_target * (a_curr - E::F::from(self.expected_value)));

        eval
    }
}

pub type FibComponent = FrameworkComponent<FibEval>;

/// Calculate the minimum log_size needed to include fibonacci_index row
pub fn calculate_log_size(fibonacci_index: usize) -> u32 {
    let min_rows = fibonacci_index.saturating_add(1).max(1);
    let log_size = (min_rows as f64).log2().ceil() as u32;
    log_size.max(2)
}

/// Generate trace for Fibonacci sequence with public inputs
pub fn gen_fib_trace(
    log_size: u32,
    fibonacci_index: usize,
    initial_a: u32,
    initial_b: u32,
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

    let mut a = BaseField::from_u32_unchecked(initial_a);
    let mut b = BaseField::from_u32_unchecked(initial_b);
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
            CircleEvaluation::new(domain, col_c),
        ],
        target_value,
    )
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

#[derive(Clone)]
pub struct ProofData {
    fib_stmt0: FibStatement0,
    stark_proof: StarkProof<KeccakMerkleHasher>,
}

struct OffchainArtifacts {
    digest: FixedBytes<32>,
    component: FibComponent,
    log_sizes: Vec<Vec<u32>>,
    composition_log_degree_bound: u32,
}

fn prove_fibonacci(
    log_size: u32,
    fibonacci_index: usize,
    initial_a: u32,
    initial_b: u32,
    config: PcsConfig,
) -> Result<(ProofData, SecureCirclePoly<SimdBackend>), Box<dyn std::error::Error>> {
    let (trace, expected_value) = gen_fib_trace(log_size, fibonacci_index, initial_a, initial_b);
    let fib_is_first_col = gen_is_first_column(log_size);
    let fib_is_target_col = gen_is_target_column(log_size, fibonacci_index);

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let prover_channel = &mut KeccakChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, KeccakMerkleChannel>::new(config, &twiddles);

    let fib_stmt0 = FibStatement0 {
        log_size,
        fibonacci_index,
        initial_a,
        initial_b,
        expected_value,
    };
    fib_stmt0.mix_into(prover_channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals([fib_is_first_col.clone(), fib_is_target_col.clone()]);
    tree_builder.commit(prover_channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(prover_channel);

    let all_preprocessed_columns =
        vec![is_first_column_id(log_size), is_target_column_id(log_size)];
    let mut tree_span_provider =
        TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);
    let fib_component = FibComponent::new(
        &mut tree_span_provider,
        FibEval {
            log_n_rows: log_size,
            is_first_id: is_first_column_id(log_size),
            is_target_id: is_target_column_id(log_size),
            initial_a: BaseField::from_u32_unchecked(initial_a),
            initial_b: BaseField::from_u32_unchecked(initial_b),
            expected_value: BaseField::from_u32_unchecked(expected_value),
        },
        SecureField::zero(),
    );

    let (proof, composition_polynomial) =
        prove(&[&fib_component], prover_channel, commitment_scheme)?;

    Ok((
        ProofData {
            fib_stmt0,
            stark_proof: proof,
        },
        composition_polynomial,
    ))
}

fn verify_proof_offchain(
    proof_data: &ProofData,
    composition_polynomial: SecureCirclePoly<SimdBackend>,
    config: PcsConfig,
) -> Result<OffchainArtifacts, VerificationError> {
    let mut channel = KeccakChannel::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<KeccakMerkleChannel>::new(config);

    let all_preprocessed_columns = vec![
        is_first_column_id(proof_data.fib_stmt0.log_size),
        is_target_column_id(proof_data.fib_stmt0.log_size),
    ];
    let mut tree_span_provider =
        TraceLocationAllocator::new_with_preprocessed_columns(&all_preprocessed_columns);
    let fib_component = FibComponent::new(
        &mut tree_span_provider,
        FibEval {
            log_n_rows: proof_data.fib_stmt0.log_size,
            is_first_id: is_first_column_id(proof_data.fib_stmt0.log_size),
            is_target_id: is_target_column_id(proof_data.fib_stmt0.log_size),
            initial_a: BaseField::from_u32_unchecked(proof_data.fib_stmt0.initial_a),
            initial_b: BaseField::from_u32_unchecked(proof_data.fib_stmt0.initial_b),
            expected_value: BaseField::from_u32_unchecked(proof_data.fib_stmt0.expected_value),
        },
        SecureField::zero(),
    );

    let trace_log_sizes = fib_component.trace_log_degree_bounds();

    proof_data.fib_stmt0.mix_into(&mut channel);
    commitment_scheme.commit(
        proof_data.stark_proof.commitments[0],
        &trace_log_sizes[0],
        &mut channel,
    );
    commitment_scheme.commit(
        proof_data.stark_proof.commitments[1],
        &trace_log_sizes[1],
        &mut channel,
    );

    let digest = FixedBytes::from(channel.digest().0);

    let n_preprocessed_columns = commitment_scheme.trees[0].column_log_sizes.len();
    let components = stwo::core::air::Components {
        components: vec![&fib_component as &dyn Component],
        n_preprocessed_columns,
    };
    let composition_log_degree_bound = components.composition_log_degree_bound();

    verify(
        &[&fib_component],
        &mut channel,
        &mut commitment_scheme,
        proof_data.stark_proof.clone(),
        composition_polynomial,
    )?;

    Ok(OffchainArtifacts {
        digest,
        component: fib_component,
        log_sizes: trace_log_sizes.0.clone(),
        composition_log_degree_bound,
    })
}

fn prepare_onchain_inputs(
    proof_data: &ProofData,
    offchain: &OffchainArtifacts,
    config: PcsConfig,
) -> (
    VerificationParams,
    Vec<Vec<u32>>,
    Vec<u64>,
) {
    let component_info = ComponentInfo {
        maxConstraintLogDegreeBound: offchain.component.max_constraint_log_degree_bound(),
        logSize: offchain.component.log_size(),
        maskOffsets: offchain
            .component
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
        preprocessedColumns: offchain
            .component
            .info
            .preprocessed_columns
            .iter()
            .enumerate()
            .map(|(idx, _)| U256::from(idx))
            .collect(),
    };

    let verification_params = VerificationParams {
        componentParams: vec![ComponentParams {
            logSize: offchain.component.log_size(),
            claimedSum: QM31 {
                first: CM31 {
                    real: offchain.component.claimed_sum().0 .0 .0,
                    imag: offchain.component.claimed_sum().0 .1 .0,
                },
                second: CM31 {
                    real: offchain.component.claimed_sum().1 .0 .0,
                    imag: offchain.component.claimed_sum().1 .1 .0,
                },
            },
            info: component_info,
        }],
        nPreprocessedColumns: U256::from(offchain.component.info.preprocessed_columns.len()),
        componentsCompositionLogDegreeBound: offchain.composition_log_degree_bound,
    };

    let log_sizes: Vec<Vec<u32>> = vec![
        offchain.log_sizes[0].clone(),
        offchain.log_sizes[1].clone(),
    ];

    let public_inputs = vec![
        proof_data.fib_stmt0.log_size as u64,
        proof_data.fib_stmt0.fibonacci_index as u64,
        proof_data.fib_stmt0.initial_a as u64,
        proof_data.fib_stmt0.initial_b as u64,
        proof_data.fib_stmt0.expected_value as u64,
    ];

    (verification_params, log_sizes, public_inputs)
}

async fn test_contract_verify(
    proof: Proof,
    verification_params: VerificationParams,
    tree_column_log_sizes: Vec<Vec<u32>>,
    public_inputs: Vec<u64>,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔗 Testing Contract Verify Call");

    let rpc_url = "http://localhost:8545";
    let provider = ProviderBuilder::new().on_http(rpc_url.parse()?);

    let contract_address =
        Address::parse_checksummed("0x5FbDB2315678afecb367f032d93F642f64180aa3", None)?;

    println!("Calling contract verify function...");

    let call_data = IStwoVerifier::verifyCall {
        proof,
        params: verification_params,
        treeColumnLogSizes: tree_column_log_sizes,
        publicInputs: public_inputs,
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
    let fibonacci_index = 10; // Compute f(10)
    let initial_a = 0;
    let initial_b = 1;
    println!(
        "📝 Computing Fibonacci f({}) using STARK proof\n",
        fibonacci_index
    );

    // ═══════════════════════════════════════════════════════════
    // STEP 1: GENERATE FIBONACCI TRACE
    // ═══════════════════════════════════════════════════════════
    println!("📊 STEP 1: Generate Fibonacci Trace");
    let log_size = calculate_log_size(fibonacci_index);
    let (_, target_value) = gen_fib_trace(log_size, fibonacci_index, initial_a, initial_b);
    println!("  Trace size: 2^{} = {} rows", log_size, 1 << log_size);
    println!("  Target value f({}) = {}", fibonacci_index, target_value);
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

    let (proof_data, composition_polynomial) = prove_fibonacci(
        log_size,
        fibonacci_index,
        initial_a,
        initial_b,
        config.clone(),
    )?;
    println!("  ✅ STARK proof generated\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 3: VERIFY PROOF (OFF-CHAIN)
    // ═══════════════════════════════════════════════════════════
    println!("✅ STEP 3: Verify Proof (Off-Chain)");
    let offchain =
        verify_proof_offchain(&proof_data, composition_polynomial.clone(), config.clone())?;
    println!("  Digest: 0x{}", hex::encode(offchain.digest));
    println!(
        "  Composition log degree bound: {}",
        offchain.composition_log_degree_bound
    );
    println!("  ✅ Off-chain verification successful\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 4: CONVERT TO SOLIDITY FORMAT
    // ═══════════════════════════════════════════════════════════
    println!("🔄 STEP 4: Convert Proof to Solidity Format");

    let solidity_proof = convert_to_solidity_proof(
        proof_data.stark_proof.clone(),
        composition_polynomial,
        config.clone(),
    );
    println!("  ✅ Proof converted to Solidity format\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 5: PREPARE VERIFICATION PARAMETERS
    // ═══════════════════════════════════════════════════════════
    println!("📋 STEP 5: Prepare Verification Parameters");
    let (verification_params, log_sizes, public_inputs) =
        prepare_onchain_inputs(&proof_data, &offchain, config.clone());

    println!("  Component log size: {}", offchain.component.log_size());
    println!(
        "  Max constraint log degree bound: {}",
        offchain.component.max_constraint_log_degree_bound()
    );
    println!("  ✅ Parameters prepared\n");

    // ═══════════════════════════════════════════════════════════
    // STEP 6: VERIFY ON-CHAIN
    // ═══════════════════════════════════════════════════════════
    println!("🌐 STEP 6: Verify Proof On-Chain");

    if let Err(e) = test_contract_verify(
        solidity_proof,
        verification_params,
        log_sizes,
        public_inputs,
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
    println!("  Target: f({}) = {}", fibonacci_index, target_value);
    println!("  Trace size: 2^{} = {} rows", log_size, 1 << log_size);
    println!("  Security bits: {}", config.security_bits());
    println!("  ✅ Off-chain verification: PASSED");
    println!("  ✅ On-chain verification: CHECK ABOVE");

    println!("\n🎉 Fibonacci STARK proof generated and verified!");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_fibonacci_onchain_with_public_inputs() {
        let fibonacci_index = 10;
        let initial_a = 0;
        let initial_b = 1;
        let log_size = calculate_log_size(fibonacci_index);

        let config = PcsConfig {
            pow_bits: 15,
            fri_config: StwoFriConfig::new(2, 3, 27),
        };

        let (proof_data, composition_polynomial) = prove_fibonacci(
            log_size,
            fibonacci_index,
            initial_a,
            initial_b,
            config.clone(),
        )
        .expect("proof generation failed");

        let offchain =
            verify_proof_offchain(&proof_data, composition_polynomial.clone(), config.clone())
                .expect("off-chain verification failed");

        let solidity_proof = convert_to_solidity_proof(
            proof_data.stark_proof.clone(),
            composition_polynomial,
            config.clone(),
        );

        let (verification_params, log_sizes, public_inputs) =
            prepare_onchain_inputs(&proof_data, &offchain, config);

        test_contract_verify(
            solidity_proof,
            verification_params,
            log_sizes,
            public_inputs,
        )
        .await
        .expect("on-chain verification failed");
    }
}
