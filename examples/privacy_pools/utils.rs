//! Merkle tree verification circuit with LogUp - KKRT Labs style
//!
//! This implementation follows the approach used by KKRT Labs in cairo-m:
//! https://github.com/KKRT-labs/cairo-m
//!
//! # KKRT Key Features
//!
//! - **Node size**: SINGLE M31 value (vs 8 M31 in standard) → 8x smaller proofs
//! - **Hash input**: `[left, right, 0, 0, ..., 0]` (2 values + 14 zeros padding)
//! - **Hash output**: Only `state[0]` after Poseidon2 permutation
//! - **Rows per level**: 1 row (vs 2 in standard sequential absorption)
//! - **Capacity**: Always implicitly 0 (from padding, no capacity management)
//!
//! # Example Usage
//!
//! ```ignore
//! use poseidon_uacias_components_merkle_kkrt::*;
//!
//! // Generate tree and get siblings
//! let tree = generate_merkle_tree(3, 100);  // depth=3, 8 leaves
//! let siblings = tree.get_siblings(5);      // siblings for leaf 5
//!
//! // Prove and verify
//! let (proof, ..) = prove_merkle(
//!     tree.depth,
//!     tree.leaves[5],
//!     siblings,
//!     5,
//!     tree.root,
//!     channel,
//!     commitment_scheme,
//! )?;
//! verify_merkle(proof, tree.depth, statement0, statement1, config)?;
//! ```
//!
//! See README.md for detailed documentation.
//!
//! Architecture:
//! - MerkleComputingComponent: Computes Merkle path from leaf to root using Poseidon hash (yields
//!   computed root via LogUp)
//! - MerkleSchedulerComponent: Verifies computed root equals expected root
//!
//! Based on Poseidon2 hash function from <https://eprint.iacr.org/2023/323.pdf>

use std::ops::{Add, AddAssign, Mul, Sub};

use stwo::core::channel::{KeccakChannel, Channel};
use stwo::core::vcs::keccak_merkle::{KeccakMerkleChannel, KeccakMerkleHasher};
use stwo_constraint_framework::relation;


// pub use computing::{MerkleComputingComponent, MerkleComputingEval};
use num_traits::Zero;
// pub use scheduler::{MerkleSchedulerComponent, MerkleSchedulerEval};
// use stwo::core::channel::{Blake2sChannel, Channel, KeccakChannel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fields::FieldExpOps;
use stwo::core::pcs::TreeVec;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::{CircleEvaluation, SecureCirclePoly};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::CommitmentSchemeProver;
use stwo_polynomial::prove::prove;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;
pub use crate::trace_gen::{
    gen_merkle_computing_interaction_trace, gen_merkle_computing_trace,
    gen_merkle_scheduler_interaction_trace, gen_merkle_scheduler_trace,
    gen_poseidon_computing_interaction_trace, gen_poseidon_computing_trace,
    gen_poseidon_scheduler_interaction_trace, gen_poseidon_scheduler_trace,
};

use crate::computing::{MerkleComputingComponent, MerkleComputingEval};
use crate::scheduler::{MerkleSchedulerComponent, MerkleSchedulerEval};

// Poseidon parameters
pub const N_STATE: usize = 16;
pub const RATE: usize = 8; // First 8 elements absorb message
#[allow(dead_code)]
pub const CAPACITY: usize = 8; // Last 8 elements for security
pub const N_PARTIAL_ROUNDS: usize = 14;
pub const N_HALF_FULL_ROUNDS: usize = 4;
pub const FULL_ROUNDS: usize = 2 * N_HALF_FULL_ROUNDS;
pub const N_COLUMNS: usize = RATE + N_STATE * (1 + FULL_ROUNDS) + N_PARTIAL_ROUNDS + N_STATE;
pub const LOG_EXPAND: u32 = 3; // Start with 0 to avoid extension

// TODO(shahars): Use poseidon's real constants.
pub const EXTERNAL_ROUND_CONSTS: [[BaseField; N_STATE]; 2 * N_HALF_FULL_ROUNDS] =
    [[BaseField::from_u32_unchecked(1234); N_STATE]; 2 * N_HALF_FULL_ROUNDS];
pub const INTERNAL_ROUND_CONSTS: [BaseField; N_PARTIAL_ROUNDS] =
    [BaseField::from_u32_unchecked(1234); N_PARTIAL_ROUNDS];

// LogUp relation for 16-element final_state (used by multi-component Poseidon)
relation!(PoseidonRelation, N_STATE);

// LogUp relation for 1-element Merkle nodes (KKRT style: only state[0])
relation!(MerkleRelation, 1);

#[inline(always)]
/// Applies the M4 MDS matrix described in <https://eprint.iacr.org/2023/323.pdf> 5.1.
pub fn apply_m4<F>(x: [F; 4]) -> [F; 4]
where
    F: Clone + AddAssign<F> + Add<F, Output = F> + Sub<F, Output = F> + Mul<BaseField, Output = F>,
{
    let t0 = x[0].clone() + x[1].clone();
    let t02 = t0.clone() + t0.clone();
    let t1 = x[2].clone() + x[3].clone();
    let t12 = t1.clone() + t1.clone();
    let t2 = x[1].clone() + x[1].clone() + t1.clone();
    let t3 = x[3].clone() + x[3].clone() + t0.clone();
    let t4 = t12.clone() + t12.clone() + t3.clone();
    let t5 = t02.clone() + t02.clone() + t2.clone();
    let t6 = t3.clone() + t5.clone();
    let t7 = t2.clone() + t4.clone();
    [t6, t5, t7, t4]
}

/// Applies the external round matrix.
/// See <https://eprint.iacr.org/2023/323.pdf> 5.1 and Appendix B.
pub fn apply_external_round_matrix<F>(state: &mut [F; 16])
where
    F: Clone + AddAssign<F> + Add<F, Output = F> + Sub<F, Output = F> + Mul<BaseField, Output = F>,
{
    // Applies circ(2M4, M4, M4, M4).
    for i in 0..4 {
        [
            state[4 * i],
            state[4 * i + 1],
            state[4 * i + 2],
            state[4 * i + 3],
        ] = apply_m4([
            state[4 * i].clone(),
            state[4 * i + 1].clone(),
            state[4 * i + 2].clone(),
            state[4 * i + 3].clone(),
        ]);
    }
    for j in 0..4 {
        let s =
            state[j].clone() + state[j + 4].clone() + state[j + 8].clone() + state[j + 12].clone();
        for i in 0..4 {
            state[4 * i + j] += s.clone();
        }
    }
}

// Applies the internal round matrix.
//   mu_i = 2^{i+1} + 1.
// See <https://eprint.iacr.org/2023/323.pdf> 5.2.
pub fn apply_internal_round_matrix<F>(state: &mut [F; 16])
where
    F: Clone + AddAssign<F> + Add<F, Output = F> + Sub<F, Output = F> + Mul<BaseField, Output = F>,
{
    // TODO(shahars): Check that these coefficients are good according to section  5.3 of Poseidon2
    // paper.
    let sum = state[1..]
        .iter()
        .cloned()
        .fold(state[0].clone(), |acc, s| acc + s);
    state.iter_mut().enumerate().for_each(|(i, s)| {
        // TODO(andrew): Change to rotations.
        *s = s.clone() * BaseField::from_u32_unchecked(1 << (i + 1)) + sum.clone();
    });
}

pub fn pow5<F: FieldExpOps>(x: F) -> F {
    let x2 = x.clone() * x.clone();
    let x4 = x2.clone() * x2.clone();
    x4 * x.clone()
}

/// Helper function to compute x^5 for constraint expressions
pub fn pow5_expr<F: Clone + std::ops::Mul<Output = F>>(x: F) -> F {
    let x2 = x.clone() * x.clone();
    let x4 = x2.clone() * x2.clone();
    x4 * x
}

/// Generates the is_first preprocessed column
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

/// Generates the is_active preprocessed column
///
/// Marks which rows are "active" (contain real messages) vs "padding" (unused).
/// Active rows have value 1, padding rows have value 0.
///
/// # Arguments
/// * `log_size` - Log2 of trace size
/// * `n_active` - Number of active rows
///
/// # Returns
/// Column where first `n_active` rows are 1, rest are 0 (in sequential order before bit-reversal)
pub fn gen_is_active_column(
    log_size: u32,
    n_active: usize,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_rows = 1 << log_size;

    assert!(
        n_active <= n_rows,
        "n_active ({}) exceeds n_rows ({}). Use larger log_size.",
        n_active,
        n_rows
    );

    let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);

    // Set first n_active rows to 1
    for i in 0..n_active {
        col.set(i, BaseField::from_u32_unchecked(1));
    }

    bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());

    CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)
}

pub fn is_active_column_id(log_size: u32, n_active: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_active_{}_{}", log_size, n_active),
    }
}

/// Generates the is_target preprocessed column
///
/// Marks which row is the "target" row for LogUp (yields final_state).
/// Only the target row has value 1, all other rows have value 0.
///
/// # Arguments
/// * `log_size` - Log2 of trace size
/// * `n_active` - Number of active rows (target = n_active - 1)
///
/// # Returns
/// Column where only row (n_active - 1) is 1, rest are 0 (in sequential order before bit-reversal)
pub fn gen_is_target_column(
    log_size: u32,
    n_active: usize,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_rows = 1 << log_size;

    assert!(
        n_active > 0 && n_active <= n_rows,
        "n_active ({}) must be in range [1, {}]",
        n_active,
        n_rows
    );

    let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);

    // Set only the target row (last active row) to 1
    let target_row = n_active - 1;
    col.set(target_row, BaseField::from_u32_unchecked(1));

    bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());

    CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)
}

pub fn is_target_column_id(log_size: u32, n_active: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_target_{}_{}", log_size, n_active),
    }
}

/// Generates the is_last preprocessed column (used in Merkle sponge context)
///
/// Marks which row is the "last" active row (for Merkle: the final root computation).
/// In sponge construction, each tree level uses 2 rows, so: n_active_rows = 2*depth
/// Only the last active row has value 1, all other rows have value 0.
///
/// # Arguments
/// * `log_size` - Log2 of trace size
/// * `depth` - Tree depth (number of tree levels)
///
/// # Returns
/// Column where only row (2*depth - 1) is 1, rest are 0 (in sequential order before bit-reversal)
pub fn gen_is_last_column(
    log_size: u32,
    depth: usize,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_active_rows = depth; // KKRT: 1 row per level, not 2
    gen_is_target_column(log_size, n_active_rows)
}

pub fn is_last_column_id(log_size: u32, depth: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_last_{}_{}", log_size, depth),
    }
}

/// Generates the is_level_start preprocessed column
///
/// Marks which rows are the START of a new Merkle level (even rows: 0, 2, 4, ...).
/// These rows should have capacity=0 (fresh sponge for each level).
/// Only active even rows have value 1, all other rows have value 0.
///
/// # Arguments
/// * `log_size` - Log2 of trace size
/// * `depth` - Tree depth (number of tree levels)
///
/// # Returns
/// Column where rows 0, 2, 4, ..., (2*depth-2) are 1, rest are 0
pub fn gen_is_level_start_column(
    log_size: u32,
    depth: usize,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let n_rows = 1 << log_size;
    let n_active_rows = depth; // KKRT: 1 row per level

    let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);

    // KKRT: Every active row is a level start (rows 0, 1, 2, ..., depth-1)
    for row in 0..n_active_rows {
        col.set(row, BaseField::from_u32_unchecked(1));
    }

    bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());

    CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)
}

pub fn is_level_start_column_id(log_size: u32, depth: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("is_level_start_{}_{}", log_size, depth),
    }
}

/// Statement 0 for Merkle verification: Component configuration
/// This is mixed into the channel before drawing the PoseidonRelation
#[derive(Clone, Copy, Debug)]
pub struct MerkleStatement0 {
    pub log_size: u32,
    pub depth: usize, // Tree depth (number of hash computations)
}

impl MerkleStatement0 {
    pub fn mix_into(&self, channel: &mut KeccakChannel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.depth as u64);
    }

    /// Returns log sizes for all trees (preprocessed, main, interaction)
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        // For Merkle (KKRT STYLE): Calculate actual column counts
        // Computing: NO message columns + initial_state (16) +
        //            intermediates (full1: 4*16, partial: 14, full2: 4*16) + final_state (16)
        // = 16 + 64 + 14 + 64 + 16 = 174 columns
        const MERKLE_COMPUTING_N_COLUMNS: usize = N_STATE
            + (N_HALF_FULL_ROUNDS * N_STATE)
            + N_PARTIAL_ROUNDS
            + (N_HALF_FULL_ROUNDS * N_STATE)
            + N_STATE;

        // Scheduler (KKRT): computed_root (1) + expected_root (1) = 2 columns
        const MERKLE_SCHEDULER_N_COLUMNS: usize = 2;

        TreeVec(vec![
            // Tree 0: Preprocessed (4 columns: is_first, is_active, is_level_start, is_last)
            vec![self.log_size; 4],
            // Tree 1: Main traces (Computing + Scheduler)
            vec![self.log_size; MERKLE_COMPUTING_N_COLUMNS + MERKLE_SCHEDULER_N_COLUMNS],
            // Tree 2: Interaction traces (2 components * 4 columns each = 8)
            vec![self.log_size; 8],
        ])
    }
}

/// Statement 1 for Merkle verification: Public inputs and LogUp sums (KKRT STYLE)
/// This is mixed into the channel after drawing PoseidonRelation
#[derive(Clone, Debug)]
pub struct MerkleStatement1 {
    pub expected_root: BaseField, // Public input: the expected Merkle root (single M31 value)
    pub claimed_sum_computing: SecureField,
    pub claimed_sum_scheduler: SecureField,
}

impl MerkleStatement1 {
    pub fn mix_into(&self, channel: &mut KeccakChannel) {
        // Mix expected_root as public input (single value)
        channel.mix_felts(&[SecureField::from(self.expected_root)]);
        // Mix claimed sums
        channel.mix_felts(&[self.claimed_sum_computing, self.claimed_sum_scheduler]);
    }
}

/// Prove Merkle tree membership with LogUp
///
/// This generates a STARK proof that verifies a leaf belongs to a Merkle tree
/// by computing the path from leaf to root and checking it matches the expected root.
///
/// # Arguments
/// * `depth` - Tree depth (number of hash computations)
/// * `leaf` - The leaf value (8 elements)
/// * `siblings` - Sibling nodes for each level (length = depth)
/// * `index` - Leaf position in tree
/// * `expected_root` - Expected Merkle root (public input, 8 elements)
/// * `channel` - Blake2s channel for Fiat-Shamir
/// * `commitment_scheme` - Commitment scheme prover
///
/// # Returns
/// * STARK proof
/// * Computing component
/// * Scheduler component
/// * Statement0 (log_size, depth)
/// * Statement1 (expected_root, claimed_sums)
pub fn prove_merkle(
    depth: usize,
    leaf: BaseField,          // KKRT: Single M31 value
    siblings: Vec<BaseField>, // KKRT: Vec of single M31 values
    index: u32,
    expected_root: BaseField, // KKRT: Single M31 value
    channel: &mut KeccakChannel,
    mut commitment_scheme: CommitmentSchemeProver<SimdBackend, KeccakMerkleChannel>,
) -> Result<
    (
        StarkProof<KeccakMerkleHasher>,
        MerkleComputingComponent,
        MerkleSchedulerComponent,
        MerkleStatement0,
        MerkleStatement1,
        SecureCirclePoly<SimdBackend>
    ),
    Box<dyn std::error::Error>,
> {
    // Step 0: Compute dynamic log_size
    // KKRT construction: each tree level = 1 row, so need depth rows
    let min_rows = depth.max(1);
    let min_log_size = if min_rows <= 1 {
        0
    } else {
        (min_rows - 1).ilog2() + 1 // log2_ceil
    };
    let log_size = min_log_size.max(4); // minimum 16 rows for SIMD (LOG_N_LANES = 4)

    println!("=== Merkle Proof Generation ===");
    println!("Tree depth: {}", depth);
    println!("Leaf index: {}", index);
    println!("Computed log_size: {} ({} rows)\n", log_size, 1 << log_size);

    // Step 1: Generate and commit preprocessed columns
    // Note: In KKRT construction, we have depth active rows (1 row per tree level)
    println!("Step 1: Generating and committing preprocessed columns...");
    let n_active_rows = depth;
    let is_first_col = gen_is_first_column(log_size);
    let is_active_col = gen_is_active_column(log_size, n_active_rows);
    let is_level_start_col = gen_is_level_start_column(log_size, depth);
    let is_last_col = gen_is_last_column(log_size, depth);

    let preprocessed_trace = vec![is_first_col, is_active_col, is_level_start_col, is_last_col];
    println!("Generated 4 preprocessed columns");

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed_trace);
    tree_builder.commit(channel);

    // Mix Statement0 (log_size, depth) into channel
    let statement0 = MerkleStatement0 { log_size, depth };
    statement0.mix_into(channel);

    // Step 2: Generate main traces
    println!("\nStep 2: Generating main traces...");
    let (trace_computing, computed_root) =
        gen_merkle_computing_trace(log_size, depth, leaf, siblings, index);
    let trace_scheduler = gen_merkle_scheduler_trace(log_size, computed_root, expected_root);
    println!("Computing trace: {} rows, depth {}", 1 << log_size, depth);
    println!("Scheduler trace: {} rows", 1 << log_size);
    println!("DEBUG: computed_root = {}", computed_root.0);
    println!("DEBUG: expected_root = {}", expected_root.0);

    // Step 3: Commit main traces
    println!("\nStep 3: Committing main traces...");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals([trace_computing.clone(), trace_scheduler.clone()].concat());
    tree_builder.commit(channel);

    // Step 4: Draw MerkleRelation from channel
    println!("\nStep 4: Drawing LogUp relation from channel...");
    let merkle_relation = MerkleRelation::draw(channel);

    // Step 5: Generate interaction traces (LogUp columns)
    println!("\nStep 5: Generating LogUp interaction traces...");
    let (interaction_trace_computing, claimed_sum_computing) =
        gen_merkle_computing_interaction_trace(&trace_computing, &merkle_relation, log_size, depth);

    let (interaction_trace_scheduler, claimed_sum_scheduler) =
        gen_merkle_scheduler_interaction_trace(&trace_scheduler, &merkle_relation, log_size);

    // Step 6: Verify LogUp property: sum of all claimed_sums should be 0
    let total_sum = claimed_sum_computing + claimed_sum_scheduler;
    println!("\nLogUp verification:");
    println!("  Computing yields: {:?}", claimed_sum_computing);
    println!("  Scheduler uses:   {:?}", claimed_sum_scheduler);
    println!("  Total sum:        {:?}", total_sum);
    if total_sum == Zero::zero() {
        println!("✅ LogUp property satisfied: total sum = 0");
    } else {
        println!("⚠️  Warning: LogUp sum is not zero!");
    }

    // Mix Statement1 (expected_root, claimed_sums) into channel
    let statement1 = MerkleStatement1 {
        expected_root,
        claimed_sum_computing,
        claimed_sum_scheduler,
    };
    statement1.mix_into(channel);

    // Step 7: Commit interaction traces
    println!("\nStep 6: Committing interaction traces...");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals([interaction_trace_computing, interaction_trace_scheduler].concat());
    tree_builder.commit(channel);

    // Step 8: Create components with TraceLocationAllocator
    println!("\nStep 7: Creating components...");
    let mut tree_span_provider = TraceLocationAllocator::default();
    let is_first_id = is_first_column_id(log_size);

    let component_computing = MerkleComputingComponent::new(
        &mut tree_span_provider,
        MerkleComputingEval {
            log_n_rows: log_size,
            depth,
            merkle_relation: merkle_relation.clone(),
            claimed_sum: claimed_sum_computing,
            is_first_id: is_first_id.clone(),
            is_active_id: is_active_column_id(log_size, n_active_rows),
            is_level_start_id: is_level_start_column_id(log_size, depth),
            is_last_id: is_last_column_id(log_size, depth),
        },
        claimed_sum_computing,
    );

    let component_scheduler = MerkleSchedulerComponent::new(
        &mut tree_span_provider,
        MerkleSchedulerEval {
            log_n_rows: log_size,
            merkle_relation,
            claimed_sum: claimed_sum_scheduler,
            is_first_id: is_first_id.clone(),
        },
        claimed_sum_scheduler,
    );

    // Step 9: Generate proof
    println!("\nStep 8: Generating STARK proof...");
    let (proof, composition_polynomial) = prove(
        &[&component_computing, &component_scheduler],
        channel,
        commitment_scheme,
    )?;
    println!("✅ Proof generated successfully!");

    Ok((
        proof,
        component_computing,
        component_scheduler,
        statement0,
        statement1,
        composition_polynomial,
    ))
}

/// Verify Merkle proof with LogUp
///
/// This verifies a STARK proof for Merkle tree membership.
/// The verifier must commit to the same tree structure as the prover.
///
/// # Arguments
/// * `proof` - The STARK proof
/// * `depth` - Tree depth
/// * `statement0` - Statement0 (log_size, depth)
/// * `statement1` - Statement1 (expected_root, claimed_sums)
/// * `config` - PCS configuration
///
/// # Returns
/// * Result indicating success or failure
pub fn verify_merkle(
    proof: StarkProof<KeccakMerkleHasher>,
    depth: usize,
    statement0: MerkleStatement0,
    statement1: MerkleStatement1,
    config: stwo::core::pcs::PcsConfig,
    composition_polynomial: SecureCirclePoly<SimdBackend>,
) -> Result<(), Box<dyn std::error::Error>> {
    use stwo::core::pcs::CommitmentSchemeVerifier;

    println!("\n=== Merkle Proof Verification ===");
    println!("Tree depth: {}\n", depth);

    // Extract log_size from statement
    let log_size = statement0.log_size;

    // Step 1: Setup verifier channel and commitment scheme
    println!("Step 1: Setting up verifier...");
    let channel = &mut KeccakChannel::default();
    let commitment_scheme = &mut CommitmentSchemeVerifier::<KeccakMerkleChannel>::new(config);
    let log_sizes = statement0.log_sizes();

    // Step 2: Commit preprocessed columns
    println!("\nStep 2: Committing preprocessed columns...");
    commitment_scheme.commit(proof.commitments[0], &log_sizes[0], channel);

    // Mix Statement0 (log_size, depth) into channel
    statement0.mix_into(channel);

    // Step 3: Commit main traces
    println!("\nStep 3: Committing main traces...");
    commitment_scheme.commit(proof.commitments[1], &log_sizes[1], channel);

    // Step 4: Draw MerkleRelation from channel (must match prover)
    println!("\nStep 4: Drawing LogUp relation from channel...");
    let merkle_relation = MerkleRelation::draw(channel);

    // Mix Statement1 (expected_root, claimed_sums) into channel
    statement1.mix_into(channel);

    // Step 5: Commit interaction traces
    println!("\nStep 5: Committing interaction traces...");
    commitment_scheme.commit(proof.commitments[2], &log_sizes[2], channel);

    // Step 6: Create components (AFTER committing interaction traces, matching prover order)
    println!("\nStep 6: Creating components for verification...");
    let mut tree_span_provider = TraceLocationAllocator::default();
    let is_first_id = is_first_column_id(log_size);

    let component_computing = MerkleComputingComponent::new(
        &mut tree_span_provider,
        MerkleComputingEval {
            log_n_rows: log_size,
            depth,
            merkle_relation: merkle_relation.clone(),
            claimed_sum: statement1.claimed_sum_computing,
            is_first_id: is_first_id.clone(),
            is_active_id: is_active_column_id(log_size, depth), // KKRT: depth active rows
            is_level_start_id: is_level_start_column_id(log_size, depth),
            is_last_id: is_last_column_id(log_size, depth),
        },
        statement1.claimed_sum_computing,
    );

    let component_scheduler = MerkleSchedulerComponent::new(
        &mut tree_span_provider,
        MerkleSchedulerEval {
            log_n_rows: log_size,
            merkle_relation,
            claimed_sum: statement1.claimed_sum_scheduler,
            is_first_id: is_first_id.clone(),
        },
        statement1.claimed_sum_scheduler,
    );

    // Step 7: Verify the proof
    println!("\nStep 7: Verifying STARK proof...");
    stwo_polynomial::verify::verify(
        &[&component_computing, &component_scheduler],
        channel,
        commitment_scheme,
        proof,
        composition_polynomial,
    )?;
    println!("✅ Proof verified successfully!");

    Ok(())
}

/// Helper structure to represent a complete Merkle tree
pub struct MerkleTree {
    pub depth: usize,
    pub leaves: Vec<BaseField>,
    pub levels: Vec<Vec<BaseField>>, // levels[0] = leaves, levels[depth] = root
    pub root: BaseField,
}

impl MerkleTree {
    /// Get siblings for a given leaf index
    pub fn get_siblings(&self, leaf_index: usize) -> Vec<BaseField> {
        let mut siblings = Vec::new();
        let mut current_index = leaf_index;

        for level in 0..self.depth {
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };
            siblings.push(self.levels[level][sibling_index]);
            current_index /= 2;
        }

        siblings
    }

    /// Verify that a leaf at given index produces the correct root
    pub fn verify_path(&self, leaf_index: usize) -> bool {
        let siblings = self.get_siblings(leaf_index);
        let mut current = self.leaves[leaf_index];
        let mut index = leaf_index;

        for sibling in siblings {
            let (left, right) = if index % 2 == 0 {
                (current, sibling)
            } else {
                (sibling, current)
            };
            current = hash_two_nodes_kkrt(left, right);
            index /= 2;
        }

        current == self.root
    }
}

/// Generate a complete Merkle tree of given depth with sequential leaf values
///
/// # Arguments
/// * `depth` - Tree depth (number of levels, including root)
/// * `start_value` - Starting value for leaves (leaves will be start_value, start_value+10, start_value+20, ...)
///
/// # Returns
/// Complete MerkleTree structure with all nodes computed
///
/// # Example
/// ```ignore
/// let tree = generate_merkle_tree(3, 100); // depth 3, 8 leaves starting at 100
/// assert_eq!(tree.leaves.len(), 8);
/// assert_eq!(tree.depth, 3);
/// ```
pub fn generate_merkle_tree(depth: usize, start_value: u32) -> MerkleTree {
    let n_leaves = 1 << depth; // 2^depth leaves

    // Generate leaves with sequential values
    let leaves: Vec<BaseField> = (0..n_leaves)
        .map(|i| BaseField::from_u32_unchecked(start_value + (i as u32) * 10))
        .collect();

    // Build tree level by level
    let mut levels = vec![leaves.clone()];

    for level in 0..depth {
        let current_level = &levels[level];
        let mut next_level = Vec::new();

        for i in 0..(current_level.len() / 2) {
            let left = current_level[i * 2];
            let right = current_level[i * 2 + 1];
            let parent = hash_two_nodes_kkrt(left, right);
            next_level.push(parent);
        }

        levels.push(next_level);
    }

    let root = levels[depth][0];

    MerkleTree {
        depth,
        leaves,
        levels,
        root,
    }
}

// Helper function for all tests: KKRT-style hash (single permutation)
pub fn hash_two_nodes_kkrt(left: BaseField, right: BaseField) -> BaseField {
    // Build initial state: [left, right, 0, 0, ..., 0]
    let mut state: [BaseField; N_STATE] = [BaseField::from_u32_unchecked(0); N_STATE];
    state[0] = left;
    state[1] = right;
    // Elements 2-15 are already zeros (implicit capacity = 0)

    // Single Poseidon2 permutation
    for round in 0..N_HALF_FULL_ROUNDS {
        for i in 0..N_STATE {
            state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
        }
        apply_external_round_matrix(&mut state);
        state = std::array::from_fn(|i| pow5(state[i]));
    }

    for round in 0..N_PARTIAL_ROUNDS {
        state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
        apply_internal_round_matrix(&mut state);
        state[0] = pow5(state[0]);
    }

    for round in 0..N_HALF_FULL_ROUNDS {
        for i in 0..N_STATE {
            state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
        }
        apply_external_round_matrix(&mut state);
        state = std::array::from_fn(|i| pow5(state[i]));
    }

    // Return ONLY state[0] (KKRT style)
    state[0]
}

// #[cfg(test)]
// mod tests {
//     use stwo::core::channel::Blake2sChannel;
//     use stwo::core::pcs::PcsConfig;
//     use stwo::core::poly::circle::CanonicCoset;
//     use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
//     use stwo::prover::backend::simd::SimdBackend;
//     use stwo::prover::poly::circle::PolyOps;
//     use stwo::prover::CommitmentSchemeProver;

//     use super::*;

//     #[test]
//     #[ignore] // Old test - not updated for KKRT style yet
//     #[cfg(any())] // Disabled - old array-based tests not compatible with KKRT
//     fn test_merkle_proof() {
//         println!("\n==================================================");
//         println!("  MERKLE TREE VERIFICATION PROOF TEST");
//         println!("==================================================\n");

//         // Build a simple Merkle tree of depth 3 (8 leaves)
//         let depth = 3;
//         let leaf_index = 5; // Verify leaf at index 5

//         // Create leaf value (KKRT: single M31)
//         let leaf: BaseField = BaseField::from_u32_unchecked(100);

//         // Build a full tree with 8 leaves (KKRT: each leaf is single M31)
//         let mut leaves: Vec<BaseField> = (0..8)
//             .map(|i| BaseField::from_u32_unchecked(i * 10))
//             .collect();

//         // Our target leaf
//         leaves[leaf_index] = leaf;

//         // Compute siblings for the path from leaf_index to root
//         let mut siblings = Vec::new();
//         let mut current_index = leaf_index;

//         // Level 0: leaves (8 leaves)
//         let level0 = leaves.clone();
//         let sibling0_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level0[sibling0_index]);
//         let _parent0 = if current_index % 2 == 0 {
//             hash_two_nodes_kkrt(level0[current_index], level0[sibling0_index])
//         } else {
//             hash_two_nodes_kkrt(level0[sibling0_index], level0[current_index])
//         };
//         current_index /= 2;

//         // Level 1: 4 nodes
//         let mut level1 = Vec::new();
//         for i in 0..4 {
//             let left = level0[i * 2];
//             let right = level0[i * 2 + 1];
//             level1.push(hash_two_nodes_kkrt(left, right));
//         }
//         let sibling1_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level1[sibling1_index]);
//         let _parent1 = if current_index % 2 == 0 {
//             hash_two_nodes_kkrt(level1[current_index], level1[sibling1_index])
//         } else {
//             hash_two_nodes_kkrt(level1[sibling1_index], level1[current_index])
//         };
//         current_index /= 2;

//         // Level 2: 2 nodes
//         let mut level2 = Vec::new();
//         for i in 0..2 {
//             let left = level1[i * 2];
//             let right = level1[i * 2 + 1];
//             level2.push(hash_two_nodes_kkrt(left, right));
//         }
//         let sibling2_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level2[sibling2_index]);

//         // Root (KKRT: single M31 value)
//         let expected_root = hash_two_nodes_kkrt(level2[0], level2[1]);

//         println!("Built Merkle tree (KKRT style):");
//         println!("  Depth: {}", depth);
//         println!("  Leaf index: {}", leaf_index);
//         println!("  Leaf: {}", leaf.0);
//         println!("  Expected root: {}", expected_root.0);

//         // Setup prover
//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme_prover =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         // Generate proof
//         println!("\n--- Proving ---");
//         let (proof, _component_computing, _component_scheduler, statement0, statement1) =
//             prove_merkle(
//                 depth,
//                 leaf,
//                 siblings,
//                 leaf_index as u32,
//                 expected_root,
//                 channel,
//                 commitment_scheme_prover,
//             )
//             .expect("Proof generation failed");

//         println!("\n--- Verifying ---");
//         verify_merkle(proof, depth, statement0, statement1, config).expect("Verification failed");

//         println!("\n==================================================");
//         println!("  ✅ MERKLE PROOF TEST PASSED!");
//         println!("==================================================\n");
//     }

//     #[ignore]
//     #[cfg(any())] // Disabled - old array-based tests not compatible with KKRT
//     #[test]
//     fn test_merkle_proof_simple_value() {
//         println!("\n==================================================");
//         println!("  MERKLE PROOF WITH SIMPLE VALUE (123)");
//         println!("==================================================\n");

//         // Build a simple Merkle tree of depth 2 (4 leaves)
//         let depth = 2;
//         let leaf_index = 2;

//         // Create leaf with simple value 123 in first element, rest is padding
//         let mut leaf = [BaseField::from_u32_unchecked(0); RATE];
//         leaf[0] = BaseField::from_u32_unchecked(123);

//         println!("Leaf with value 123 (and padding):");
//         println!("  {:?}", &leaf);

//         // Helper function (same as before)
//         fn hash_two_nodes(left: [BaseField; RATE], right: [BaseField; RATE]) -> [BaseField; RATE] {
//             use super::{
//                 apply_external_round_matrix, apply_internal_round_matrix, pow5,
//                 EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS,
//             };

//             let mut state: [BaseField; N_STATE] = [BaseField::from_u32_unchecked(0); N_STATE];
//             state[0..RATE].copy_from_slice(&left);

//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }

//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }

//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }

//             let output1 = state;

//             for i in 0..RATE {
//                 state[i] = output1[i] + right[i];
//             }
//             for i in RATE..N_STATE {
//                 state[i] = output1[i];
//             }

//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }

//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }

//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }

//             let mut result = [BaseField::from_u32_unchecked(0); RATE];
//             result.copy_from_slice(&state[0..RATE]);
//             result
//         }

//         // Build tree with 4 leaves
//         let mut leaves: Vec<[BaseField; RATE]> = vec![
//             [BaseField::from_u32_unchecked(0); RATE], // leaf 0
//             [BaseField::from_u32_unchecked(0); RATE], // leaf 1
//             [BaseField::from_u32_unchecked(0); RATE], // leaf 2 (will be our target)
//             [BaseField::from_u32_unchecked(0); RATE], // leaf 3
//         ];

//         // Set some distinguishable values for other leaves
//         leaves[0][0] = BaseField::from_u32_unchecked(10);
//         leaves[1][0] = BaseField::from_u32_unchecked(20);
//         leaves[3][0] = BaseField::from_u32_unchecked(30);

//         // Our target leaf with value 123
//         leaves[leaf_index] = leaf;

//         // Compute siblings
//         let mut siblings = Vec::new();
//         let mut current_index = leaf_index;

//         // Level 0
//         let level0 = leaves.clone();
//         let sibling0_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level0[sibling0_index]);
//         current_index /= 2;

//         // Level 1
//         let mut level1 = Vec::new();
//         for i in 0..2 {
//             let left = level0[i * 2];
//             let right = level0[i * 2 + 1];
//             level1.push(hash_two_nodes(left, right));
//         }
//         let sibling1_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level1[sibling1_index]);

//         // Root
//         let expected_root = hash_two_nodes(level1[0], level1[1]);

//         println!("\nBuilt Merkle tree:");
//         println!("  Depth: {}", depth);
//         println!("  Leaf index: {}", leaf_index);
//         println!("  Leaf value: {} (with padding zeros)", leaf[0]);
//         println!("  Expected root: {:?}", &expected_root[0..2]);

//         // Setup prover
//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme_prover =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         // Generate proof
//         println!("\n--- Proving that leaf with value 123 is in tree ---");
//         let (proof, _component_computing, _component_scheduler, statement0, statement1) =
//             prove_merkle(
//                 depth,
//                 leaf,
//                 siblings,
//                 leaf_index as u32,
//                 expected_root,
//                 channel,
//                 commitment_scheme_prover,
//             )
//             .expect("Proof generation failed");

//         println!("\n--- Verifying ---");
//         verify_merkle(proof, depth, statement0, statement1, config).expect("Verification failed");

//         println!("\n==================================================");
//         println!("  ✅ SIMPLE VALUE TEST PASSED!");
//         println!("  Proved that value 123 is at index {} in tree", leaf_index);
//         println!("==================================================\n");
//     }

//     #[test]
//     #[ignore]
//     #[cfg(any())] // Disabled - old array-based tests not compatible with KKRT
//     fn test_merkle_proof_two_values() {
//         println!("\n==================================================");
//         println!("  MERKLE PROOF WITH TWO VALUES (123, 456)");
//         println!("==================================================\n");

//         let depth = 2;
//         let leaf_index = 1;

//         // Create leaf with TWO values: user_id=123, balance=456
//         let mut leaf = [BaseField::from_u32_unchecked(0); RATE];
//         leaf[0] = BaseField::from_u32_unchecked(123); // user_id
//         leaf[1] = BaseField::from_u32_unchecked(456); // balance

//         println!("Leaf with user_id=123, balance=456:");
//         println!("  {:?}", &leaf);

//         // Use same helper function
//         fn hash_two_nodes(left: [BaseField; RATE], right: [BaseField; RATE]) -> [BaseField; RATE] {
//             use super::{
//                 apply_external_round_matrix, apply_internal_round_matrix, pow5,
//                 EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS,
//             };
//             let mut state: [BaseField; N_STATE] = [BaseField::from_u32_unchecked(0); N_STATE];
//             state[0..RATE].copy_from_slice(&left);
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let output1 = state;
//             for i in 0..RATE {
//                 state[i] = output1[i] + right[i];
//             }
//             for i in RATE..N_STATE {
//                 state[i] = output1[i];
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let mut result = [BaseField::from_u32_unchecked(0); RATE];
//             result.copy_from_slice(&state[0..RATE]);
//             result
//         }

//         let mut leaves: Vec<[BaseField; RATE]> = vec![
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//         ];
//         leaves[0][0] = BaseField::from_u32_unchecked(10);
//         leaves[2][0] = BaseField::from_u32_unchecked(20);
//         leaves[3][0] = BaseField::from_u32_unchecked(30);
//         leaves[leaf_index] = leaf;

//         let mut siblings = Vec::new();
//         let mut current_index = leaf_index;
//         let level0 = leaves.clone();
//         let sibling0_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level0[sibling0_index]);
//         current_index /= 2;
//         let mut level1 = Vec::new();
//         for i in 0..2 {
//             level1.push(hash_two_nodes(level0[i * 2], level0[i * 2 + 1]));
//         }
//         let sibling1_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level1[sibling1_index]);
//         let expected_root = hash_two_nodes(level1[0], level1[1]);

//         println!(
//             "\nProving leaf contains user_id={}, balance={}",
//             leaf[0], leaf[1]
//         );

//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme_prover =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         let (proof, _, _, statement0, statement1) = prove_merkle(
//             depth,
//             leaf,
//             siblings,
//             leaf_index as u32,
//             expected_root,
//             channel,
//             commitment_scheme_prover,
//         )
//         .expect("Proof generation failed");

//         verify_merkle(proof, depth, statement0, statement1, config).expect("Verification failed");

//         println!("\n==================================================");
//         println!("  ✅ TWO VALUES TEST PASSED!");
//         println!("==================================================\n");
//     }

//     #[test]
//     #[ignore]
//     #[cfg(any())] // Disabled - old array-based tests not compatible with KKRT
//     fn test_merkle_proof_four_values() {
//         println!("\n==================================================");
//         println!("  MERKLE PROOF WITH FOUR VALUES");
//         println!("==================================================\n");

//         let depth = 2;
//         let leaf_index = 3;

//         // Create leaf with FOUR values: id, balance, timestamp, status
//         let mut leaf = [BaseField::from_u32_unchecked(0); RATE];
//         leaf[0] = BaseField::from_u32_unchecked(1001); // user_id
//         leaf[1] = BaseField::from_u32_unchecked(50000); // balance
//         leaf[2] = BaseField::from_u32_unchecked(1704067200); // timestamp (example)
//         leaf[3] = BaseField::from_u32_unchecked(1); // status (active=1)

//         println!("Leaf with 4 values:");
//         println!("  user_id:   {}", leaf[0]);
//         println!("  balance:   {}", leaf[1]);
//         println!("  timestamp: {}", leaf[2]);
//         println!("  status:    {}", leaf[3]);
//         println!("  Full leaf: {:?}", &leaf);

//         fn hash_two_nodes(left: [BaseField; RATE], right: [BaseField; RATE]) -> [BaseField; RATE] {
//             use super::{
//                 apply_external_round_matrix, apply_internal_round_matrix, pow5,
//                 EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS,
//             };
//             let mut state: [BaseField; N_STATE] = [BaseField::from_u32_unchecked(0); N_STATE];
//             state[0..RATE].copy_from_slice(&left);
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let output1 = state;
//             for i in 0..RATE {
//                 state[i] = output1[i] + right[i];
//             }
//             for i in RATE..N_STATE {
//                 state[i] = output1[i];
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let mut result = [BaseField::from_u32_unchecked(0); RATE];
//             result.copy_from_slice(&state[0..RATE]);
//             result
//         }

//         let mut leaves: Vec<[BaseField; RATE]> = vec![
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//         ];
//         leaves[leaf_index] = leaf;

//         let mut siblings = Vec::new();
//         let mut current_index = leaf_index;
//         let level0 = leaves.clone();
//         let sibling0_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level0[sibling0_index]);
//         current_index /= 2;
//         let mut level1 = Vec::new();
//         for i in 0..2 {
//             level1.push(hash_two_nodes(level0[i * 2], level0[i * 2 + 1]));
//         }
//         let sibling1_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level1[sibling1_index]);
//         let expected_root = hash_two_nodes(level1[0], level1[1]);

//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme_prover =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         let (proof, _, _, statement0, statement1) = prove_merkle(
//             depth,
//             leaf,
//             siblings,
//             leaf_index as u32,
//             expected_root,
//             channel,
//             commitment_scheme_prover,
//         )
//         .expect("Proof generation failed");

//         verify_merkle(proof, depth, statement0, statement1, config).expect("Verification failed");

//         println!("\n==================================================");
//         println!("  ✅ FOUR VALUES TEST PASSED!");
//         println!("==================================================\n");
//     }

//     #[test]
//     #[ignore]
//     #[cfg(any())] // Disabled - old array-based tests not compatible with KKRT
//     fn test_merkle_proof_eight_values() {
//         println!("\n==================================================");
//         println!("  MERKLE PROOF WITH EIGHT VALUES (FULL RATE)");
//         println!("==================================================\n");

//         let depth = 2;
//         let leaf_index = 0;

//         // Create leaf with ALL EIGHT values - full utilization!
//         let leaf: [BaseField; RATE] = [
//             BaseField::from_u32_unchecked(2001),       // user_id
//             BaseField::from_u32_unchecked(100000),     // balance
//             BaseField::from_u32_unchecked(1704067200), // timestamp
//             BaseField::from_u32_unchecked(2),          // status
//             BaseField::from_u32_unchecked(5),          // role
//             BaseField::from_u32_unchecked(1234567),    // nonce
//             BaseField::from_u32_unchecked(999),        // score
//             BaseField::from_u32_unchecked(42),         // metadata
//         ];

//         println!("Leaf with ALL 8 values (full RATE utilization):");
//         println!("  [0] user_id:   {}", leaf[0]);
//         println!("  [1] balance:   {}", leaf[1]);
//         println!("  [2] timestamp: {}", leaf[2]);
//         println!("  [3] status:    {}", leaf[3]);
//         println!("  [4] role:      {}", leaf[4]);
//         println!("  [5] nonce:     {}", leaf[5]);
//         println!("  [6] score:     {}", leaf[6]);
//         println!("  [7] metadata:  {}", leaf[7]);
//         println!("  Full: {:?}", &leaf);

//         fn hash_two_nodes(left: [BaseField; RATE], right: [BaseField; RATE]) -> [BaseField; RATE] {
//             use super::{
//                 apply_external_round_matrix, apply_internal_round_matrix, pow5,
//                 EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS,
//             };
//             let mut state: [BaseField; N_STATE] = [BaseField::from_u32_unchecked(0); N_STATE];
//             state[0..RATE].copy_from_slice(&left);
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let output1 = state;
//             for i in 0..RATE {
//                 state[i] = output1[i] + right[i];
//             }
//             for i in RATE..N_STATE {
//                 state[i] = output1[i];
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let mut result = [BaseField::from_u32_unchecked(0); RATE];
//             result.copy_from_slice(&state[0..RATE]);
//             result
//         }

//         let mut leaves: Vec<[BaseField; RATE]> = vec![
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//             [BaseField::from_u32_unchecked(0); RATE],
//         ];
//         leaves[leaf_index] = leaf;

//         let mut siblings = Vec::new();
//         let mut current_index = leaf_index;
//         let level0 = leaves.clone();
//         let sibling0_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level0[sibling0_index]);
//         current_index /= 2;
//         let mut level1 = Vec::new();
//         for i in 0..2 {
//             level1.push(hash_two_nodes(level0[i * 2], level0[i * 2 + 1]));
//         }
//         let sibling1_index = if current_index % 2 == 0 {
//             current_index + 1
//         } else {
//             current_index - 1
//         };
//         siblings.push(level1[sibling1_index]);
//         let expected_root = hash_two_nodes(level1[0], level1[1]);

//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme_prover =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         let (proof, _, _, statement0, statement1) = prove_merkle(
//             depth,
//             leaf,
//             siblings,
//             leaf_index as u32,
//             expected_root,
//             channel,
//             commitment_scheme_prover,
//         )
//         .expect("Proof generation failed");

//         verify_merkle(proof, depth, statement0, statement1, config).expect("Verification failed");

//         println!("\n==================================================");
//         println!("  ✅ EIGHT VALUES TEST PASSED!");
//         println!("  Successfully proved leaf with FULL rate utilization");
//         println!("==================================================\n");
//     }

//     #[test]
//     #[ignore]
//     #[cfg(any())] // Disabled - old array-based tests not compatible with KKRT
//     fn test_merkle_detailed_simulation() {
//         println!("\n==================================================");
//         println!("  MERKLE DETAILED SIMULATION - STEP BY STEP");
//         println!("==================================================\n");

//         // Simple tree: depth=2, 4 leaves
//         let depth = 2;
//         let leaf_index = 2; // L2

//         println!("📋 STEP 1: Define leaves");
//         println!("========================");

//         let l0 = {
//             let mut l = [BaseField::from_u32_unchecked(0); RATE];
//             l[0] = BaseField::from_u32_unchecked(10);
//             l
//         };
//         let l1 = {
//             let mut l = [BaseField::from_u32_unchecked(0); RATE];
//             l[0] = BaseField::from_u32_unchecked(20);
//             l
//         };
//         let l2 = {
//             let mut l = [BaseField::from_u32_unchecked(0); RATE];
//             l[0] = BaseField::from_u32_unchecked(30);
//             l
//         };
//         let l3 = {
//             let mut l = [BaseField::from_u32_unchecked(0); RATE];
//             l[0] = BaseField::from_u32_unchecked(40);
//             l
//         };

//         println!("L0 = [{}, 0, 0, ...]", l0[0]);
//         println!("L1 = [{}, 0, 0, ...]", l1[0]);
//         println!(
//             "L2 = [{}, 0, 0, ...] ← TARGET (index={})",
//             l2[0], leaf_index
//         );
//         println!("L3 = [{}, 0, 0, ...]", l3[0]);

//         println!("\n📋 STEP 2: Build tree (hash all pairs)");
//         println!("========================================");

//         fn hash_two_nodes(left: [BaseField; RATE], right: [BaseField; RATE]) -> [BaseField; RATE] {
//             use super::{
//                 apply_external_round_matrix, apply_internal_round_matrix, pow5,
//                 EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS,
//             };
//             let mut state: [BaseField; N_STATE] = [BaseField::from_u32_unchecked(0); N_STATE];
//             state[0..RATE].copy_from_slice(&left);
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let output1 = state;
//             for i in 0..RATE {
//                 state[i] = output1[i] + right[i];
//             }
//             for i in RATE..N_STATE {
//                 state[i] = output1[i];
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             for round in 0..N_PARTIAL_ROUNDS {
//                 state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
//                 apply_internal_round_matrix(&mut state);
//                 state[0] = pow5(state[0]);
//             }
//             for round in 0..N_HALF_FULL_ROUNDS {
//                 for i in 0..N_STATE {
//                     state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
//                 }
//                 apply_external_round_matrix(&mut state);
//                 state = std::array::from_fn(|i| pow5(state[i]));
//             }
//             let mut result = [BaseField::from_u32_unchecked(0); RATE];
//             result.copy_from_slice(&state[0..RATE]);
//             result
//         }

//         // Level 0 → Level 1
//         let h01 = hash_two_nodes(l0, l1);
//         let h23 = hash_two_nodes(l2, l3);

//         println!("Level 1:");
//         println!("  H01 = hash(L0, L1) = [{}, {}, ...]", h01[0], h01[1]);
//         println!("  H23 = hash(L2, L3) = [{}, {}, ...]", h23[0], h23[1]);

//         // Level 1 → Root
//         let root = hash_two_nodes(h01, h23);

//         println!("\nRoot:");
//         println!("  ROOT = hash(H01, H23) = [{}, {}, ...]", root[0], root[1]);

//         println!("\n📋 STEP 3: Collect siblings for path from L2 to ROOT");
//         println!("======================================================");

//         // For index=2 (binary 10):
//         // Level 0: sibling is L3
//         // Level 1: sibling is H01

//         let siblings = vec![l3, h01];

//         println!("Path from L2 (index={}, binary=10):", leaf_index);
//         println!("  Level 0: L2 with sibling L3 → H23");
//         println!("    siblings[0] = L3 = [{}, ...]", siblings[0][0]);
//         println!("  Level 1: H23 with sibling H01 → ROOT");
//         println!(
//             "    siblings[1] = H01 = [{}, {}, ...]",
//             siblings[1][0], siblings[1][1]
//         );

//         println!("\n📋 STEP 4: Generate STARK proof");
//         println!("================================");

//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme_prover =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         println!("Generating proof that L2 belongs to tree...");
//         let (proof, _, _, statement0, statement1) = prove_merkle(
//             depth,
//             l2,
//             siblings,
//             leaf_index as u32,
//             root,
//             channel,
//             commitment_scheme_prover,
//         )
//         .expect("Proof generation failed");

//         println!("\n📋 STEP 5: Verify proof");
//         println!("========================");

//         verify_merkle(proof, depth, statement0, statement1, config).expect("Verification failed");

//         println!("\n==================================================");
//         println!("  ✅ SIMULATION COMPLETE!");
//         println!("  Successfully proved L2 (value=30) belongs to tree");
//         println!("  with root = [{}, {}, ...]", root[0], root[1]);
//         println!("==================================================\n");

//         println!("💡 Key points:");
//         println!("  • Tree has 4 leaves: L0(10), L1(20), L2(30), L3(40)");
//         println!("  • We proved L2 at index=2 without revealing:");
//         println!("    ❌ The value 30 (private)");
//         println!("    ❌ The index 2 (private)");
//         println!("    ❌ The siblings (private)");
//         println!("  • Verifier only knows ROOT and accepts the proof!");
//         println!("  • This is ZERO-KNOWLEDGE! 🎉\n");
//     }

//     #[test]
//     fn test_kkrt_simple() {
//         println!("\n=== KKRT Simple Merkle Test (Depth 2) ===\n");

//         // Generate a depth-2 tree with 4 leaves
//         let tree = generate_merkle_tree(2, 10);
//         let leaf_index = 2;

//         println!("Generated tree with {} leaves", tree.leaves.len());
//         println!(
//             "Leaves: {}",
//             tree.leaves
//                 .iter()
//                 .map(|l| l.0.to_string())
//                 .collect::<Vec<_>>()
//                 .join(", ")
//         );
//         println!("Root: {}", tree.root.0);

//         // Get siblings for proving leaf at index 2
//         let siblings = tree.get_siblings(leaf_index);
//         println!(
//             "Siblings for leaf {}: {}",
//             leaf_index,
//             siblings
//                 .iter()
//                 .map(|s| s.0.to_string())
//                 .collect::<Vec<_>>()
//                 .join(", ")
//         );

//         // Verify the path locally first
//         assert!(
//             tree.verify_path(leaf_index),
//             "Local path verification failed"
//         );

//         // Setup
//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         // Prove!
//         println!("\nGenerating STARK proof...");
//         let result = prove_merkle(
//             tree.depth,
//             tree.leaves[leaf_index],
//             siblings,
//             leaf_index as u32,
//             tree.root,
//             channel,
//             commitment_scheme,
//         );

//         match result {
//             Ok((proof, _, _, statement0, statement1)) => {
//                 println!("✅ Proof generated successfully!");
//                 println!("   Proof has {} queried values", proof.queried_values.len());

//                 // Verify the proof
//                 println!("\nVerifying STARK proof...");
//                 verify_merkle(proof, tree.depth, statement0, statement1, config)
//                     .expect("Verification failed");

//                 println!("✅ Proof verified successfully!");
//                 println!("\n🎉 KKRT Merkle proof works end-to-end! (Depth {})", tree.depth);
//             }
//             Err(e) => {
//                 panic!("❌ Proof generation failed: {}", e);
//             }
//         }
//     }

//     #[test]
//     fn test_kkrt_depth_3() {
//         println!("\n=== KKRT Merkle Test (Depth 3, 8 leaves) ===\n");

//         // Generate a depth-3 tree with 8 leaves
//         let tree = generate_merkle_tree(3, 100);
//         let leaf_index = 5;

//         println!("Tree depth: {}, leaves: {}", tree.depth, tree.leaves.len());
//         println!("Testing leaf at index: {}", leaf_index);
//         println!("Leaf value: {}", tree.leaves[leaf_index].0);
//         println!("Root: {}", tree.root.0);

//         // Get siblings and verify locally
//         let siblings = tree.get_siblings(leaf_index);
//         assert!(tree.verify_path(leaf_index), "Local verification failed");

//         // Setup and prove
//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         println!("\nGenerating STARK proof...");
//         let (proof, _, _, statement0, statement1) = prove_merkle(
//             tree.depth,
//             tree.leaves[leaf_index],
//             siblings,
//             leaf_index as u32,
//             tree.root,
//             channel,
//             commitment_scheme,
//         )
//         .expect("Proof generation failed");

//         println!("✅ Proof generated!");

//         // Verify
//         println!("Verifying STARK proof...");
//         verify_merkle(proof, tree.depth, statement0, statement1, config)
//             .expect("Verification failed");

//         println!("✅ Verified successfully! (Depth 3) 🎉");
//     }

//     #[test]
//     fn test_kkrt_depth_4() {
//         println!("\n=== KKRT Merkle Test (Depth 4, 16 leaves) ===\n");

//         // Generate a depth-4 tree with 16 leaves
//         let tree = generate_merkle_tree(4, 1000);
//         let leaf_index = 10;

//         println!("Tree depth: {}, leaves: {}", tree.depth, tree.leaves.len());
//         println!("Testing leaf at index: {}", leaf_index);
//         println!("Leaf value: {}", tree.leaves[leaf_index].0);

//         // Get siblings and verify locally
//         let siblings = tree.get_siblings(leaf_index);
//         assert!(tree.verify_path(leaf_index), "Local verification failed");

//         // Setup and prove
//         let config = PcsConfig::default();
//         let channel = &mut Blake2sChannel::default();
//         let twiddles =
//             SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//         let commitment_scheme =
//             CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

//         let (proof, _, _, statement0, statement1) = prove_merkle(
//             tree.depth,
//             tree.leaves[leaf_index],
//             siblings,
//             leaf_index as u32,
//             tree.root,
//             channel,
//             commitment_scheme,
//         )
//         .expect("Proof generation failed");

//         // Verify
//         verify_merkle(proof, tree.depth, statement0, statement1, config)
//             .expect("Verification failed");

//         println!("✅ Verified successfully! (Depth 4, 16 leaves) 🎉");
//     }

//     #[test]
//     fn test_kkrt_multiple_indices() {
//         println!("\n=== KKRT Multiple Leaf Indices Test ===\n");

//         // Generate one tree and test multiple leaf indices
//         let tree = generate_merkle_tree(3, 500);

//         println!("Testing tree with {} leaves", tree.leaves.len());
//         println!("Root: {}\n", tree.root.0);

//         // Test indices: 0 (leftmost), 3 (middle-ish), 7 (rightmost)
//         let test_indices = vec![0, 3, 7];

//         for &leaf_index in &test_indices {
//             println!("--- Testing leaf {} ---", leaf_index);
//             let siblings = tree.get_siblings(leaf_index);
//             assert!(
//                 tree.verify_path(leaf_index),
//                 "Local verification failed for index {}",
//                 leaf_index
//             );

//             let config = PcsConfig::default();
//             let channel = &mut Blake2sChannel::default();
//             let twiddles =
//                 SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
//             let commitment_scheme =
//                 CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(
//                     config,
//                     &twiddles,
//                 );

//             let (proof, _, _, statement0, statement1) = prove_merkle(
//                 tree.depth,
//                 tree.leaves[leaf_index],
//                 siblings,
//                 leaf_index as u32,
//                 tree.root,
//                 channel,
//                 commitment_scheme,
//             )
//             .expect("Proof generation failed");

//             verify_merkle(proof, tree.depth, statement0, statement1, config)
//                 .expect("Verification failed");

//             println!("   ✅ Leaf {} verified!", leaf_index);
//         }

//         println!("\n🎉 All indices verified successfully!");
//     }

//     #[test]
//     #[ignore] // Requires larger twiddles configuration
//     fn test_kkrt_depth_5() {
//         println!("\n=== KKRT Merkle Test (Depth 5, 32 leaves) ===\n");
//         println!("⚠️  This test requires larger twiddles and is ignored by default");
//         println!("    Run with: cargo test -- --ignored test_kkrt_depth_5\n");

//         // Note: depth=5 (32 leaves, 5 active rows) requires careful twiddles setup
//         // The standard tests (depth 2-4) demonstrate KKRT implementation well
//         // This is here as a placeholder for future optimization

//         let tree = generate_merkle_tree(5, 2000);
//         println!("Tree with {} leaves generated successfully!", tree.leaves.len());
//         println!("Root: {}", tree.root.0);

//         // Verify tree structure works
//         assert_eq!(tree.leaves.len(), 32);
//         assert_eq!(tree.depth, 5);
//         assert!(tree.verify_path(0), "Path verification failed");

//         println!("✅ Tree structure verified (STARK proof generation skipped)");
//     }

//     #[test]
//     fn test_kkrt_info() {
//         println!("\n=== KKRT Implementation Info ===\n");

//         println!("📊 KKRT Style vs Standard Sponge Comparison:\n");

//         println!("Node representation:");
//         println!("  • KKRT:     1 M31 element  (single field element)");
//         println!("  • Standard: 8 M31 elements (full rate)");
//         println!("  → Proof size reduction: 8x smaller!\n");

//         println!("Rows per tree level:");
//         println!("  • KKRT:     1 row  (single permutation with [left, right, 0, ...])");
//         println!("  • Standard: 2 rows (sequential absorption)");
//         println!("  → Trace reduction: 2x fewer rows!\n");

//         println!("Hash computation:");
//         println!("  • KKRT:     hash([left, right, 0, 0, ..., 0]) → state[0]");
//         println!("  • Standard: absorb(left) → absorb(right) → state[0..8]");
//         println!("  → Simpler and more efficient!\n");

//         println!("Column counts (for depth=2 tree):");
//         let depth = 2;

//         // KKRT counts
//         const KKRT_COMPUTING_COLS: usize = 174; // No message columns
//         const KKRT_SCHEDULER_COLS: usize = 2;    // 1 + 1
//         let kkrt_total = KKRT_COMPUTING_COLS + KKRT_SCHEDULER_COLS;

//         // Standard counts (from old implementation)
//         const STD_COMPUTING_COLS: usize = 182; // 8 message + 174 others
//         const STD_SCHEDULER_COLS: usize = 16;  // 8 + 8
//         let std_total = STD_COMPUTING_COLS + STD_SCHEDULER_COLS;

//         println!("  Computing component:");
//         println!("    • KKRT:     {} columns", KKRT_COMPUTING_COLS);
//         println!("    • Standard: {} columns", STD_COMPUTING_COLS);

//         println!("  Scheduler component:");
//         println!("    • KKRT:     {} columns", KKRT_SCHEDULER_COLS);
//         println!("    • Standard: {} columns", STD_SCHEDULER_COLS);

//         println!("  Total:");
//         println!("    • KKRT:     {} columns", kkrt_total);
//         println!("    • Standard: {} columns", std_total);
//         println!("    → Column reduction: {} fewer columns!\n", std_total - kkrt_total);

//         println!("Active rows (for depth={}):", depth);
//         println!("  • KKRT:     {} rows", depth);
//         println!("  • Standard: {} rows", depth * 2);
//         println!("  → {} fewer active rows!\n", depth);

//         println!("✨ KKRT Labs style achieves significant efficiency gains!");
//         println!("   Reference: https://github.com/KKRT-labs/cairo-m\n");
//     }
// }
