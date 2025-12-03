use num_traits::One;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::bit_reverse_coset_to_circle_domain_order;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::poly::circle::{CircleEvaluation, CirclePoly};
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use crate::utils::{
    apply_external_round_matrix, apply_internal_round_matrix, pow5, PoseidonRelation,
    EXTERNAL_ROUND_CONSTS, FULL_ROUNDS, INTERNAL_ROUND_CONSTS, N_COLUMNS, N_HALF_FULL_ROUNDS,
    N_PARTIAL_ROUNDS, N_STATE, RATE,
};

/// Generate trace for Poseidon Computing component
///
/// Returns (trace columns, target_final_state)
/// - trace: N_COLUMNS columns (message + initial_state + intermediates + final_state)
/// - target_final_state: the final_state at target_message row (BEFORE bit-reversal)
///
/// Generates Poseidon hashes only up to n_active_messages (inclusive), rest are padding zeros.
///
/// # Arguments
/// * `log_size` - Log2 of total number of rows
/// * `n_active_messages` - Number of active messages to hash (rest are padding)
/// * `messages` - Vector of messages (each RATE=8 elements)
///
/// # Returns
/// * Trace columns (bit-reversed)
/// * target_final_state: final_state at row (n_active_messages - 1) before bit-reversal
pub fn gen_poseidon_computing_trace(
    log_size: u32,
    n_active_messages: usize,
    messages: Vec<[BaseField; RATE]>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    [BaseField; N_STATE],
) {
    let n_rows = 1 << log_size;

    // Extend messages to fill all rows if needed
    let mut extended_messages = messages;
    while extended_messages.len() < n_rows {
        extended_messages.push([BaseField::from_u32_unchecked(0); RATE]);
    }

    let mut trace = (0..N_COLUMNS)
        .map(|_| Col::<SimdBackend, BaseField>::zeros(n_rows))
        .collect::<Vec<_>>();

    let mut prev_output: Option<[BaseField; N_STATE]> = None;
    let mut target_final_state = [BaseField::from_u32_unchecked(0); N_STATE];

    for row in 0..n_rows {
        let mut col_index = 0;
        let is_padding_row = row >= n_active_messages;

        // For padding rows: use zero message
        let message = if is_padding_row {
            [BaseField::from_u32_unchecked(0); RATE]
        } else {
            extended_messages[row]
        };

        // Write message columns (8 elements)
        for i in 0..RATE {
            trace[col_index].set(row, message[i]);
            col_index += 1;
        }

        // Compute initial state
        let mut state: [BaseField; N_STATE] = if !is_padding_row && prev_output.is_some() {
            // Not first row AND not padding: state = [prev_rate + message, prev_capacity]
            let prev = prev_output.unwrap();
            std::array::from_fn(|i| {
                if i < RATE {
                    prev[i] + message[i]
                } else {
                    prev[i]
                }
            })
        } else {
            // First row OR padding row: state = [message, zeros] (no chaining)
            let new_state = if is_padding_row {
                // Padding row: completely zero initial state
                [BaseField::from_u32_unchecked(0); N_STATE]
            } else {
                // First row: state = [message, zeros]
                std::array::from_fn(|i| {
                    if i < RATE {
                        message[i]
                    } else {
                        BaseField::from_u32_unchecked(0)
                    }
                })
            };
            new_state
        };

        // Write initial state columns (16 elements)
        for i in 0..N_STATE {
            trace[col_index].set(row, state[i]);
            col_index += 1;
        }

        // For padding rows: skip Poseidon computation, set intermediate and final states to zeros
        if is_padding_row {
            // Intermediate states for first 4 full rounds: all zeros
            for _ in 0..N_HALF_FULL_ROUNDS {
                for _ in 0..N_STATE {
                    trace[col_index].set(row, BaseField::from_u32_unchecked(0));
                    col_index += 1;
                }
            }

            // Partial rounds intermediate states: all zeros
            for _ in 0..N_PARTIAL_ROUNDS {
                trace[col_index].set(row, BaseField::from_u32_unchecked(0));
                col_index += 1;
            }

            // Intermediate states for last 4 full rounds: all zeros
            for _ in 0..N_HALF_FULL_ROUNDS {
                for _ in 0..N_STATE {
                    trace[col_index].set(row, BaseField::from_u32_unchecked(0));
                    col_index += 1;
                }
            }

            // Final state: all zeros
            for _ in 0..N_STATE {
                trace[col_index].set(row, BaseField::from_u32_unchecked(0));
                col_index += 1;
            }
        } else {
            // Active row: compute Poseidon permutation normally
            // 4 full rounds
            (0..N_HALF_FULL_ROUNDS).for_each(|round| {
                (0..N_STATE).for_each(|i| {
                    state[i] += EXTERNAL_ROUND_CONSTS[round][i];
                });
                apply_external_round_matrix(&mut state);
                state = std::array::from_fn(|i| pow5(state[i]));
                state.iter().for_each(|&s| {
                    trace[col_index].set(row, s);
                    col_index += 1;
                });
            });

            // Partial rounds
            (0..N_PARTIAL_ROUNDS).for_each(|round| {
                state[0] += INTERNAL_ROUND_CONSTS[round];
                apply_internal_round_matrix(&mut state);
                state[0] = pow5(state[0]);
                trace[col_index].set(row, state[0]);
                col_index += 1;
            });

            // 4 full rounds
            (0..N_HALF_FULL_ROUNDS).for_each(|round| {
                (0..N_STATE).for_each(|i| {
                    state[i] += EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
                });
                apply_external_round_matrix(&mut state);
                state = std::array::from_fn(|i| pow5(state[i]));
                state.iter().for_each(|&s| {
                    trace[col_index].set(row, s);
                    col_index += 1;
                });
            });

            // Write final state columns (16 elements)
            for &s in state.iter() {
                trace[col_index].set(row, s);
                col_index += 1;
            }

            // Save the final_state at target_message row (BEFORE bit-reversal)
            if row == n_active_messages - 1 {
                target_final_state = state;
            }
        }

        // Store output for next row (only for active rows)
        if !is_padding_row {
            prev_output = Some(state);
        }
    }

    // Apply bit_reverse_coset_to_circle_domain_order to trace columns
    for col in trace.iter_mut() {
        bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());
    }

    let domain = CanonicCoset::new(log_size).circle_domain();
    let trace = trace
        .into_iter()
        .map(|eval| CircleEvaluation::new(domain, eval))
        .collect();

    (trace, target_final_state)
}

/// Generate interaction trace for Poseidon Computing component using LogUp
///
/// Only the target_message row (= n_active_messages - 1) yields its final_state:
///   Adds: +1 / (final_state - z)  to the LogUp column for that row
///   Other rows contribute 0 (numerator=0)
///
/// This allows Scheduler to verify it's using the correct Poseidon hash result
///
/// # Arguments
/// * `trace` - Main trace columns (bit-reversed)
/// * `poseidon_relation` - LogUp relation elements
/// * `n_active_messages` - Number of active messages (target = n_active_messages - 1)
///
/// # Returns
/// * Interaction trace columns (bit-reversed)
/// * claimed_sum - LogUp claimed sum for this component
pub fn gen_poseidon_computing_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    poseidon_relation: &PoseidonRelation,
    n_active_messages: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = trace[0].domain.log_size();
    let n_rows = 1 << log_size;

    // Target row is the last active message (0-indexed)
    let target_row = n_active_messages - 1;

    // Create selector column: 1 only for target_row, 0 for rest
    let mut selector_col = Col::<SimdBackend, BaseField>::zeros(n_rows);
    selector_col.set(target_row, BaseField::one());

    // IMPORTANT: Apply bit-reverse to match trace column ordering!
    bit_reverse_coset_to_circle_domain_order(selector_col.as_mut_slice());

    let mut logup_gen = LogupTraceGenerator::new(log_size);

    {
        let mut col_gen = logup_gen.new_col();

        // Final state columns start at: RATE + N_STATE + N_STATE*FULL_ROUNDS + N_PARTIAL_ROUNDS
        let final_state_col_start = RATE + N_STATE + N_STATE * FULL_ROUNDS + N_PARTIAL_ROUNDS;

        // For each vec_row, yield the final_state with selector masking
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Read final_state (16 elements)
            let final_state_packed: [_; N_STATE] =
                std::array::from_fn(|i| trace[final_state_col_start + i].data[vec_row]);

            // Compute denominator: poseidon_relation.combine(final_state)
            let denom = poseidon_relation.combine(&final_state_packed);

            // Use selector - only target_row lane has numerator=1
            let numerator: PackedSecureField = selector_col.data[vec_row].into();

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}

/// Generate trace for Poseidon Scheduler component
///
/// Returns 3 * N_STATE = 48 columns:
/// - Columns 0-15: poseidon1_final_state (from Computing1)
/// - Columns 16-31: poseidon2_final_state (from Computing2)
/// - Columns 32-47: combined_state (element-wise sum)
///
/// All rows have the same constant values.
///
/// # Arguments
/// * `log_size` - Log2 of total number of rows
/// * `poseidon1_final_state` - Final state from Computing1 (16 elements)
/// * `poseidon2_final_state` - Final state from Computing2 (16 elements)
///
/// # Returns
/// * Trace columns (bit-reversed)
pub fn gen_poseidon_scheduler_trace(
    log_size: u32,
    poseidon1_final_state: [BaseField; N_STATE],
    poseidon2_final_state: [BaseField; N_STATE],
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let n_rows = 1 << log_size;

    // Compute combined_state: element-wise addition
    let combined_state: [BaseField; N_STATE] =
        std::array::from_fn(|i| poseidon1_final_state[i] + poseidon2_final_state[i]);

    println!("  Scheduler trace:");
    println!(
        "    poseidon1_final_state[0]: {}",
        poseidon1_final_state[0].0
    );
    println!(
        "    poseidon2_final_state[0]: {}",
        poseidon2_final_state[0].0
    );
    println!("    combined_state[0]: {}", combined_state[0].0);

    // Create 48 columns (3 * N_STATE)
    let mut columns: Vec<Col<SimdBackend, BaseField>> = Vec::with_capacity(3 * N_STATE);

    // Columns 0-15: poseidon1_final_state
    for i in 0..N_STATE {
        let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);
        for row in 0..n_rows {
            col.set(row, poseidon1_final_state[i]);
        }
        columns.push(col);
    }

    // Columns 16-31: poseidon2_final_state
    for i in 0..N_STATE {
        let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);
        for row in 0..n_rows {
            col.set(row, poseidon2_final_state[i]);
        }
        columns.push(col);
    }

    // Columns 32-47: combined_state
    for i in 0..N_STATE {
        let mut col = Col::<SimdBackend, BaseField>::zeros(n_rows);
        for row in 0..n_rows {
            col.set(row, combined_state[i]);
        }
        columns.push(col);
    }

    // Convert to bit-reversed circle domain order
    for col in columns.iter_mut() {
        bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());
    }

    let domain = CanonicCoset::new(log_size).circle_domain();
    columns
        .into_iter()
        .map(|col| CircleEvaluation::new(domain, col))
        .collect()
}

/// Generate interaction trace for Poseidon Scheduler component using LogUp
///
/// For row 0 only, uses two final_state values:
///   Adds: -1 / (poseidon1_final_state - z)  to the LogUp column
///   Adds: -1 / (poseidon2_final_state - z)  to the LogUp column
///
/// The sum of all LogUp entries from Computing1, Computing2, and Scheduler should be 0.
///
/// # Arguments
/// * `trace` - Main trace columns (bit-reversed)
/// * `poseidon_relation` - LogUp relation elements
///
/// # Returns
/// * Interaction trace columns (bit-reversed)
/// * claimed_sum - LogUp claimed sum for this component
pub fn gen_poseidon_scheduler_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    poseidon_relation: &PoseidonRelation,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = trace[0].domain.log_size();
    let n_rows = 1 << log_size;

    // Create is_first selector column: 1 only for row 0, 0 for rest
    let mut is_first_col = Col::<SimdBackend, BaseField>::zeros(n_rows);
    is_first_col.set(0, BaseField::one());

    // IMPORTANT: Apply bit-reverse to match trace column ordering!
    bit_reverse_coset_to_circle_domain_order(is_first_col.as_mut_slice());

    let mut logup_gen = LogupTraceGenerator::new(log_size);

    {
        let mut col_gen = logup_gen.new_col();

        // For each row, use both poseidon1_final_state (columns 0-15) and poseidon2_final_state
        // (columns 16-31) Multiplicity controlled by is_first selector (only row 0
        // contributes)
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Read poseidon1_final_state (16 elements)
            let poseidon1_packed: [_; N_STATE] = std::array::from_fn(|i| trace[i].data[vec_row]);

            // Read poseidon2_final_state (16 elements)
            let poseidon2_packed: [_; N_STATE] =
                std::array::from_fn(|i| trace[N_STATE + i].data[vec_row]);

            // Compute denominators for both values
            let denom1: PackedSecureField = poseidon_relation.combine(&poseidon1_packed);
            let denom2: PackedSecureField = poseidon_relation.combine(&poseidon2_packed);

            // We need to write TWO fractions per row:
            // -1 / (poseidon1 - z) and -1 / (poseidon2 - z)
            //
            // For finalize_logup_in_pairs(), we combine them:
            // -1/denom1 + -1/denom2 = -(denom1 + denom2) / (denom1 * denom2)
            //
            // Multiplicity is controlled by is_first selector

            let is_first_value = is_first_col.data[vec_row];
            let sum: PackedSecureField = denom1 + denom2;
            let is_first_secure: PackedSecureField = is_first_value.into();
            let numerator = -(sum * is_first_secure); // -1 * (denom1+denom2) for row 0, 0 for rest
            let denominator = denom1 * denom2;

            col_gen.write_frac(vec_row, numerator, denominator);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}

/// Generate trace for Merkle Computing component (KKRT STYLE)
///
/// Computes a Merkle path verification using KKRT Labs approach:
/// - Each node is a SINGLE M31 value
/// - Each level uses ONE row with hash input [left, right, 0, ..., 0]
/// - Hash output is only state[0] after Poseidon2 permutation
/// - Capacity is implicitly 0 (from padding)
///
/// Returns (trace columns, computed_root)
/// - trace: MerkleComputing columns (initial_state, intermediates, final_state)
/// - computed_root: the final root hash (BEFORE bit-reversal)
///
/// # Arguments
/// * `log_size` - Log2 of total number of rows
/// * `depth` - Tree depth (number of levels in tree)
/// * `leaf` - Starting leaf value (single M31 element)
/// * `siblings` - Sibling nodes for each level (length = depth, each is single M31)
/// * `index` - Leaf position in tree (determines left/right order)
///
/// # Returns
/// * Trace columns (bit-reversed)
/// * computed_root: final root hash at row (depth-1) before bit-reversal
///
/// # KKRT Construction
/// For each level (0..depth):
///   - Row level: hash([left, right, 0, ..., 0]) → state[0] is parent node
/// Total active rows: depth
pub fn gen_merkle_computing_trace(
    log_size: u32,
    depth: usize,
    leaf: BaseField,
    siblings: Vec<BaseField>,
    index: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    BaseField,
) {
    assert_eq!(siblings.len(), depth, "siblings.len() must equal depth");

    let n_rows = 1 << log_size;
    let n_active_rows = depth; // KKRT: 1 row per level (not 2)
    assert!(n_active_rows <= n_rows, "depth must be <= n_rows");

    // Column layout (KKRT STYLE - no message columns):
    // initial_state (16) + intermediates (4*16 + 14 + 4*16 = 142) + final_state (16)
    // = 16 + 142 + 16 = 174 columns
    const MERKLE_COMPUTING_N_COLUMNS: usize = N_STATE
        + (N_HALF_FULL_ROUNDS * N_STATE)
        + N_PARTIAL_ROUNDS
        + (N_HALF_FULL_ROUNDS * N_STATE)
        + N_STATE;

    let mut trace = (0..MERKLE_COMPUTING_N_COLUMNS)
        .map(|_| Col::<SimdBackend, BaseField>::zeros(n_rows))
        .collect::<Vec<_>>();

    let mut current_node = leaf; // Single M31 value
    let mut computed_root = BaseField::from_u32_unchecked(0);

    for row in 0..n_rows {
        let mut col_index = 0;
        let is_padding_row = row >= n_active_rows;

        if is_padding_row {
            // Padding row: all zeros
            for _ in 0..MERKLE_COMPUTING_N_COLUMNS {
                trace[col_index].set(row, BaseField::from_u32_unchecked(0));
                col_index += 1;
            }
        } else {
            // Active row: hash one level (KKRT STYLE - single permutation per level)
            let level = row; // Each row processes one tree level
            let index_bit = (index >> level) & 1;

            // Determine left and right children for this hash
            let (left_child, right_child) = if index_bit == 0 {
                // Current node on left, sibling on right
                (current_node, siblings[level])
            } else {
                // Sibling on left, current node on right
                (siblings[level], current_node)
            };

            // Build initial_state = [left, right, 0, 0, ..., 0] (KKRT style)
            // Element 0: left child
            // Element 1: right child
            // Elements 2-15: zeros (implicit capacity = 0)
            let mut state = [BaseField::from_u32_unchecked(0); N_STATE];
            state[0] = left_child;
            state[1] = right_child;
            // Rest are already zeros from initialization

            // Write initial_state (16 elements)
            for i in 0..N_STATE {
                trace[col_index].set(row, state[i]);
                col_index += 1;
            }

            // Compute Poseidon2 permutation

            // First 4 full rounds
            for round in 0..N_HALF_FULL_ROUNDS {
                for i in 0..N_STATE {
                    state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round][i];
                }
                apply_external_round_matrix(&mut state);
                state = std::array::from_fn(|i| pow5(state[i]));

                // Write intermediate state (16 elements)
                for i in 0..N_STATE {
                    trace[col_index].set(row, state[i]);
                    col_index += 1;
                }
            }

            // Partial rounds
            for round in 0..N_PARTIAL_ROUNDS {
                state[0] = state[0] + INTERNAL_ROUND_CONSTS[round];
                apply_internal_round_matrix(&mut state);
                state[0] = pow5(state[0]);

                // Write intermediate state (1 element)
                trace[col_index].set(row, state[0]);
                col_index += 1;
            }

            // Last 4 full rounds
            for round in 0..N_HALF_FULL_ROUNDS {
                for i in 0..N_STATE {
                    state[i] = state[i] + EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
                }
                apply_external_round_matrix(&mut state);
                state = std::array::from_fn(|i| pow5(state[i]));

                // Write intermediate state (16 elements)
                for i in 0..N_STATE {
                    trace[col_index].set(row, state[i]);
                    col_index += 1;
                }
            }

            // Write final_state (16 elements)
            for i in 0..N_STATE {
                trace[col_index].set(row, state[i]);
                col_index += 1;
            }

            // Extract hash output: ONLY state[0] (KKRT style)
            let hash_output = state[0];

            // Update current_node for next level
            current_node = hash_output;

            // If this is the last active row, save the computed root
            if row == n_active_rows - 1 {
                computed_root = hash_output;
            }
        }
    }

    // Apply bit-reversal to all columns
    for col in trace.iter_mut() {
        bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());
    }

    // Convert to CircleEvaluation
    let trace_cols = trace
        .into_iter()
        .map(|col| CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col))
        .collect::<Vec<_>>();

    (trace_cols, computed_root)
}

/// Generate interaction trace for Merkle Computing component (KKRT STYLE)
///
/// Creates LogUp interaction trace that yields the computed root (1 element)
/// ONLY at the last row (depth - 1).
///
/// # Arguments
/// * `trace` - The main trace columns from gen_merkle_computing_trace
/// * `merkle_relation` - The MerkleRelation for combining 1-element roots
/// * `depth` - Tree depth (determines which row is last: depth - 1)
///
/// # Returns
/// * Interaction trace columns (bit-reversed)
/// * claimed_sum: The LogUp claimed sum for this component
pub fn gen_merkle_computing_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    merkle_relation: &crate::utils::MerkleRelation,
    log_size: u32,
    depth: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1 << log_size;
    let last_row = depth - 1; // Last active row in KKRT construction (1 row per level)

    // Generate is_last selector column (1 only for row depth-1)
    let mut is_last_col = Col::<SimdBackend, BaseField>::zeros(n_rows);
    if depth > 0 {
        is_last_col.set(last_row, BaseField::one());
    }
    bit_reverse_coset_to_circle_domain_order(is_last_col.as_mut_slice());

    // Extract final_state columns (only state[0], 1 element)
    // Column layout (KKRT): initial_state (16) + intermediates (142) + final_state (16)
    // final_state starts at column: 16 + 142 = 158
    const FINAL_STATE_START: usize = N_STATE
        + (N_HALF_FULL_ROUNDS * N_STATE)
        + N_PARTIAL_ROUNDS
        + (N_HALF_FULL_ROUNDS * N_STATE);

    let mut logup_gen = LogupTraceGenerator::new(log_size);

    {
        let mut col_gen = logup_gen.new_col();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Read final_state (only state[0] - 1 element, KKRT style)
            let col_data = &trace[FINAL_STATE_START].data; // Only first element
            let root_value: PackedSecureField = col_data[vec_row].into();

            // Combine using merkle_relation (1 element)
            let denom: PackedSecureField = merkle_relation.combine(&[root_value]);

            // Multiplicity controlled by is_last selector
            let is_last_value = is_last_col.data[vec_row];
            let is_last_secure: PackedSecureField = is_last_value.into();
            let numerator = is_last_secure; // 1 for last row, 0 for rest

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}

/// Generate trace for Merkle Scheduler component (KKRT STYLE)
///
/// Creates a trace where all rows have the same constant values:
/// computed_root and expected_root (each is a SINGLE M31 value).
///
/// # Arguments
/// * `log_size` - Log2 of total number of rows
/// * `computed_root` - The root computed by the Computing component (1 element)
/// * `expected_root` - The expected Merkle root (public input, 1 element)
///
/// # Returns
/// * Trace columns (bit-reversed): computed_root (1 col) + expected_root (1 col) = 2 total
pub fn gen_merkle_scheduler_trace(
    log_size: u32,
    computed_root: BaseField,
    expected_root: BaseField,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let n_rows = 1 << log_size;

    // 2 columns: computed_root (1) + expected_root (1) - KKRT style
    const MERKLE_SCHEDULER_N_COLUMNS: usize = 2;

    let mut trace = (0..MERKLE_SCHEDULER_N_COLUMNS)
        .map(|_| Col::<SimdBackend, BaseField>::zeros(n_rows))
        .collect::<Vec<_>>();

    // All rows have the same values
    for row in 0..n_rows {
        // Write computed_root (1 element)
        trace[0].set(row, computed_root);

        // Write expected_root (1 element)
        trace[1].set(row, expected_root);
    }

    // Apply bit-reversal to all columns
    for col in trace.iter_mut() {
        bit_reverse_coset_to_circle_domain_order(col.as_mut_slice());
    }

    // Convert to CircleEvaluation
    trace
        .into_iter()
        .map(|col| CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col))
        .collect::<Vec<_>>()
}

/// Generate interaction trace for Merkle Scheduler component (KKRT STYLE)
///
/// Creates LogUp interaction trace that uses (consumes) the computed_root
/// ONLY at the first row (multiplicity = -1).
///
/// # Arguments
/// * `trace` - The main trace columns from gen_merkle_scheduler_trace
/// * `merkle_relation` - The MerkleRelation for combining 1-element roots
/// * `log_size` - Log2 of trace size
///
/// # Returns
/// * Interaction trace columns (bit-reversed)
/// * claimed_sum: The LogUp claimed sum for this component
pub fn gen_merkle_scheduler_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    merkle_relation: &crate::utils::MerkleRelation,
    log_size: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1 << log_size;

    // Generate is_first selector column (1 only for row 0)
    let mut is_first_col = Col::<SimdBackend, BaseField>::zeros(n_rows);
    is_first_col.set(0, BaseField::one());
    bit_reverse_coset_to_circle_domain_order(is_first_col.as_mut_slice());

    // Extract computed_root column (first column, 1 element - KKRT style)
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    {
        let mut col_gen = logup_gen.new_col();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Read computed_root (1 element only)
            let col_data = &trace[0].data;  // First column
            let computed_root_value: PackedSecureField = col_data[vec_row].into();

            // Combine using merkle_relation (1 element)
            let denom: PackedSecureField = merkle_relation.combine(&[computed_root_value]);

            // Multiplicity controlled by is_first selector (negative for "use")
            let is_first_value = is_first_col.data[vec_row];
            let is_first_secure: PackedSecureField = is_first_value.into();
            let numerator = -is_first_secure; // -1 for first row, 0 for rest

            col_gen.write_frac(vec_row, numerator, denom);
        }

        col_gen.finalize_col();
    }

    logup_gen.finalize_last()
}
