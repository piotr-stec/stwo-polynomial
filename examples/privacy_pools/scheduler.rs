use num_traits::One;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry, ORIGINAL_TRACE_IDX,
};

use crate::utils::{MerkleRelation, LOG_EXPAND};

/// Evaluator for Merkle Scheduler component (KKRT STYLE)
///
/// This component uses (consumes) the computed_root from the Merkle Computing component
/// and verifies it matches the expected_root (public input).
///
/// KKRT style: Both roots are SINGLE M31 values (not 8-element arrays).
///
/// Trace columns (ORIGINAL_TRACE_IDX):
/// - Column 0: computed_root (1 element from Computing component)
/// - Column 1: expected_root (1 element, public input)
///
/// Constraints:
/// 1. computed_root == expected_root (single value equality, all rows)
/// 2. Transition constraints: values are constant across rows (both values same in all rows)
/// 3. LogUp: uses computed_root ONLY in first row (multiplicity = -is_first)
///
/// All rows have the same constant values.
#[derive(Clone)]
pub struct MerkleSchedulerEval {
    pub log_n_rows: u32,
    pub merkle_relation: MerkleRelation,
    pub claimed_sum: SecureField,
    pub is_first_id: PreProcessedColumnId,
}

impl FrameworkEval for MerkleSchedulerEval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + LOG_EXPAND
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let is_first = eval.get_preprocessed_column(self.is_first_id.clone());

        // Read computed_root (1 element) - current and previous row
        let [computed_root_curr, computed_root_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);

        // Read expected_root (1 element) - current and previous row
        let [expected_root_curr, expected_root_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);

        // Constraint 1: computed_root == expected_root (for all rows, single value)
        // This is the main Merkle verification constraint
        eval.add_constraint(computed_root_curr.clone() - expected_root_curr.clone());

        // Constraint 2: Transition constraints - values are constant across rows
        // Disabled for first row
        let not_first = E::F::one() - is_first.clone();

        eval.add_constraint(not_first.clone() * (computed_root_curr.clone() - computed_root_prev));
        eval.add_constraint(not_first * (expected_root_curr.clone() - expected_root_prev));

        // LogUp: Use computed_root ONLY in first row (multiplicity = -is_first)
        // This "consumes" the value that Computing component "yielded"
        eval.add_to_relation(RelationEntry::new(
            &self.merkle_relation,
            (-is_first.clone()).into(), // multiplicity: -1 for row 0, 0 for rest
            &[computed_root_curr],      // KKRT: single element array
        ));

        eval.finalize_logup_in_pairs();

        eval
    }
}

pub type MerkleSchedulerComponent = FrameworkComponent<MerkleSchedulerEval>;
