use stwo_prover::core::air::{Component, Components};
use stwo_prover::core::backend::BackendForChannel;
use stwo_prover::core::channel::{Channel, MerkleChannel};
use stwo_prover::core::circle::CirclePoint;
use stwo_prover::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo_prover::core::pcs::{CommitmentSchemeVerifier, TreeVec};
use stwo_prover::core::poly::circle::SecureCirclePoly;
use stwo_prover::core::prover::{StarkProof, VerificationError};
use stwo_prover::core::queries::QueriesWithBranching;
use stwo_prover::core::ColumnVec;
use tracing::instrument;
pub const PREPROCESSED_TRACE_IDX: usize = 0;

pub fn verify_with_queries<B: BackendForChannel<MC>, MC: MerkleChannel>(
    components: &[&dyn Component],
    channel: &mut MC::C,
    commitment_scheme: &mut CommitmentSchemeVerifier<MC>,
    proof: StarkProof<MC::H>,
    composition_polynomial: SecureCirclePoly<B>,
) -> Result<(QueriesWithBranching, TreeVec<ColumnVec<u32>>), VerificationError> {
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .column_log_sizes
        .len();

    let components = Components {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    let random_coeff = channel.draw_felt();

    // Read composition polynomial commitment.
    commitment_scheme.commit(
        *proof.commitments.last().unwrap(),
        &[components.composition_log_degree_bound(); SECURE_EXTENSION_DEGREE],
        channel,
    );

    // Draw OODS point.
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);

    // Get mask sample points relative to oods point.
    let mut sample_points = components.mask_points(oods_point);
    // Add the composition polynomial mask points.
    sample_points.push(vec![vec![oods_point]; SECURE_EXTENSION_DEGREE]);

    let composition_oods_eval = proof.extract_composition_oods_eval().map_err(|_| {
        VerificationError::InvalidStructure("Unexpected sampled_values structure".to_string())
    })?;

    if composition_oods_eval != composition_polynomial.eval_at_point(oods_point) {
        return Err(VerificationError::OodsNotMatching);
    }

    commitment_scheme.verify_values(sample_points, proof.0, channel)
}
