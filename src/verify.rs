use std_shims::vec;
use stwo::core::air::{Component, Components};
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::circle::CirclePoint;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::CommitmentSchemeVerifier;
use stwo::core::proof::StarkProof;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::BackendForChannel;
use stwo::prover::poly::circle::SecureCirclePoly;

use crate::prove::extract_composition_oods_eval;
pub const PREPROCESSED_TRACE_IDX: usize = 0;

pub fn verify<B: BackendForChannel<MC>, MC: MerkleChannel>(
    components: &[&dyn Component],
    channel: &mut MC::C,
    commitment_scheme: &mut CommitmentSchemeVerifier<MC>,
    proof: StarkProof<MC::H>,
    composition_polynomial: SecureCirclePoly<B>,
) -> Result<(), VerificationError> {
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .column_log_sizes
        .len();

    let components = Components {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    tracing::info!(
        "Composition polynomial log degree bound: {}",
        components.composition_log_degree_bound()
    );
    let _random_coeff = channel.draw_secure_felt();

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

    let sample_points_by_column = sample_points.as_cols_ref().flatten();
    tracing::info!("Sampling {} columns.", sample_points_by_column.len());
    tracing::info!(
        "Total sample points: {}.",
        sample_points_by_column.into_iter().flatten().count()
    );

    let composition_oods_eval = extract_composition_oods_eval::<MC>(&proof)
            .ok_or(VerificationError::InvalidStructure(
                std_shims::ToString::to_string(&"Unexpected sampled_values structure"),
            ))?;

    if composition_oods_eval
        != composition_polynomial.eval_at_point(oods_point)
    {
        return Err(VerificationError::OodsNotMatching);
    }

    commitment_scheme.verify_values(sample_points, proof.0, channel)
}


