use stwo::prover::poly::circle::SecureCirclePoly;
use stwo::prover::{CommitmentSchemeProver, ComponentProver, ComponentProvers, ProvingError};
use tracing::{info, span, Level};

use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::circle::CirclePoint;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::proof::StarkProof;
use stwo::core::verifier::PREPROCESSED_TRACE_IDX;
use stwo::prover::backend::BackendForChannel;

// pub use air::component_prover::{ComponentProver, ComponentProvers, Trace};
// pub use air::{AccumulationOps, ColumnAccumulator, DomainEvaluationAccumulator};
// pub use pcs::quotient_ops::QuotientOps;
// pub use pcs::{CommitmentSchemeProver, CommitmentTreeProver, TreeBuilder};


pub fn prove<B: BackendForChannel<MC>, MC: MerkleChannel>(
    components: &[&dyn ComponentProver<B>],
    channel: &mut MC::C,
    mut commitment_scheme: CommitmentSchemeProver<'_, B, MC>,
) -> Result<(StarkProof<MC::H>, SecureCirclePoly<B>), ProvingError> {
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .polynomials
        .len();
    let component_provers = ComponentProvers {
        components: components.to_vec(),
        n_preprocessed_columns,
    };
    let trace = commitment_scheme.trace();

    // Evaluate and commit on composition polynomial.
    let random_coeff = channel.draw_secure_felt();

    let span = span!(Level::INFO, "Composition", class = "Composition").entered();
    let span1 = span!(
        Level::INFO,
        "Generation",
        class = "CompositionPolynomialGeneration"
    )
    .entered();
    let composition_poly= component_provers.compute_composition_polynomial(random_coeff, &trace);
    let compostion_polynomial_to_return = component_provers.compute_composition_polynomial(random_coeff, &trace);
    span1.exit();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_polys(composition_poly.into_coordinate_polys());
    tree_builder.commit(channel);
    span.exit();

    // Draw OODS point.
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);

    // Get mask sample points relative to oods point.
    let mut sample_points = component_provers.components().mask_points(oods_point);

    // Add the composition polynomial mask points.
    sample_points.push(vec![vec![oods_point]; SECURE_EXTENSION_DEGREE]);

    // Prove the trace and composition OODS values, and retrieve them.
    let commitment_scheme_proof = commitment_scheme.prove_values(sample_points, channel);
    let proof = StarkProof(commitment_scheme_proof);
    info!(proof_size_estimate = proof.size_estimate());

    // Evaluate composition polynomial at OODS point and check that it matches the trace OODS
    // values. This is a sanity check.
    if extract_composition_oods_eval::<MC>(&proof).unwrap()
        != component_provers
            .components()
            .eval_composition_polynomial_at_point(oods_point, &proof.sampled_values, random_coeff)
    {
        return Err(ProvingError::ConstraintsNotSatisfied);
    }

    Ok((proof, compostion_polynomial_to_return))
}


pub fn extract_composition_oods_eval<MC: MerkleChannel>(
    proof: &StarkProof<MC::H>,
) -> Option<SecureField> {
    // TODO(andrew): `[.., composition_mask, _quotients_mask]` when add quotients
    // commitment.
    let [.., composition_mask] = &**proof.sampled_values else {
        return None;
    };
    let coordinate_evals = composition_mask
        .iter()
        .map(|columns| {
            let &[eval] = &columns[..] else {
                return None;
            };
            Some(eval)
        })
        .collect::<Option<Vec<_>>>()?
        .try_into()
        .ok()?;
    Some(SecureField::from_partial_evals(coordinate_evals))
}
