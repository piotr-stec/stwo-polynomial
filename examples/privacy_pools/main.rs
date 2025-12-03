mod mixer;
mod computing;
mod scheduler;
mod trace_gen;
mod utils;

use mixer::full_flow::{generate_operation, compute_commitment, HybridMerkleTree};
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::CommitmentSchemeProver;
use utils::{prove_merkle, verify_merkle};
use stwo::prover::poly::circle::PolyOps;
fn main() {
    println!("🔒 Privacy Pools Example");
    
    // Complete privacy mixer flow (same as test)
    run_complete_privacy_mixer_flow();
}

fn run_complete_privacy_mixer_flow() {
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
        pow_bits: 10,
        fri_config: FriConfig::new(2, 2, 70),
    };
    println!("Security bits: {}", config.security_bits());
    let channel = &mut Blake2sChannel::default();
    let twiddles =
        SimdBackend::precompute_twiddles(CanonicCoset::new(20).circle_domain().half_coset);
    let commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

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

    println!("✅ STARK proof generated successfully!");

    // Verify STARK proof
    println!("\nVerifying STARK proof...");
    verify_merkle(proof, tree_height - 1, statement0, statement1, config, composition_polynomial)
        .expect("Failed to verify proof");

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
