//! Complete End-to-End Privacy Mixer Flow
//!
//! This test demonstrates the COMPLETE flow matching the frontend:
//! 1. Generate operations (deterministic)
//! 2. Compute commitments
//! 3. Add to HybridMerkleTree (incremental with zero hashes)
//! 4. Get proof data
//! 5. Verify using STARK proof (AIR)

#[cfg(test)]
mod tests {
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::poly::circle::PolyOps;
    use stwo::prover::CommitmentSchemeProver;

    use crate::mixer::full_flow::{
        compute_commitment, generate_operation, HybridMerkleTree,
    };
    use crate::utils::{prove_merkle, verify_merkle};

    #[test]
    fn test_complete_privacy_mixer_flow() {
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
        // let config = PcsConfig {
        //     pow_bits: 32,
        //     fri_config: FriConfig::new(5, 2, 32),
        // };            pow_bits: 42,
            // fri_config: super::FriConfig::new(10, 10, 70),

        let config = PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(0, 1, 3),
        };
        println!("Security bits: {}", config.security_bits());
        let channel = &mut Blake2sChannel::default();
        let twiddles =
            SimdBackend::precompute_twiddles(CanonicCoset::new(20).circle_domain().half_coset);
        let commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        // Generate STARK proof for membership
        println!("Generating STARK proof...");
        let (proof, _, _, statement0, statement1) = prove_merkle(
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
        verify_merkle(proof, tree_height - 1, statement0, statement1, config)
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

    #[test]
    fn test_multiple_verifications() {
        println!("\n╔══════════════════════════════════════════════════════════╗");
        println!("║        Multiple Verifications (like batch withdraw)      ║");
        println!("╚══════════════════════════════════════════════════════════╝\n");

        let master_nonce = BaseField::from_u32_unchecked(111222333);
        let amount = BaseField::from_u32_unchecked(500);
        let token = BaseField::from_u32_unchecked(1);

        // Generate 3 operations and commitments
        let ops: Vec<_> = (0..3)
            .map(|i| generate_operation(i, master_nonce))
            .collect();

        let commitments: Vec<_> = ops
            .iter()
            .map(|op| compute_commitment(op.hash, amount, token))
            .collect();

        // Build tree
        let mut tree = HybridMerkleTree::new(4);
        for &commitment in &commitments {
            tree.add_leaf(commitment);
        }

        println!("Tree with {} commitments", commitments.len());
        println!("Root: {}\n", tree.get_root().0);

        // Setup for verification
        let config = PcsConfig::default();
        let twiddles =
            SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);

        // Verify each commitment
        for (i, &commitment) in commitments.iter().enumerate() {
            println!("Verifying commitment {}...", i);

            let channel = &mut Blake2sChannel::default();
            let commitment_scheme =
                CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

            let proof_data = tree.get_proof_data(commitment).unwrap();

            let (proof, _, _, statement0, statement1) = prove_merkle(
                3, // depth
                commitment,
                proof_data.siblings,
                proof_data.index as u32,
                proof_data.root,
                channel,
                commitment_scheme,
            )
            .unwrap();

            verify_merkle(proof, 3, statement0, statement1, config).unwrap();

            println!(
                "  ✅ Commitment {} verified (index {})",
                i, proof_data.index
            );
        }

        println!(
            "\n🎉 All {} commitments verified successfully!",
            commitments.len()
        );
    }

    #[test]
    fn test_production_tree_height_32() {
        println!("\n╔══════════════════════════════════════════════════════════╗");
        println!("║     PRODUCTION HEIGHT (32) - Full Scale Test            ║");
        println!("╚══════════════════════════════════════════════════════════╝\n");

        // ═══════════════════════════════════════════════════════════
        // STEP 1: Generate Operations
        // ═══════════════════════════════════════════════════════════
        println!("📝 STEP 1: Generate Operations\n");

        let master_nonce = BaseField::from_u32_unchecked(123456789);
        let num_operations = 10; // Can test with more if needed

        let operations: Vec<_> = (0..num_operations)
            .map(|i| generate_operation(i, master_nonce))
            .collect();

        println!("Generated {} operations", num_operations);

        // ═══════════════════════════════════════════════════════════
        // STEP 2: Compute Commitments
        // ═══════════════════════════════════════════════════════════
        println!("\n💰 STEP 2: Compute Commitments\n");

        let amount = BaseField::from_u32_unchecked(1000);
        let token_address = BaseField::from_u32_unchecked(42);

        let commitments: Vec<_> = operations
            .iter()
            .map(|op| compute_commitment(op.hash, amount, token_address))
            .collect();

        println!("Computed {} commitments", commitments.len());

        // ═══════════════════════════════════════════════════════════
        // STEP 3: Build Production-Scale Merkle Tree (HEIGHT = 32)
        // ═══════════════════════════════════════════════════════════
        println!("\n🌳 STEP 3: Build Merkle Tree with HEIGHT = 32\n");

        let tree_height = 32; // PRODUCTION HEIGHT
        let mut tree = HybridMerkleTree::new(tree_height);

        println!("✅ Created hybrid tree with height {}", tree_height);
        println!(
            "   Max capacity: 2^{} = {} leaves",
            tree_height - 1,
            1u64 << (tree_height - 1)
        );
        println!("   Precomputed zero hashes: {}", tree.precomputed.len());

        println!("\nFirst 5 precomputed zero hashes:");
        for (i, hash) in tree.precomputed.iter().take(5).enumerate() {
            println!("  Level {}: {}", i, hash.0);
        }
        println!("  ...");
        println!("  Level 31: {}", tree.precomputed[31].0);

        println!("\nAdding commitments:");
        for (i, &commitment) in commitments.iter().enumerate() {
            tree.add_leaf(commitment);
            if i < 3 || i == commitments.len() - 1 {
                println!("  [{}] Root: {}", i, tree.get_root().0);
            } else if i == 3 {
                println!("  ...");
            }
        }

        let final_root = tree.get_root();
        println!("\n✅ Final Merkle Root: {}", final_root.0);
        println!("   Current leaves: {}", tree.get_leafs().len());

        // ═══════════════════════════════════════════════════════════
        // STEP 4: Get Proof Data (depth = 31)
        // ═══════════════════════════════════════════════════════════
        println!("\n🔗 STEP 4: Get Proof Data\n");

        let target_commitment = commitments[5]; // Middle commitment
        let proof_data = tree
            .get_proof_data(target_commitment)
            .expect("Failed to get proof data");

        println!("Proof data for commitment at index {}:", proof_data.index);
        println!("  Root: {}", proof_data.root.0);
        println!(
            "  Siblings path length: {} (depth = {})",
            proof_data.siblings.len(),
            tree_height - 1
        );
        println!("  First 3 siblings:");
        for (i, sibling) in proof_data.siblings.iter().take(3).enumerate() {
            println!(
                "    Level {}: {} (isRight: {})",
                i, sibling.0, proof_data.is_right[i]
            );
        }
        println!("  ...");

        // ═══════════════════════════════════════════════════════════
        // STEP 5: Verify with STARK (depth = 31)
        // ═══════════════════════════════════════════════════════════
        println!("\n✨ STEP 5: STARK Verification (depth = 31)\n");

        let config = PcsConfig::default();
        let channel = &mut Blake2sChannel::default();

        // Note: log_size must accommodate depth=31 trace
        // We need at least 2^5=32 rows for depth=31
        let twiddles =
            SimdBackend::precompute_twiddles(CanonicCoset::new(16).circle_domain().half_coset);
        let commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        println!("Generating STARK proof for depth = {} ...", tree_height - 1);
        let start = std::time::Instant::now();

        let (proof, _, _, statement0, statement1) = prove_merkle(
            tree_height - 1, // depth = 31
            target_commitment,
            proof_data.siblings.clone(),
            proof_data.index as u32,
            proof_data.root,
            channel,
            commitment_scheme,
        )
        .expect("Failed to generate proof");

        let proof_time = start.elapsed();
        println!("✅ STARK proof generated in {:?}", proof_time);

        println!("\nVerifying STARK proof...");
        let start = std::time::Instant::now();

        verify_merkle(proof, tree_height - 1, statement0, statement1, config)
            .expect("Failed to verify proof");

        let verify_time = start.elapsed();
        println!("✅ STARK proof verified in {:?}", verify_time);

        // ═══════════════════════════════════════════════════════════
        // SUMMARY
        // ═══════════════════════════════════════════════════════════
        println!("\n╔══════════════════════════════════════════════════════════╗");
        println!("║          PRODUCTION SCALE TEST COMPLETE ✅                ║");
        println!("╚══════════════════════════════════════════════════════════╝\n");

        println!("📊 Production Statistics:");
        println!("  Tree height: {}", tree_height);
        println!("  Tree depth: {}", tree_height - 1);
        println!(
            "  Max capacity: 2^{} = {} leaves",
            tree_height - 1,
            1u64 << (tree_height - 1)
        );
        println!("  Current leaves: {}", tree.get_leafs().len());
        println!("  Precomputed hashes: {}", tree.precomputed.len());
        println!("  Siblings path length: {}", proof_data.siblings.len());
        println!("  Final root: {}", final_root.0);
        println!("  Proof generation time: {:?}", proof_time);
        println!("  Verification time: {:?}", verify_time);

        println!(
            "\n🎉 Successfully verified commitment at index {} in production-scale tree!",
            proof_data.index
        );
        println!("This tree can hold up to {} leaves (2^31)!", 1u64 << 31);
    }
}
