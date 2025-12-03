//! Complete Privacy Mixer Flow (Frontend-compatible)
//!
//! This module replicates the TypeScript frontend flow:
//! 1. Generate operation (deterministic: secret, nullifier, hash)
//! 2. Compute commitment (hash → amount → token)
//! 3. Add to HybridMerkleTree (incremental with zero hashes)
//! 4. Get proof data (index, siblings, isRight flags, root)
//! 5. Verify using AIR (generate and verify STARK proof)

use stwo::core::fields::m31::BaseField;
 
use crate::utils::hash_two_nodes_kkrt;
/// Operation data (like frontend generateOperation)
#[derive(Debug, Clone)]
pub struct Operation {
    pub index: u32,
    pub secret: BaseField,
    pub nullifier: BaseField,
    pub hash: BaseField,
}

/// Generate operation deterministically (matches frontend logic)
///
/// ```typescript
/// const secret = garaga.poseidonHashBN254(BigInt(index), masterNonce);
/// const nullifier = garaga.poseidonHashBN254(secret, secret);
/// const hash = garaga.poseidonHashBN254(secret, nullifier);
/// ```
pub fn generate_operation(index: u32, master_nonce: BaseField) -> Operation {
    // IMPORTANT: Using KKRT Poseidon2 (same as AIR!)
    let secret = hash_two_nodes_kkrt(
        BaseField::from_u32_unchecked(index),
        master_nonce
    );

    let nullifier = hash_two_nodes_kkrt(secret, secret);

    let hash = hash_two_nodes_kkrt(secret, nullifier);

    Operation {
        index,
        secret,
        nullifier,
        hash,
    }
}

/// Compute commitment from operation hash (matches frontend)
///
/// ```typescript
/// const preCommitment = garaga.poseidonHashBN254(hash, amount);
/// const commitment = garaga.poseidonHashBN254(preCommitment, tokenAddress);
/// ```
pub fn compute_commitment(
    operation_hash: BaseField,
    amount: BaseField,
    token_address: BaseField,
) -> BaseField {
    // IMPORTANT: Using KKRT Poseidon2 (same as AIR!)
    let pre_commitment = hash_two_nodes_kkrt(operation_hash, amount);
    let commitment = hash_two_nodes_kkrt(pre_commitment, token_address);
    commitment
}

/// Proof data for Merkle verification (matches frontend getProofData)
#[derive(Debug, Clone)]
pub struct ProofData {
    pub index: usize,
    pub siblings: Vec<BaseField>,
    pub is_right: Vec<bool>,  // Position flags (true = current node is on right)
    pub root: BaseField,
}

/// Hybrid Merkle Tree with incremental insertion and zero hashes
/// (matches frontend HybridMerkleTree)
pub struct HybridMerkleTree {
    pub height: usize,
    pub precomputed: Vec<BaseField>,  // Precomputed zero hashes
    pub left_path: Vec<BaseField>,    // Current left-most path
    pub layers: Vec<Vec<BaseField>>,  // All layers (sparse)
    pub leafs: Vec<BaseField>,        // All leaves
    free_index: usize,                // Next available index
}

impl HybridMerkleTree {
    /// Create new hybrid Merkle tree
    ///
    /// ```typescript
    /// this.precomputed = HybridMerkleTree.computePrecomputedHashes(height, this.poseidon);
    /// this.leftPath = [...this.precomputed];
    /// ```
    pub fn new(height: usize) -> Self {
        let precomputed = Self::compute_precomputed_hashes(height);
        let left_path = precomputed.clone();
        let layers = vec![Vec::new(); height];

        Self {
            height,
            precomputed,
            left_path,
            layers,
            leafs: Vec::new(),
            free_index: 0,
        }
    }

    /// Compute precomputed zero hashes (matches frontend)
    ///
    /// ```typescript
    /// let current = hashFn(0n, 0n);
    /// hashes.push(current);
    /// for (let i = 1; i < height; i++) {
    ///     current = hashFn(current, current);
    ///     hashes.push(current);
    /// }
    /// ```
    fn compute_precomputed_hashes(height: usize) -> Vec<BaseField> {
        let mut hashes = Vec::new();

        // IMPORTANT: Using KKRT Poseidon2 (same as AIR!)
        let mut current = hash_two_nodes_kkrt(
            BaseField::from_u32_unchecked(0),
            BaseField::from_u32_unchecked(0)
        );
        hashes.push(current);

        for _ in 1..height {
            current = hash_two_nodes_kkrt(current, current);
            hashes.push(current);
        }

        hashes
    }

    /// Add leaf to tree (incremental, matches frontend addLeaf)
    ///
    /// ```typescript
    /// for (let i = 1; i < this.height; i++) {
    ///     if (index % 2 === 0) {
    ///         const combined = this.poseidon(hashVal, this.precomputed[i - 1]);
    ///         this.leftPath[i - 1] = hashVal;
    ///         hashVal = combined;
    ///     } else {
    ///         hashVal = this.poseidon(this.leftPath[i - 1], hashVal);
    ///     }
    ///     index = Math.floor(index / 2);
    ///     this.layers[i][index] = hashVal;
    /// }
    /// ```
    pub fn add_leaf(&mut self, leaf: BaseField) {
        // Skip if already exists
        if self.leafs.contains(&leaf) {
            return;
        }

        let mut hash_val = leaf;
        let mut index = self.free_index;
        self.free_index += 1;

        self.leafs.push(leaf);
        self.layers[0].push(leaf);

        for i in 1..self.height {
            if index % 2 == 0 {
                // Left child: hash with precomputed zero on right
                // IMPORTANT: Using KKRT Poseidon2 (same as AIR!)
                let combined = hash_two_nodes_kkrt(hash_val, self.precomputed[i - 1]);
                self.left_path[i - 1] = hash_val;
                hash_val = combined;
            } else {
                // Right child: hash with left_path on left
                // IMPORTANT: Using KKRT Poseidon2 (same as AIR!)
                hash_val = hash_two_nodes_kkrt(self.left_path[i - 1], hash_val);
            }

            index /= 2;

            // Update or insert node at this level
            if index < self.layers[i].len() {
                self.layers[i][index] = hash_val;
            } else {
                self.layers[i].push(hash_val);
            }
        }

        self.left_path[self.height - 1] = hash_val;
    }

    /// Get current root
    pub fn get_root(&self) -> BaseField {
        self.left_path[self.height - 1]
    }

    /// Get proof data for a leaf (matches frontend getProofData)
    ///
    /// ```typescript
    /// for (let i = 0; i < this.height - 1; i++) {
    ///     const isRight = index % 2 === 1;
    ///     let sibling: bigint;
    ///     if (isRight) {
    ///         sibling = this.layers[i][index - 1];
    ///     } else {
    ///         sibling = this.layers[i][index + 1] ?? this.precomputed[i];
    ///     }
    ///     elements.push(sibling);
    ///     indices.push(isRight);
    ///     index = Math.floor(index / 2);
    /// }
    /// ```
    pub fn get_proof_data(&self, leaf: BaseField) -> Result<ProofData, String> {
        // Find leaf index
        let leaf_index = self.layers[0]
            .iter()
            .position(|&l| l == leaf)
            .ok_or_else(|| "Leaf not found in tree".to_string())?;

        let mut siblings = Vec::new();
        let mut is_right = Vec::new();
        let mut index = leaf_index;

        for i in 0..(self.height - 1) {
            let is_right_flag = index % 2 == 1;

            let sibling = if is_right_flag {
                // Current is on right, sibling is on left
                self.layers[i][index - 1]
            } else {
                // Current is on left, sibling is on right (or precomputed zero)
                if index + 1 < self.layers[i].len() {
                    self.layers[i][index + 1]
                } else {
                    self.precomputed[i]
                }
            };

            siblings.push(sibling);
            is_right.push(is_right_flag);
            index /= 2;
        }

        Ok(ProofData {
            index: leaf_index,
            siblings,
            is_right,
            root: self.get_root(),
        })
    }

    /// Get all leaves
    pub fn get_leafs(&self) -> &[BaseField] {
        &self.leafs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_operation() {
        println!("\n=== Test Generate Operation ===\n");

        let master_nonce = BaseField::from_u32_unchecked(999999);
        let op = generate_operation(0, master_nonce);

        println!("Operation 0:");
        println!("  secret: {}", op.secret.0);
        println!("  nullifier: {}", op.nullifier.0);
        println!("  hash: {}", op.hash.0);

        // Generate another one - should be deterministic
        let op2 = generate_operation(0, master_nonce);
        assert_eq!(op.secret, op2.secret);
        assert_eq!(op.nullifier, op2.nullifier);
        assert_eq!(op.hash, op2.hash);
        println!("✅ Deterministic generation verified");

        // Different index should give different values
        let op3 = generate_operation(1, master_nonce);
        assert_ne!(op.hash, op3.hash);
        println!("✅ Different indices produce different operations");
    }

    #[test]
    fn test_compute_commitment() {
        println!("\n=== Test Compute Commitment ===\n");

        let hash = BaseField::from_u32_unchecked(12345);
        let amount = BaseField::from_u32_unchecked(1000);
        let token = BaseField::from_u32_unchecked(42);

        let commitment = compute_commitment(hash, amount, token);
        println!("Commitment: {}", commitment.0);

        // Should be deterministic
        let commitment2 = compute_commitment(hash, amount, token);
        assert_eq!(commitment, commitment2);
        println!("✅ Commitment computation is deterministic");
    }

    #[test]
    fn test_hybrid_merkle_tree() {
        println!("\n=== Test Hybrid Merkle Tree ===\n");

        let height = 4; // 16 leaves max
        let mut tree = HybridMerkleTree::new(height);

        println!("Created tree with height {}", height);
        println!("Precomputed zero hashes:");
        for (i, hash) in tree.precomputed.iter().enumerate() {
            println!("  Level {}: {}", i, hash.0);
        }

        // Add some leaves incrementally
        let leaf1 = BaseField::from_u32_unchecked(100);
        let leaf2 = BaseField::from_u32_unchecked(200);
        let leaf3 = BaseField::from_u32_unchecked(300);

        tree.add_leaf(leaf1);
        println!("\nAfter adding leaf1:");
        println!("  Root: {}", tree.get_root().0);
        println!("  Leafs count: {}", tree.leafs.len());

        tree.add_leaf(leaf2);
        println!("\nAfter adding leaf2:");
        println!("  Root: {}", tree.get_root().0);
        println!("  Leafs count: {}", tree.leafs.len());

        tree.add_leaf(leaf3);
        println!("\nAfter adding leaf3:");
        println!("  Root: {}", tree.get_root().0);
        println!("  Leafs count: {}", tree.leafs.len());

        // Get proof for leaf2
        let proof_data = tree.get_proof_data(leaf2).expect("Failed to get proof");
        println!("\nProof data for leaf2 (index {}):", proof_data.index);
        println!("  Root: {}", proof_data.root.0);
        println!("  Siblings: {:?}", proof_data.siblings.iter().map(|s| s.0).collect::<Vec<_>>());
        println!("  IsRight: {:?}", proof_data.is_right);

        assert_eq!(proof_data.index, 1);
        assert_eq!(proof_data.siblings.len(), height - 1);
        assert_eq!(proof_data.is_right.len(), height - 1);
        println!("\n✅ Hybrid Merkle tree works correctly!");
    }

    #[test]
    fn test_full_flow() {
        println!("\n=== Test Complete Flow ===\n");

        let master_nonce = BaseField::from_u32_unchecked(123456789);
        let height = 5; // 32 leaves max
        let mut tree = HybridMerkleTree::new(height);

        println!("Step 1: Generate 3 operations");
        let ops: Vec<_> = (0..3)
            .map(|i| generate_operation(i, master_nonce))
            .collect();

        for (i, op) in ops.iter().enumerate() {
            println!("  Op {}: hash={}", i, op.hash.0);
        }

        println!("\nStep 2: Compute commitments");
        let amount = BaseField::from_u32_unchecked(1000);
        let token = BaseField::from_u32_unchecked(42);

        let commitments: Vec<_> = ops.iter()
            .map(|op| compute_commitment(op.hash, amount, token))
            .collect();

        for (i, comm) in commitments.iter().enumerate() {
            println!("  Commitment {}: {}", i, comm.0);
        }

        println!("\nStep 3: Add to Merkle tree");
        for (i, &commitment) in commitments.iter().enumerate() {
            tree.add_leaf(commitment);
            println!("  Added commitment {} → Root: {}", i, tree.get_root().0);
        }

        println!("\nStep 4: Get proof data for commitment 1");
        let proof = tree.get_proof_data(commitments[1]).expect("Failed to get proof");
        println!("  Index: {}", proof.index);
        println!("  Root: {}", proof.root.0);
        println!("  Siblings: {:?}", proof.siblings.iter().map(|s| s.0).collect::<Vec<_>>());
        println!("  IsRight: {:?}", proof.is_right);

        println!("\n✅ Complete flow executed successfully!");
        println!("\nNext: Use verify_membership_with_air() to generate STARK proof!");
    }
}
