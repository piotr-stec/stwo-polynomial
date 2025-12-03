//! Privacy Mixer - Production Implementation
//!
//! This implements a privacy mixer with KKRT-style Merkle trees:
//!
//! # Flow:
//!
//! 1. **Operation Generation**: Deterministic from master_nonce + index ``` secret = hash(index,
//!    master_nonce) nullifier = hash(secret, secret) hash = hash(secret, nullifier) ```
//!
//! 2. **Commitment Computation**: Two-stage hashing ``` pre_commitment = hash(operation_hash,
//!    amount) commitment = hash(pre_commitment, token_address) ```
//!
//! 3. **HybridMerkleTree**: Incremental insertion with precomputed zero hashes
//!    - Height 32 (can hold 2^31 leaves)
//!    - 32 precomputed zero hashes for sparse tree optimization
//!    - O(log n) insertion time
//!
//! 4. **Merkle Proof**: Get siblings path with position flags
//!
//! 5. **STARK Verification**: Using MerkleComputingComponent + MerkleSchedulerComponent
//!
//! # Components:
//!
//! - **MerkleComputingComponent**: Computes Merkle path (from parent module)
//! - **MerkleSchedulerComponent**: Verifies root equality (from parent module)
//! - Uses LogUp to connect components

// Complete flow (frontend-compatible)
pub mod full_flow;

// Complete end-to-end tests
pub mod complete_flow_test;

use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;

/// Statement for mixer (public inputs)
#[derive(Clone, Debug)]
pub struct MixerStatement {
    pub root: BaseField,              // Merkle root
    pub nullifier: BaseField,         // Nullifier (prevents double-spend)
    pub spent_amount: BaseField,      // Amount being withdrawn
    pub refund_commitment: BaseField, // New deposit commitment for change
}

impl MixerStatement {
    pub fn mix_into(&self, channel: &mut Blake2sChannel) {
        use stwo::core::channel::Channel;
        use stwo::core::fields::qm31::SecureField;

        channel.mix_felts(&[
            SecureField::from(self.root),
            SecureField::from(self.nullifier),
            SecureField::from(self.spent_amount),
            SecureField::from(self.refund_commitment),
        ]);
    }
}
