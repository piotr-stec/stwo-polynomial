# Fibonacci On-Chain Verification Example

This example demonstrates how to generate a STARK proof for Fibonacci sequence computation and verify it on-chain using a Solidity verifier contract.

## Overview

The example computes `f(10) = 55` using STARK proofs with the following flow:

1. **Generate Fibonacci Trace** - Creates execution trace with 3 columns [f(n-2), f(n-1), f(n)]
2. **Generate STARK Proof** - Proves correct computation using Keccak channel
3. **Verify Off-Chain** - Validates proof locally
4. **Convert to Solidity Format** - Transforms proof to contract-compatible format
5. **Prepare Verification Parameters** - Extracts component metadata
6. **Verify On-Chain** - Calls Solidity verifier contract via Alloy

## Key Features

- **Keccak Channel**: Uses Keccak256 for Fiat-Shamir (compatible with EVM)
- **Single Component**: Simple AIR with one constraint: `f(n) = f(n-1) + f(n-2)`
- **Zero Padding**: Unused trace rows are padded with zeros (satisfies `0 = 0 + 0`)
- **Alloy Integration**: Direct contract calls using Rust types

## Circuit Constraint

The AIR evaluates a single constraint per row:

```rust
eval.add_constraint(c - (a + b));
// Where: a = f(n-2), b = f(n-1), c = f(n)
```

## Configuration

```rust
let config = PcsConfig {
    pow_bits: 12,
    fri_config: StwoFriConfig::new(2, 2, 42),
};
// Security bits: ~96
```

## Running the Example

### Prerequisites

1. Start local Ethereum node (Anvil):
```bash
anvil
```

2. Deploy STWO verifier contract at address:
```
0xDc64a140Aa3E981100a9becA4E685f962f0cF6C9
```

### Execute

```bash
cargo run --example fibonacci_onchain
```

## Expected Output

```
🔢 Fibonacci On-Chain Verification Example
════════════════════════════════════════════

📝 Computing Fibonacci f(10) using STARK proof

📊 STEP 1: Generate Fibonacci Trace
  Trace size: 2^4 = 16 rows
  Target value f(10) = 55
  ✅ Trace generated

🔐 STEP 2: Generate STARK Proof
  Security bits: 96
  ✅ STARK proof generated

✅ STEP 3: Verify Proof (Off-Chain)
  Digest: 0x...
  Composition log degree bound: 5
  ✅ Off-chain verification successful

🔄 STEP 4: Convert Proof to Solidity Format
  ✅ Proof converted to Solidity format

📋 STEP 5: Prepare Verification Parameters
  Component log size: 4
  Max constraint log degree bound: 5
  ✅ Parameters prepared

🌐 STEP 6: Verify Proof On-Chain
  Simulating contract call...
  ✅ Contract call succeeded: 0x...

╔══════════════════════════════════════════════════════════╗
║              FIBONACCI ON-CHAIN COMPLETE ✅               ║
╚══════════════════════════════════════════════════════════╝

📊 Summary:
  Target: f(10) = 55
  Trace size: 2^4 = 16 rows
  Security bits: 96
  ✅ Off-chain verification: PASSED
  ✅ On-chain verification: CHECK ABOVE

🎉 Fibonacci STARK proof generated and verified!
```

## Comparison with Privacy Pools Example

| Feature | Fibonacci | Privacy Pools |
|---------|-----------|---------------|
| Components | 1 (Fibonacci) | 2 (Computing + Scheduler) |
| Constraints | 1 per row | Multiple (Merkle path verification) |
| Trace Columns | 3 (a, b, c) | Multiple per component |
| Complexity | Simple | Complex (cryptographic operations) |
| Use Case | Educational | Privacy-preserving transactions |

## Proof Structure

The Solidity proof contains:

- **Config**: PCS and FRI parameters
- **Commitments**: Merkle roots of trace polynomials
- **Sampled Values**: OODS evaluations (QM31 field elements)
- **Decommitments**: Merkle authentication paths
- **Queried Values**: FRI query values (M31 field elements)
- **Proof of Work**: Optional PoW nonce
- **FRI Proof**: FRI layers with commitments and witnesses
- **Composition Polynomial**: Combined constraint polynomial coefficients

## Contract Verification

The on-chain verifier performs:

1. **Merkle Tree Verification**: Validates trace commitments
2. **OODS Sampling**: Checks out-of-domain evaluations
3. **Constraint Evaluation**: Verifies AIR constraints at random point
4. **FRI Protocol**: Validates polynomial degree claims
5. **Composition Check**: Ensures all constraints are satisfied

## Error Handling

The example includes detailed error reporting:

```rust
match provider.call(&call_input).await {
    Ok(result) => println!("✅ Contract call succeeded"),
    Err(e) => {
        println!("❌ Contract call reverted: {}", e);
        if let Some(data) = e.as_error_resp() {
            println!("Revert data: {:?}", data);
        }
    }
}
```

## Extending the Example

To compute different Fibonacci numbers:

```rust
let target_n = 50; // Compute f(50)
```

Note: Larger `target_n` requires larger trace (higher `log_size`) which increases proof size and verification time.

## Technical Details

### Field Elements

- **M31**: Prime field modulo 2^31 - 1 (base field)
- **QM31**: Degree-4 extension field (secure field for composition)

### Trace Layout

```
Row | Col 0 (a) | Col 1 (b) | Col 2 (c) | Constraint
----|-----------|-----------|-----------|------------
 0  |    0      |    1      |    1      | 1 = 0 + 1 ✓
 1  |    1      |    1      |    2      | 2 = 1 + 1 ✓
 2  |    1      |    2      |    3      | 3 = 1 + 2 ✓
 3  |    2      |    3      |    5      | 5 = 2 + 3 ✓
 4  |    3      |    5      |    8      | 8 = 3 + 5 ✓
 5  |    5      |    8      |   13      | 13 = 5 + 8 ✓
 6  |    8      |   13      |   21      | 21 = 8 + 13 ✓
 7  |   13      |   21      |   34      | 34 = 13 + 21 ✓
 8  |   21      |   34      |   55      | 55 = 21 + 34 ✓ (f(10))
 9  |    0      |    0      |    0      | 0 = 0 + 0 ✓ (padding)
...
15  |    0      |    0      |    0      | 0 = 0 + 0 ✓ (padding)
```

### Component Metadata

```rust
ComponentInfo {
    maxConstraintLogDegreeBound: 5,  // 2^5 = 32 (constraint degree)
    logSize: 4,                        // 2^4 = 16 rows
    maskOffsets: [[[0, 1, 2]]],       // Read 3 consecutive values
    preprocessedColumns: [],           // No preprocessed columns
}
```

## References

- [STWO Prover](https://github.com/starkware-libs/stwo)
- [Circle STARKs](https://eprint.iacr.org/2024/278)
- [Alloy](https://github.com/alloy-rs/alloy)
- [FRI Protocol](https://drops.dagstuhl.de/opus/volltexte/2018/9018/)
