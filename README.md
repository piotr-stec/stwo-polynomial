# STWO Polynomial Library

## Features

- **Prove**: Generate cryptographic proofs and return the composition polynomial
- **Verify**: Verify proofs using the composition polynomial
- **Composition Polynomial Access**: Get access to the underlying polynomial for advanced operations

## Usage

### Basic Example

```rust
use stwo_polynomial::{prove, verify};

// Generate proof
let (proof, composition_polynomial) = prove(components, &mut channel, commitment_scheme)?;

// Verify proof
verify(components, &mut channel, &mut verifier, proof, composition_polynomial)?;
```

## Examples

This library includes two example implementations:

### 1. Fibonacci Proof Generation

Demonstrates how to generate a proof for Fibonacci sequence computation.

```bash
cargo run --example prove_fibonacci
```

### 2. Fibonacci Proof Verification

Shows how to verify a previously generated Fibonacci proof.

```bash
cargo run --example verify_fibonacci
```

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
stwo-polynomial = { git = "https://github.com/your-repo/stwo-polynomial" }
```
