# ΛSNARK-R Test Vectors

Conformance test vectors for cross-language validation (C++ ↔ Rust).

## Structure

Each test vector contains:
- **params.json**: Public parameters (n, k, q, σ, security level)
- **input.json**: Public input (statement to prove)
- **witness.json**: Private witness (solution)
- **proof.json**: Expected proof artifact (serialized)
- **expected.json**: Expected verification result

## Test Vectors

### TV-0: Linear System Az = b
**Description**: Prove knowledge of solution z to linear system Az = b  
**Size**: 5×5 matrix, 5-element vector  
**Purpose**: Basic R1CS validation  
**File**: `tv-0-linear-system/`

### TV-1: Multiplication 7 × 13 = 91
**Description**: Prove knowledge of factorization of 91  
**Size**: 3 variables (1, a, b, c where a·b = c)  
**Purpose**: Simple R1CS gate  
**File**: `tv-1-multiplication/`

### TV-2: Plaquette Constraint
**Description**: Prove θ₁ + θ₂ - θ₃ - θ₄ = 0 (lattice gauge theory)  
**Size**: 4 angles on 2D plaquette  
**Purpose**: Physics application  
**File**: `tv-2-plaquette/`

## Usage

### Rust
```rust
use lambda_snark::{Params, setup, prove, verify};
use std::fs;

let params: Params = serde_json::from_str(
    &fs::read_to_string("test-vectors/tv-0-linear-system/params.json")?
)?;
let input: Vec<Field> = serde_json::from_str(
    &fs::read_to_string("test-vectors/tv-0-linear-system/input.json")?
)?;
let witness: Vec<Field> = serde_json::from_str(
    &fs::read_to_string("test-vectors/tv-0-linear-system/witness.json")?
)?;

let (pk, vk) = setup(params)?;
let proof = prove(&pk, &input, &witness)?;
let valid = verify(&vk, &input, &proof)?;
assert!(valid);
```

### C++
```cpp
#include "lambda_snark/commitment.h"
#include <nlohmann/json.hpp>

auto params = load_params("test-vectors/tv-0-linear-system/params.json");
auto ctx = lwe_context_create(&params);
// ... prove and verify
```

## Reproducibility

All test vectors use **fixed random seeds**:
- TV-0: seed = 0xDEADBEEF
- TV-1: seed = 0xCAFEBABE
- TV-2: seed = 0x8BADF00D

## Validation

Run all test vectors:
```bash
# Rust
cargo test --test conformance

# C++
cd cpp-core/build
ctest -R conformance
```
