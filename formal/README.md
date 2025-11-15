# Lean 4 Formal Verification

This directory contains formal proofs of ΛSNARK-R properties in Lean 4.

## Structure

```
formal/
├── lakefile.lean          # Lake build configuration
├── Main.lean              # Entry point
├── LambdaSNARK.lean       # Root module
└── LambdaSNARK/
    ├── Core.lean          # Core definitions (R1CS, VectorCommitment, Proof)
    ├── Polynomial.lean    # Lagrange interpolation, polynomial division
    ├── Soundness.lean     # Knowledge soundness theorem + proof skeleton
    ├── Completeness.lean  # Completeness theorem
    └── ZeroKnowledge.lean # Zero-knowledge theorem (TODO)
```

## Building

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
lake build

# Check proofs
lake env lean LambdaSNARK/Soundness.lean
```

## Status

**Current (v0.1.0-alpha, M8 Phase 1 - November 15, 2025)**:
- ✅ Core definitions: R1CS, Witness, Satisfaction predicate
- ✅ VectorCommitment interface (binding, correctness properties)
- ✅ Proof structure (commitments, challenges, openings)
- ✅ Soundness statement (knowledge_soundness theorem)
- ✅ Forking lemma statement (rewinding extraction)
- ✅ Schwartz-Zippel lemma statement (polynomial identity testing)
- ✅ Completeness statement (perfect completeness)
- ✅ Polynomial operations (Lagrange interpolation, division by Z_H)
- ⏳ Soundness proof (detailed steps TODO, estimated 40-60h)
- ⏳ Completeness proof (detailed steps TODO, estimated 10-20h)
- ⏳ Polynomial lemmas (Lagrange correctness, quotient uniqueness)

**Target (v1.0.0, M8-M9 complete - Q1-Q2 2026)**:
- ✅ Soundness proof complete (under Module-SIS + ROM)
- ✅ Zero-knowledge proof complete (under Module-LWE + σ bounds)
- ✅ Completeness proof complete
- ✅ Polynomial lemmas proven (Lagrange, Schwartz-Zippel, division)
- ✅ Integration tests (extract VK as Lean terms, check against Rust/C++)
- ✅ CI verification (lake build + proof checking)

## Theorems

### Soundness (Knowledge Soundness)

```lean
theorem knowledge_soundness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (VC : VectorCommitment F) (cs : R1CS F) (λ : ℕ)
    (A : Adversary F VC) (ε : ℕ → ℝ)
    (h_non_negl : NonNegligible ε)  -- ε(λ) ≥ 1/poly(λ)
    (h_sis : ModuleSIS_Hard 256 2 12289 1024)  -- Module-SIS hardness
    (h_rom : True)  -- Random Oracle Model
    :
    ∃ (E : Extractor F VC),
      E.poly_time ∧  -- Extractor is PPT
      ∀ (x : PublicInput F cs.nPub),
        -- If adversary produces accepting proof
        (∃ π, verify VC cs x π = true) →
        -- Then extractor finds valid witness
        (∃ w : Witness F cs.nVars, 
          satisfies cs w ∧ 
          extractPublic (by omega) w = x)
```

**Proof Strategy**:
1. Apply forking lemma (rewind adversary with different challenges)
2. Extract two accepting transcripts with distinct challenges α ≠ α'
3. Compute witness from quotient polynomial difference q - q'
4. Verify extracted witness satisfies R1CS via Schwartz-Zippel

**Status**: Statement complete ✅, proof skeleton TODO ⏳

### Completeness (Perfect Completeness)

```lean
theorem completeness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (VC : VectorCommitment F) (cs : R1CS F) (λ : ℕ)
    (P : HonestProver F VC) 
    (h_correct : VC.correctness)  -- Commitment scheme is correct
    :
    ∀ (w : Witness F cs.nVars) (x : PublicInput F cs.nPub) (r : ℕ),
      -- If witness is valid
      satisfies cs w →
      extractPublic (by omega) w = x →
      -- Then proof verifies with probability 1
      verify VC cs x (P.prove cs w x r) = true
```

**Proof Strategy**:
1. Show polynomial construction Az, Bz, Cz is correct
2. Show quotient polynomial q exists (by satisfaction hypothesis)
3. Show commitment correctness (VC.correctness property)
4. Show all verifier checks pass deterministically

**Status**: Statement complete ✅, proof TODO ⏳

### Zero-Knowledge (Computational Hiding)

```lean
theorem zero_knowledge
  (pp : PP R) (vk : VK R)
  (h_lwe : ModuleLWE_Hard pp.vc_pp) :
  ∃ (Sim : Simulator), ∀ (D : Distinguisher),
    |Pr[D (Real vk)] - Pr[D (Sim vk)]| ≤ negl(λ)
```

**Status**: TODO (M9)

## References

- Lean 4 manual: https://leanprover.github.io/lean4/doc/
- Mathlib4: https://github.com/leanprover-community/mathlib4
- Functional correctness: https://lean-fro.org/
