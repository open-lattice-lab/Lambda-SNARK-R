# S3 Forking Lemma Infrastructure Research
**Date**: November 16, 2025  
**Objective**: Determine if Mathlib Probability API sufficient for forking_lemma proof  
**Estimate**: 1-2h research → 20h implementation

---

## Mathlib Probability API Survey

### Available Modules
✅ **ProbabilityMassFunction** (`Mathlib/Probability/ProbabilityMassFunction/`)
- `Basic.lean`: PMF definition, support, sum = 1
- `Monad.lean`: `pure`, `bind` operations
- `Constructions.lean`: PMF combinators
- `Binomial.lean`: Binomial distribution

✅ **Measure Theory** (`Mathlib/Probability/`)
- `ConditionalProbability.lean`: `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`, Bayes' theorem
- `Notation.lean`: `μ[|s]` and `μ[t|s]` notations
- `Integration.lean`, `Variance.lean`: Statistical properties

❌ **Cryptographic Primitives** (not found):
- No forking lemma infrastructure
- No rewinding/replay mechanisms
- No challenge-response transcript types
- No success amplification lemmas (ε² bounds)

### Key APIs for Forking Lemma

#### 1. PMF Support and Summation ✅
```lean
def PMF.support (p : PMF α) : Set α := Function.support p
theorem hasSum_coe_one (p : PMF α) : HasSum p 1
theorem tsum_coe (p : PMF α) : ∑' a, p a = 1
```
**Use case**: Define success probability over random choices.

#### 2. PMF Bind (Monadic Composition) ✅
```lean
def bind (p : PMF α) (f : α → PMF β) : PMF β
```
**Use case**: Sequential probability (first challenge α, then response given α).

#### 3. Conditional Probability ✅
```lean
-- μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)
-- μ[|s∩t] = μ[|s][|t]  (conditioning composition)
```
**Use case**: `Pr[extract success | first run success]`.

#### 4. Missing: Cryptographic Transcript Types ❌
**Need custom definitions**:
```lean
structure Transcript (F : Type) [CommRing F] where
  commitment : VectorCommitment.Commitment
  challenge : F
  response : Polynomial F
```

#### 5. Missing: Rewinding Infrastructure ❌
**Need custom definitions**:
```lean
def rewind (A : Adversary F VC) (c : Commitment) : 
  (challenge : F) → PMF (F × Response)
```

#### 6. Missing: Success Amplification (ε² bound) ❌
**Need custom lemma**:
```lean
theorem forking_success_bound :
  ∀ε > 0, Pr[first_success] ≥ ε → 
  Pr[second_success_different_challenge] ≥ ε²/2 - negl(secParam)
```

---

## Decision: Custom Mini-Library Required

### Scope (50-80 lines)
1. **Transcript type** (10 lines): commitment × challenge × response
2. **Rewinding function** (15-20 lines): adversary replay with new challenge
3. **Success event definitions** (10 lines): `first_success`, `fork_success`
4. **Probability bounds** (20-30 lines): ε² - negl(λ) via Schwartz-Zippel
5. **Extraction logic** (10 lines): two transcripts → witness

### Rationale
- Mathlib has **primitives** (PMF, conditional prob, measure theory) ✅
- Mathlib lacks **crypto-specific structures** (transcripts, rewinding) ❌
- Custom library **reuses Mathlib** (composition, not reinvention)
- Estimate: **5-8h** for infrastructure + **12-15h** for forking_lemma proof

---

## Proof Strategy for S3 Forking Lemma

### Statement
```lean
theorem forking_lemma {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (VC : VectorCommitment F) (cs : R1CS F)
    (A : Adversary F VC) (ε : ℝ) (secParam : ℕ)
    (h_success : ε ≥ 1 / (secParam ^ 2 : ℝ))  -- Non-negligible
    (h_sis : ModuleSIS_Hard 256 2 12289 1024)
    :
    ∃ (E : Extractor F VC),
      ∀ (x : PublicInput F cs.nPub),
        -- If adversary produces valid proof with prob ε
        (∃ π, verify VC cs x π = true) →
        -- Extractor finds witness with prob ≥ ε² - negl(λ)
        (∃ w, satisfies cs w ∧ extractPublic cs.h_pub_le w = x)
```

### Proof Sketch (Step-by-Step)

#### Phase 1: Transcript Infrastructure (5-8h)

**1.1 Define Transcript Type**
```lean
structure Transcript (F : Type) [CommRing F] (VC : VectorCommitment F) where
  -- Commitment to witness polynomials (Az, Bz, Cz, quotient)
  comm_Az : VC.Commitment
  comm_Bz : VC.Commitment
  comm_Cz : VC.Commitment
  comm_quotient : VC.Commitment
  
  -- Fiat-Shamir challenge (random oracle)
  challenge_α : F
  
  -- Response: polynomial openings
  opening_Az : VC.Opening
  opening_Bz : VC.Opening
  opening_quotient : VC.Opening
  
  -- Verification status
  valid : Bool
```

**1.2 Define Adversary State Machine**
```lean
structure AdversaryState (F : Type) [CommRing F] (VC : VectorCommitment F) where
  -- Internal randomness
  randomness : ℕ
  
  -- Committed values (before challenge)
  commitments : (VC.Commitment × VC.Commitment × VC.Commitment × VC.Commitment)
  
  -- Response function (after challenge)
  respond : F → (VC.Opening × VC.Opening × VC.Opening)
```

**1.3 Run Adversary (First Execution)**
```lean
def run_adversary (A : Adversary F VC) (cs : R1CS F) (x : PublicInput F cs.nPub)
    : PMF (Transcript F VC) := do
  -- Sample randomness
  let r ← uniform_pmf (range secParam)
  
  -- Get commitments (deterministic given r)
  let comms := A.commit cs x r
  
  -- Sample challenge from random oracle
  let α ← uniform_pmf (Finset.univ : Finset F)
  
  -- Get response
  let openings := A.respond comms α
  
  -- Build transcript
  return {
    comm_Az := comms.1,
    comm_Bz := comms.2,
    comm_Cz := comms.3,
    comm_quotient := comms.4,
    challenge_α := α,
    opening_Az := openings.1,
    opening_Bz := openings.2,
    opening_quotient := openings.3,
    valid := verify VC cs x (build_proof comms α openings)
  }
```

**1.4 Rewinding (Second Execution with Different Challenge)**
```lean
def rewind_adversary (A : Adversary F VC) (cs : R1CS F) (x : PublicInput F cs.nPub)
    (first_transcript : Transcript F VC)
    : PMF (Transcript F VC) := do
  -- Reuse same randomness → same commitments
  let r := first_transcript.randomness
  let comms := (first_transcript.comm_Az, first_transcript.comm_Bz, 
                first_transcript.comm_Cz, first_transcript.comm_quotient)
  
  -- Sample NEW challenge α' ≠ α
  let α' ← uniform_pmf_ne first_transcript.challenge_α
  
  -- Get response for NEW challenge
  let openings' := A.respond comms α'
  
  return {
    comm_Az := comms.1,
    comm_Bz := comms.2,
    comm_Cz := comms.3,
    comm_quotient := comms.4,
    challenge_α := α',
    opening_Az := openings'.1,
    opening_Bz := openings'.2,
    opening_quotient := openings'.3,
    valid := verify VC cs x (build_proof comms α' openings')
  }
```

#### Phase 2: Probability Bounds (6-8h)

**2.1 First Success Probability**
```lean
-- Given: adversary succeeds with prob ≥ ε
axiom first_success_prob (A : Adversary F VC) (cs : R1CS F) (x : PublicInput F cs.nPub) :
  (run_adversary A cs x).support.filter (fun t => t.valid = true)).card / 
  (Fintype.card F) ≥ ε
```

**2.2 Heavy Row Lemma (Forking Core)**
```lean
-- If first success prob ≥ ε, then fraction of "good" commitments ≥ ε - 1/|F|
lemma heavy_row_exists (A : Adversary F VC) (ε : ℝ) (h_ε : ε ≥ 1 / (secParam^2 : ℝ)) :
  ∃ (good_commitments : Finset (Commitment × Commitment × Commitment × Commitment)),
    good_commitments.card ≥ ε * (Fintype.card (range secParam)) ∧
    ∀ comms ∈ good_commitments, 
      -- For each good commitment, many challenges lead to valid proofs
      (Finset.univ.filter (fun α => verify_with_commitment comms α)).card ≥ ε * (Fintype.card F)
```

**2.3 Fork Success Probability (ε²/2 bound)**
```lean
-- Given good commitment, prob of fork (two different α, both valid) ≥ ε²/2
lemma fork_success_bound (comms : CommitmentTuple) 
    (h_good : comms ∈ good_commitments) :
  let valid_challenges := Finset.univ.filter (fun α => verify_with_commitment comms α)
  -- Sample two distinct challenges from valid set
  (valid_challenges.card.choose 2) / (Fintype.card F).choose 2 ≥ ε² / 2 := by
  -- Proof: |valid_challenges| ≥ ε|F|
  -- Choose 2 from ≥ ε|F| items: (ε|F| choose 2) / (|F| choose 2) ≈ ε²/2
  sorry  -- Combinatorial calculation
```

**2.4 Negligible Error Term**
```lean
-- Account for Schwartz-Zippel collision probability
lemma negligible_error_term (secParam : ℕ) :
  1 / (Fintype.card F : ℝ) ≤ 1 / (secParam ^ 3 : ℝ) := by
  -- F = Z_q with q ≥ 2^secParam (from parameter choice)
  sorry  -- Field size calculation
```

#### Phase 3: Witness Extraction (4-6h)

**3.1 Quotient Polynomial Difference**
```lean
-- Given two valid transcripts with different challenges
def extract_quotient_diff (t1 t2 : Transcript F VC) 
    (h_same_comm : t1.comm_quotient = t2.comm_quotient)
    (h_diff_challenge : t1.challenge_α ≠ t2.challenge_α)
    (h_valid : t1.valid = true ∧ t2.valid = true)
    : Polynomial F := by
  -- From verification equations:
  -- q₁(α₁) * Z_H(α₁) = constraint_poly(α₁)
  -- q₂(α₂) * Z_H(α₂) = constraint_poly(α₂)
  -- If q₁ = q₂ (same commitment), then constraint_poly(α₁) = constraint_poly(α₂)
  -- But α₁ ≠ α₂ → contradiction if constraint_poly is low-degree
  -- Therefore: commitment binding forces q₁ = q₂ = constraint_poly / Z_H
  sorry
```

**3.2 Witness Recovery**
```lean
-- Quotient polynomial coefficients encode witness
def extract_witness (q : Polynomial F) (cs : R1CS F) : Witness F cs.nVars := by
  -- Witness is encoded in polynomial evaluations over domain H = {ωⁱ}
  -- Lagrange interpolation: w(i) = q(ωⁱ) for i ∈ [0, n)
  sorry
```

**3.3 Soundness via Module-SIS Reduction**
```lean
-- If adversary produces two valid transcripts with prob ≥ ε²/2,
-- then extracted witness satisfies R1CS (else breaks Module-SIS)
lemma extraction_soundness (t1 t2 : Transcript F VC) 
    (h_fork : fork_conditions t1 t2)
    (h_sis : ModuleSIS_Hard 256 2 12289 1024) :
  let w := extract_witness (extract_quotient_diff t1 t2) cs
  satisfies cs w := by
  -- Proof by contradiction:
  -- If ¬(satisfies cs w), then constraint_poly ≠ 0 at some point
  -- But verification passed → commitment opened to constraint_poly
  -- Binding property → commitment collision → breaks Module-SIS
  sorry
```

#### Phase 4: Final Assembly (2-3h)

**4.1 Extractor Construction**
```lean
def forking_extractor (A : Adversary F VC) : Extractor F VC := {
  extract := fun A cs x => do
    -- Run adversary first time
    let t1 ← run_adversary A cs x
    if ¬t1.valid then return none
    
    -- Rewind with different challenge
    let t2 ← rewind_adversary A cs x t1
    if ¬t2.valid then return none
    if t2.challenge_α = t1.challenge_α then return none  -- Bad luck
    
    -- Extract witness
    let q := extract_quotient_diff t1 t2
    let w := extract_witness q cs
    return some w
  
  poly_time := by
    -- Runtime = 2 × adversary_time + poly(secParam) for extraction
    sorry
}
```

**4.2 Success Probability Theorem**
```lean
theorem forking_success_probability (A : Adversary F VC) (ε : ℝ) :
  (run_adversary A cs x).support.filter (fun t => t.valid)).card / (Fintype.card F) ≥ ε →
  (forking_extractor A).extract A cs x ≠ none with probability ≥ ε² / 2 - 1/(secParam^3) := by
  intro h_first_success
  -- Apply heavy_row_exists → good commitments exist
  obtain ⟨good_comms, h_heavy, h_many_valid⟩ := heavy_row_exists A ε h_ε
  -- Apply fork_success_bound → second challenge also succeeds
  have h_fork := fork_success_bound good_comms h_many_valid
  -- Negligible error from Schwartz-Zippel
  have h_negl := negligible_error_term secParam
  -- Combine bounds
  calc 
    Pr[extract ≠ none] = Pr[first success] * Pr[second success | first success]
    _ ≥ ε * (ε - 1/|F|)  -- by h_fork
    _ ≥ ε² - ε/|F|
    _ ≥ ε² / 2 - 1/(secParam^3)  -- when ε ≥ 1/secParam²
```

---

## Implementation Plan

### Week 1 (8h): Infrastructure
- [ ] Define Transcript, AdversaryState types (2h)
- [ ] Implement run_adversary, rewind_adversary (3h)
- [ ] Define uniform_pmf, uniform_pmf_ne combinators (2h)
- [ ] Basic PMF lemmas (support filtering) (1h)

### Week 2 (6h): Probability Bounds
- [ ] Heavy row lemma (3h)
- [ ] Fork success bound (2h)
- [ ] Negligible error calculation (1h)

### Week 3 (6h): Extraction Logic
- [ ] extract_quotient_diff implementation (2h)
- [ ] extract_witness via Lagrange interpolation (2h)
- [ ] Soundness reduction to Module-SIS (2h)

### Total: 20h

---

## Conclusion

**Decision**: Implement custom 50-80 line mini-library on top of Mathlib.

**Justification**:
- Mathlib provides **foundation** (PMF, conditional prob, measure theory) ✅
- Cryptographic **structures missing** (transcripts, rewinding, forking) ❌
- Custom library **composes with Mathlib** (not parallel infrastructure)
- Estimate realistic: **5-8h infra + 12-15h proof = 20h total**

**Next action**: Begin Phase 1 (Transcript infrastructure) in next session.

---

**Author**: URPKS Research Log  
**Status**: Research complete, ready for implementation ✅
