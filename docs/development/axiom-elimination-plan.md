# Axiom Elimination Roadmap (Lean Core)

_Last updated: 2025-11-17_

The current Lean proof stack for ΛSNARK-R still depends on several crypto/analysis
axioms. This document is the live tracker for replacing them with constructive
proofs, aligned with the “variant 1” plan (remove axioms in Lean first, then sync
with Rust test vectors).

## Overview

| Axiom | Location | Role | Status | Planned Replacement |
|-------|----------|------|--------|---------------------|
| `heavy_row_lemma` | `LambdaSNARK/ForkingInfrastructure.lean` | Probabilistic heavy row argument | OPEN | Construct PMF-based proof using `uniform_pmf` + counting lemmas |
| `fork_success_bound` | `LambdaSNARK/ForkingInfrastructure.lean` | Lower bound on fork probability | OPEN | Derive from `heavy_row_lemma` + combinatorial bounds (`Nat.choose`) |
| `extraction_soundness` | `LambdaSNARK/ForkingInfrastructure.lean` | Shows extracted witness satisfies R1CS | OPEN | Reduce to verifier-equation certificate (`ForkingVerifierEquations`); construct `ForkingEquationsProvider` from protocol equations |

_No additional axioms are present in `Soundness.lean`; probabilistic facts there
forward references the axioms above._

## Work Packages

1. **Extraction Soundness (P0 priority)**
   - Inputs: transcripts forming valid fork, `quotient_poly_eq_of_fork`.
   - Required lemmas:
     - `Polynomial.coeffList` ↔ evaluation bridge for quotient polynomial.
     - Normal form of R1CS evaluation (`constraintPoly`) vs commitment openings.
     - Vanishing polynomial properties (already in `Polynomial.lean`).
    - Progress:
       - Added Lean helper lemmas `extract_witness_public`, `extract_witness_private`,
          `extract_witness_public_prefix`, and reduction lemma
          `extraction_soundness_of_constraint_zero` to isolate the remaining goal.
       - `extract_witness` behaviour on public prefix now explicit (needed for
          bridging with transcript commitments).
    - Deliverables:
       - Replace `axiom extraction_soundness` with a proved theorem. ✅ *Now parameterised by `ForkingEquationsProvider`; the global axiom is removed.*
       - Unit test: instantiate simple R1CS (e.g., healthcare circuit) and verify
          extracted witness satisfies constraints. ✅ *See `formal/tests/ForkingCertificateExample.lean`.*

2. **Heavy Row Lemma (P1 priority)**
   - Goal: eliminate reliance on unproven combinatorial probability.
   - Steps:
     1. Build helper lemmas for `PMF` over finite types:
        `sum_const`, `map`, exclusion of one element (already started via
        `uniform_pmf` / `uniform_pmf_ne`).
     2. Formalize counting argument: many valid challenges ⇒ heavy commitment
        set size.
     3. Export final statement in existing signature (keep API stable).

3. **Fork Success Bound (P1 priority)**
   - Depends on (2).
   - Additional work: binomial coefficient inequalities (`Nat.choose` bounds).
   - Confirm compatibility with real-number coercions used in `Soundness.lean`.

## Milestones & Checks

- **M1**: `extraction_soundness` proven ⇒ `forking_lemma` uses no extraction
  axioms.
- **M2**: Both probabilistic lemmas proven ⇒ `forking_lemma` completely
  constructive.
- **M3**: `knowledge_soundness` depends only on documented algebraic assumptions
  (e.g., Module-SIS hardness), no Lean axioms.

## Immediate Next Actions

1. Instantiate `ForkingEquationsProvider` from real verifier equations (currently
   abstract parameter in theorems).
2. If required, extend `Transcript` or proof objects to expose missing
   evaluation data used in the certificate fields.
3. Introduce Lean test modules mirroring Rust healthcare circuit to act as proof
   witnesses once certificate construction is implemented (next target after the
   stub example).

Please keep this file up to date after each major step (PR/commit) to maintain
shared visibility on proof obligations.
