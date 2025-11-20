/-
Copyright (c) 2025 URPKS Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: URPKS Contributors
-/

import LambdaSNARK.Core
import LambdaSNARK.Polynomial
import LambdaSNARK.Constraints

/-!
# Forking Transcript Types

Shared data structures for the ΛSNARK forking analysis.  This module bundles the
transcript representation, adversary state snapshots and lightweight predicates
such as the success and fork events so that other components (probability layer,
infrastructure lemmas, extractor logic) can depend on a consistent interface.

## Main definitions

- `TranscriptView`: verifier-facing portion of an interaction transcript
- `Transcript`: full transcript produced by the adversary
- `AdversaryState`: internal state captured before the Fiat–Shamir challenge
- `transcriptCommitTuple`: helper extracting commitment quadruples
- `success_event`: predicate for transcript acceptance
- `fork_success_event`: predicate for two transcripts forming a fork
- `Adversary`: abstraction of a single-run adversary behaviour
-/

namespace LambdaSNARK

/-- View data revealed to the verifier during transcript validation. -/
structure TranscriptView (F : Type) where
  alpha : F
  Az_eval : F
  Bz_eval : F
  Cz_eval : F
  quotient_eval : F
  vanishing_eval : F
  main_eq : Prop

/-- Placeholder relation used while the verifier equations are not yet formalised. -/
def verifierView_zero_eq (_F : Type) : Prop := True

/-- Interactive proof transcript produced by the adversary and verifier. -/
structure Transcript (F : Type) [CommRing F] (VC : VectorCommitment F) where
  pp : VC.PP
  cs : R1CS F
  x : PublicInput F cs.nPub
  domainSize : ℕ
  omega : F
  comm_Az : VC.Commitment
  comm_Bz : VC.Commitment
  comm_Cz : VC.Commitment
  comm_quotient : VC.Commitment
  quotient_poly : Polynomial F
  quotient_rand : ℕ
  quotient_commitment_spec :
    VC.commit pp (Polynomial.coeffList quotient_poly) quotient_rand = comm_quotient
  view : TranscriptView F
  challenge_β : F
  opening_Az_α : VC.Opening
  opening_Bz_β : VC.Opening
  opening_Cz_α : VC.Opening
  opening_quotient_α : VC.Opening
  valid : Bool

/-- Evaluations and openings returned by the adversary when challenged. -/
structure AdversaryResponse (F : Type) [CommRing F] (VC : VectorCommitment F) where
  Az_eval : F
  Bz_eval : F
  Cz_eval : F
  quotient_eval : F
  vanishing_eval : F
  opening_Az_α : VC.Opening
  opening_Bz_β : VC.Opening
  opening_Cz_α : VC.Opening
  opening_quotient_α : VC.Opening

/-- Fork validity predicate: identical commitments but distinct challenges. -/
def is_valid_fork {F : Type} [CommRing F] [DecidableEq F] (VC : VectorCommitment F)
    (t1 t2 : Transcript F VC) : Prop :=
  t1.pp = t2.pp ∧
  t1.cs = t2.cs ∧
  HEq t1.x t2.x ∧
  t1.domainSize = t2.domainSize ∧
  t1.omega = t2.omega ∧
  t1.comm_Az = t2.comm_Az ∧
  t1.comm_Bz = t2.comm_Bz ∧
  t1.comm_Cz = t2.comm_Cz ∧
  t1.comm_quotient = t2.comm_quotient ∧
  t1.quotient_rand = t2.quotient_rand ∧
  t1.view.alpha ≠ t2.view.alpha ∧
  t1.valid = true ∧
  t2.valid = true

/-- Adversary's internal state after the commitment phase. -/
structure AdversaryState (F : Type) [CommRing F] (VC : VectorCommitment F) where
  randomness : ℕ
  pp : VC.PP
  comm_Az : VC.Commitment
  comm_Bz : VC.Commitment
  comm_Cz : VC.Commitment
  comm_quotient : VC.Commitment
  quotient_poly : Polynomial F
  quotient_rand : ℕ
  quotient_commitment_spec :
    VC.commit pp (Polynomial.coeffList quotient_poly) quotient_rand = comm_quotient
  domainSize : ℕ
  omega : F
  respond : F → F → AdversaryResponse F VC

/-- Extract the four Pedersen commitments that the adversary published before the challenge. -/
def AdversaryState.commitments {F : Type} [CommRing F] (VC : VectorCommitment F)
    (state : AdversaryState F VC) :
    VC.Commitment × VC.Commitment × VC.Commitment × VC.Commitment :=
  (state.comm_Az, state.comm_Bz, state.comm_Cz, state.comm_quotient)

/-- Project a transcript onto its commitment quadruple. -/
def transcriptCommitTuple {F : Type} [CommRing F] (VC : VectorCommitment F)
    (t : Transcript F VC) :
    VC.Commitment × VC.Commitment × VC.Commitment × VC.Commitment :=
  (t.comm_Az, t.comm_Bz, t.comm_Cz, t.comm_quotient)

/-- Project a transcript onto the pair of commitments and Fiat–Shamir challenge. -/
def transcriptCommitChallenge {F : Type} [CommRing F] (VC : VectorCommitment F)
    (t : Transcript F VC) :
    (VC.Commitment × VC.Commitment × VC.Commitment × VC.Commitment) × F :=
  (transcriptCommitTuple VC t, t.view.alpha)

/-- Predicate asserting that the transcript passes the verifier checks. -/
def success_event {F : Type} [Field F] [DecidableEq F]
    (VC : VectorCommitment F) (cs : R1CS F) (x : PublicInput F cs.nPub)
    (t : Transcript F VC) : Prop :=
  let _ := VC
  let _ := cs
  let _ := x
  t.valid = true

/-- Predicate for a pair of transcripts that both verify and disagree on the challenge. -/
def fork_success_event {F : Type} [Field F] [DecidableEq F]
    (VC : VectorCommitment F) (cs : R1CS F) (x : PublicInput F cs.nPub)
    (pair : Transcript F VC × Transcript F VC) : Prop :=
  success_event VC cs x pair.1 ∧ success_event VC cs x pair.2 ∧
    is_valid_fork VC pair.1 pair.2

/-- Adversary interface capturing single-run behaviour. -/
structure Adversary (F : Type) [CommRing F] (VC : VectorCommitment F) where
  run :
      (cs : R1CS F) →
      (x : PublicInput F cs.nPub) →
      (randomness : ℕ) →
      Proof F VC
  snapshot :
      (cs : R1CS F) →
      (x : PublicInput F cs.nPub) →
      (randomness : ℕ) →
      AdversaryState F VC
  poly_time : Prop

end LambdaSNARK
