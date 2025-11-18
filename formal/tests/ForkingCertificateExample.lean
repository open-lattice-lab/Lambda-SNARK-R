/-
Example instantiation showing how to provide verifier equations for a
forked pair of transcripts. The goal is purely illustrative and uses a
minimal dummy vector commitment together with a trivial R1CS instance.
-/

import LambdaSNARK.ForkingInfrastructure
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic

namespace LambdaSNARK.Tests

open LambdaSNARK Polynomial

/-- Dummy vector commitment where the commitment is simply the underlying list. -/
noncomputable def dummyVC (F : Type) [CommRing F] : VectorCommitment F where
  PP := Unit
  Commitment := List F
  Opening := Unit
  setup _ := ()
  commit _ v _ := v
  openProof _ _ _ _ := ()
  verify _ _ _ _ _ := true
  binding := by
    intro _ v₁ v₂ _ _ h_ne h_commit
    simpa [commit] using congrArg id h_commit
  correctness := by intro pp v r α; simp [commit, openProof]

instance : CommRing (ZMod 2) := inferInstance

/-- Sparse matrix with a single row/column filled with zeros. -/
def trivialSparseMatrix : SparseMatrix (ZMod 2) where
  nRows := 1
  nCols := 1
  entries := []

def trivialR1CS : R1CS (ZMod 2) where
  nVars := 1
  nCons := 1
  nPub := 0
  A := trivialSparseMatrix
  B := trivialSparseMatrix
  C := trivialSparseMatrix
  h_dim_A := by simp [trivialSparseMatrix]
  h_dim_B := by simp [trivialSparseMatrix]
  h_dim_C := by simp [trivialSparseMatrix]
  h_pub_le := by decide

noncomputable def tStub : Transcript (ZMod 2) (dummyVC (ZMod 2)) :=
{ pp := ()
  cs := trivialR1CS
  x := fun i => by cases i
  domainSize := 1
  omega := 1
  comm_Az := []
  comm_Bz := []
  comm_Cz := []
  comm_quotient := []
  quotient_poly := 0
  quotient_rand := 0
  quotient_commitment_spec := by simp [Polynomial.coeffList_zero, dummyVC]
  view := {
    alpha := 0
    Az_eval := 0
    Bz_eval := 0
    Cz_eval := 0
    quotient_eval := 0
    vanishing_eval := 0
    main_eq := verifierView_zero_eq (F := ZMod 2)
  }
  challenge_β := 0
  opening_Az_α := ()
  opening_Bz_β := ()
  opening_Cz_α := ()
  opening_quotient_α := ()
  valid := true }

noncomputable def tStubFork : Transcript (ZMod 2) (dummyVC (ZMod 2)) :=
{ tStub with
  view := { tStub.view with alpha := 1,
    main_eq := verifierView_zero_eq (F := ZMod 2) } }

lemma stub_is_valid_fork :
    is_valid_fork (dummyVC (ZMod 2)) tStub tStubFork := by
  classical
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro HEq.rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro ?_ ?_
  · decide
  · exact And.intro rfl rfl
lemma stub_quotient_diff_zero :
    extract_quotient_diff (dummyVC (ZMod 2)) trivialR1CS tStub tStubFork
      stub_is_valid_fork 1 1 = 0 := rfl

lemma stub_constraint_zero (x : PublicInput (ZMod 2) trivialR1CS.nPub)
    (i : Fin trivialR1CS.nCons) :
    constraintPoly trivialR1CS
      (extract_witness (dummyVC (ZMod 2)) trivialR1CS
        (extract_quotient_diff (dummyVC (ZMod 2)) trivialR1CS tStub tStubFork
          stub_is_valid_fork 1 1)
        1 1 (by decide) x) i = 0 := by
  classical
  have : (i : ℕ) = 0 := by decide
  dsimp [constraintPoly, extract_witness]
  simp [this]

noncomputable def stubEquations :
    ForkingVerifierEquations (dummyVC (ZMod 2)) trivialR1CS tStub tStubFork
      stub_is_valid_fork :=
{ m := 1
  ω := 1
  h_m_vars := by decide
  h_m_cons := rfl
  h_primitive := IsPrimitiveRoot.one
  quotient_eval := by
    intro x i
    have h_eval : (extract_quotient_diff (dummyVC (ZMod 2)) trivialR1CS tStub tStubFork
        stub_is_valid_fork 1 1).eval (1 ^ (i : ℕ)) = 0 := by
      simpa [stub_quotient_diff_zero]
    simpa [stub_constraint_zero x i, h_eval]
  remainder_zero := by
    simpa [stub_quotient_diff_zero] }

lemma stub_extraction_soundness
    (x : PublicInput (ZMod 2) trivialR1CS.nPub)
    (h_sis : ModuleSIS_Hard 256 2 12289 1024) :
    satisfies trivialR1CS
      (extract_witness (dummyVC (ZMod 2)) trivialR1CS
        (extract_quotient_diff (dummyVC (ZMod 2)) trivialR1CS tStub tStubFork
          stub_is_valid_fork stubEquations.m stubEquations.ω)
        stubEquations.m stubEquations.ω stubEquations.h_m_vars x) :=
  extraction_soundness (VC := dummyVC (ZMod 2)) (t1 := tStub) (t2 := tStubFork)
    trivialR1CS stub_is_valid_fork stubEquations h_sis x

end LambdaSNARK.Tests

end LambdaSNARK.Tests
