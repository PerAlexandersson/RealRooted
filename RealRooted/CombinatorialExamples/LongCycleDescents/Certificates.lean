/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Mesh
public import RealRooted.CombinatorialExamples.LongCycleDescents.PackedInversion
import Mathlib.Tactic

/-!
# From recomputed coefficients to the original permutation roots

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset

/-- Quotient coefficients, reconstructed afresh rather than supplied as certificate data. -/
def quotientCoefficients (n k : ℕ) : List ℤ :=
  ((packedDescentRow n k).drop 1).take (n - 2)

/-- Check the two zero endpoint coefficients and the common negative quotient grid. -/
def descentMesh (n k : ℕ) (nodes : Array Dyadic) : Bool :=
  let cs := quotientCoefficients n k
  decide (packedDescentRow n k = (0 :: cs) ++ [0]) && negativeMesh cs nodes

/-- A successful check identifies the coefficients of the original permutation row. -/
theorem descentMesh_coefficients {n k : ℕ} {nodes : Array Dyadic}
    (h : descentMesh n k nodes = true) :
    descentRowDP n k = (0 :: quotientCoefficients n k) ++ [0] := by
  have eq := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  rwa [packedDescentRow_eq] at eq

/-- A checked row has a simple zero and all remaining zeros simple and negative. -/
theorem descentMesh_splits {n k : ℕ} (hn : 0 < n) {nodes : Array Dyadic}
    (h : descentMesh n k nodes = true) :
    let p := (descentPolynomial n k).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = nodes.size ∧ (∀ z ∈ p.roots, z ≤ 0) := by
  have mesh := (Bool.and_eq_true_iff.mp h).2
  have eq := row_eq_of_checkedCoeffs hn (descentMesh_coefficients h)
  rw [eq]
  have result := negativeMesh_splits mesh
  have pos := negativeMesh_eval_zero_pos mesh
  have ne : coefficientPolynomial (quotientCoefficients n k) ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at pos
    exact lt_irrefl _ pos
  have notRoot : (0 : ℝ) ∉ (coefficientPolynomial (quotientCoefficients n k)).roots := by
    intro hz
    have zero := (mem_roots ne).mp hz
    exact pos.ne' zero
  have roots : (X * coefficientPolynomial (quotientCoefficients n k)).roots =
      {0} + (coefficientPolynomial (quotientCoefficients n k)).roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero ne), roots_X]
  refine ⟨Splits.X.mul result.2.1, ?_, ?_, ?_, ?_⟩
  · rw [roots, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨notRoot, result.2.2.1⟩
  · rw [roots]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self 0))
  · rw [natDegree_mul (X_ne_zero) ne, natDegree_X, result.1]
    have sizes := (negativeMesh_size mesh).1
    lia
  · intro z hz
    rw [roots, Multiset.mem_add, Multiset.mem_singleton] at hz
    exact hz.elim (fun e ↦ e ▸ le_rfl) (fun e ↦ (result.2.2.2 z e).le)

end RealRooted.LongCycleDescents.Necklace
