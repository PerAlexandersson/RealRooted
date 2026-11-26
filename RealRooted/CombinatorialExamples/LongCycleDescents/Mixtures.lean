/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Certificates
import Mathlib.Tactic

/-!
# Nonnegative mixtures sharing a checked negative grid

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset

/-- The quotient sum is positive at zero and has the same alternating signs as every row. -/
private theorem quotient_sum_signs {n : ℕ} {s : Finset ℕ} {cutoff : ℕ → ℕ} {nodes : Array Dyadic}
    (mesh : ∀ k ∈ s, descentMesh n (cutoff k) nodes = true) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (pos : ∃ k ∈ s, 0 < w k) :
    let q := ∑ k ∈ s, C (w k) * coefficientPolynomial (quotientCoefficients n (cutoff k))
    0 < q.eval 0 ∧ ∀ i < nodes.size, if (nodes.size - 1 - i) % 2 = 1 then
      q.eval (nodes.getD i Dyadic.zero).value < 0 else
      0 < q.eval (nodes.getD i Dyadic.zero).value := by
  dsimp only
  have checked k hk := (Bool.and_eq_true_iff.mp (mesh k hk)).2
  have hz k hk := negativeMesh_eval_zero_pos (checked k hk)
  constructor
  · simp only [Polynomial.eval_finsetSum, eval_mul, eval_C]
    exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk) (hz k hk).le)
      (pos.imp fun k hk ↦ ⟨hk.1, mul_pos hk.2 (hz k hk.1)⟩)
  · intro i hi
    have signs k hk := negativeMesh_sign (checked k hk) hi
    by_cases parity : (nodes.size - 1 - i) % 2 = 1
    · simp only [ite_eq_left parity, Polynomial.eval_finsetSum, eval_mul, eval_C] at signs ⊢
      exact sum_neg' (fun k hk ↦ mul_nonpos_of_nonneg_of_nonpos (hw k hk) (signs k hk).le)
        (pos.imp fun k hk ↦ ⟨hk.1, mul_neg_of_pos_of_neg hk.2 (signs k hk.1)⟩)
    · simp only [ite_eq_right parity, Polynomial.eval_finsetSum, eval_mul, eval_C] at signs ⊢
      exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk) (signs k hk).le)
        (pos.imp fun k hk ↦ ⟨hk.1, mul_pos hk.2 (signs k hk.1)⟩)

/-- All nonzero nonnegative mixtures on a checked common grid split with simple roots. -/
theorem descentMesh_sum_splits {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    {nodes : Array Dyadic} {cutoff : ℕ → ℕ} (mesh : ∀ k ∈ s, descentMesh n (cutoff k) nodes = true)
    {w : ℕ → ℝ} (hw : ∀ k ∈ s, 0 ≤ w k) (pos : ∃ k ∈ s, 0 < w k) :
    let p := ∑ k ∈ s, C (w k) * (descentPolynomial n (cutoff k)).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ (∀ z ∈ p.roots, z ≤ 0) := by
  classical
  let q := ∑ k ∈ s, C (w k) * coefficientPolynomial (quotientCoefficients n (cutoff k))
  have checked k hk := (Bool.and_eq_true_iff.mp (mesh k hk)).2
  have signs := quotient_sum_signs mesh hw pos
  obtain ⟨k, hk, _⟩ := pos
  have nodePos := (negativeMesh_size (checked k hk)).1
  have ne : q ≠ 0 := by
    intro hz
    have atZero := signs.1
    change 0 < q.eval 0 at atZero
    rw [hz, eval_zero] at atZero
    exact lt_irrefl _ atZero
  have bound : q.natDegree ≤ nodes.size - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans ((natDegree_coefficientPolynomial_le _).trans_eq
      (congrArg (· - 1) (negativeMesh_size (checked j hj)).2.symm))
  have roots := Polynomial.splits_nodup_roots_of_strict_sign_changes ne bound _
    (negativeMesh_strictMono (checked k hk))
    (eval_mul_eval_neg_of_alternating_signs signs.2)
  have location {z : ℝ} (hz : z ∈ q.roots) : z < 0 :=
    (roots.2.2.2 z hz).2.trans
      (negativeMesh_node_neg (checked k hk) (Nat.sub_lt nodePos (by decide)))
  have zeroNot : (0 : ℝ) ∉ q.roots := fun hz ↦ (lt_irrefl _) (location hz)
  have eq : (∑ j ∈ s, C (w j) * (descentPolynomial n (cutoff j)).map (Int.castRingHom ℝ)) =
      X * q := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [row_eq_of_checkedCoeffs hn
      (descentMesh_coefficients (mesh j hj))]
    ring
  rw [eq]
  have rootEq : (X * q).roots = {0} + q.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero ne), roots_X]
  refine ⟨Splits.X.mul roots.2.1, ?_, ?_, ?_⟩
  · rw [rootEq, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨zeroNot, roots.2.2.1⟩
  · rw [rootEq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self 0))
  · intro z hz
    rw [rootEq, Multiset.mem_add, Multiset.mem_singleton] at hz
    exact hz.elim (fun e ↦ e ▸ le_rfl) (fun e ↦ (location e).le)

end RealRooted.LongCycleDescents.Necklace

end
