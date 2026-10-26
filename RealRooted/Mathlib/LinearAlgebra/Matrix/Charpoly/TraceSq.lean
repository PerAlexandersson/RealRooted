/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Expand
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The trace of the square of a matrix

For a square matrix `M` over a commutative ring the trace of `M * M` is `e₁² - 2 e₂`, where
`e₁ = trace M` and `e₂` is the second coefficient of the reversed characteristic polynomial.

For a symmetric matrix over `ℝ[X]`, the trace of `M * M` is the sum of the squares of the
entries.  Since the top coefficients of a sum of squares of real polynomials cannot cancel, degree
bounds on the characteristic polynomial coefficients bound the degrees of the entries.

## Main statements

* `Matrix.trace_mul_self_eq`: `trace (M * M) = trace M ^ 2 - 2 * M.charpolyRev.coeff 2`.
* `Matrix.natDegree_entry_le_of_isSymm_charpoly`: if the coefficient `j` of the characteristic
  polynomial of a symmetric matrix over `ℝ[X]` has degree at most `k * (d - j)` for all `j < d`,
  then every entry has degree at most `k`.
-/

@[expose] public section

open Polynomial

namespace Matrix

/-- `tr (M ^ 2) = e₁ ^ 2 - 2 e₂`, in terms of the reversed characteristic polynomial. -/
theorem trace_mul_self_eq {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R) :
    trace (M * M) = trace M ^ 2 - 2 * M.charpolyRev.coeff 2 := by
  have hS : det (1 + (X : R[X]) • M.map C) = M.charpolyRev.comp (-X) := by
    rw [charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  have hprod : M.charpolyRev * det (1 + (X : R[X]) • M.map C) =
      expand R 2 (M * M).charpolyRev := by
    rw [charpolyRev, charpolyRev, ← det_mul, ← AlgHom.coe_toRingHom, RingHom.map_det]
    congr 1
    rw [Matrix.map_mul]
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
    rw [show ∀ a b c : Matrix n n R[X], a + b - (b + c) = a - c by intros; abel, map_sub,
      map_one]
    congr 1
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, pow_two]
  rw [hS] at hprod
  have h2 := congrArg (fun p => p.coeff 2) hprod
  simp only [coeff_expand two_pos] at h2
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero] at h2
  have h0 : M.charpolyRev.coeff 0 = 1 := by rw [coeff_zero_eq_eval_zero, eval_charpolyRev]
  simp [coeff_comp_neg_X, h0] at h2
  linear_combination h2

/-- If a sum of squares of real polynomials has degree `≤ 2k`, each summand has degree `≤ k`
(the top coefficients cannot cancel). -/
private lemma natDegree_le_of_natDegree_sum_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (k : ℕ) (h : (∑ i ∈ s, f i ^ 2).natDegree ≤ 2 * k) : ∀ i ∈ s, (f i).natDegree ≤ k := by
  intro i0 hi0
  by_contra hlt
  push Not at hlt
  set m := s.sup (fun i => (f i).natDegree)
  have hm : (f i0).natDegree ≤ m := Finset.le_sup (f := fun i => (f i).natDegree) hi0
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_sup s ⟨i0, hi0⟩ (fun i => (f i).natDegree)
  have hcoeff : (∑ i ∈ s, f i ^ 2).coeff (m + m) = ∑ i ∈ s, (f i).coeff m ^ 2 := by
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [pow_two, pow_two, coeff_mul_add_eq_of_natDegree_le] <;>
      exact Finset.le_sup (f := fun i => (f i).natDegree) hi
  have hj0 : f j ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hjm
    lia
  have hpos : 0 < ∑ i ∈ s, (f i).coeff m ^ 2 := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg _)
    refine ⟨j, hj, ?_⟩
    have : (f j).coeff m = (f j).leadingCoeff := by rw [leadingCoeff, ← hjm]
    rw [this]
    exact pow_pos (abs_pos.mpr (leadingCoeff_ne_zero.mpr hj0)) 2 |>.trans_eq (sq_abs _)
  have := le_natDegree_of_ne_zero (hcoeff ▸ hpos.ne' : (∑ i ∈ s, f i ^ 2).coeff (m + m) ≠ 0)
  lia

/-- For a symmetric matrix of real polynomials, degree bounds on the characteristic-polynomial
coefficients bound the entries: if `coeff j` of the characteristic polynomial has degree
`≤ k (d - j)` for all `j < d`, every entry has degree `≤ k`.  (Here `tr (M ^ 2) = e₁² - 2 e₂`
has degree `≤ 2k`, and for a real symmetric matrix it is the sum of the squares of the entries,
whose top coefficients cannot cancel.) -/
theorem natDegree_entry_le_of_isSymm_charpoly {d k : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ[X]) (hM : M.IsSymm)
    (h : ∀ j < d, (M.charpoly.coeff j).natDegree ≤ k * (d - j)) :
    ∀ i l, (M i l).natDegree ≤ k := by
  intro i l
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact i.elim0
  have : Nonempty (Fin d) := ⟨i⟩
  have htr : (trace M).natDegree ≤ k := by
    rw [trace_eq_neg_charpoly_coeff, natDegree_neg, Fintype.card_fin]
    have := h (d - 1) (by lia)
    rwa [show d - (d - 1) = 1 by lia, mul_one] at this
  have hc2 : (M.charpolyRev.coeff 2).natDegree ≤ 2 * k := by
    rw [← reverse_charpoly, coeff_reverse, charpoly_natDegree_eq_dim, Fintype.card_fin]
    by_cases hd2 : 2 ≤ d
    · rw [revAt_le hd2]
      have := h (d - 2) (by lia)
      rwa [show d - (d - 2) = 2 by lia, mul_comm] at this
    · rw [revAt_eq_self_of_lt (by lia), coeff_eq_zero_of_natDegree_lt]
      · simp
      · rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; lia
  have hdeg : (trace (M * M)).natDegree ≤ 2 * k := by
    rw [trace_mul_self_eq]
    refine (natDegree_sub_le_of_le (m := 2 * k) (n := 2 * k) ?_ ?_).trans (max_self _).le
    · exact natDegree_pow_le_of_le 2 htr
    · refine (natDegree_mul_le).trans ?_
      have : (2 : ℝ[X]).natDegree = 0 := natDegree_ofNat 2
      lia
  have hsq : (∑ p : Fin d × Fin d, M p.1 p.2 ^ 2) = trace (M * M) := by
    rw [Fintype.sum_prod_type]
    simp only [trace, diag_apply, mul_apply, pow_two]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hM.apply a b]
  exact natDegree_le_of_natDegree_sum_sq_le Finset.univ (fun p : Fin d × Fin d => M p.1 p.2) k
    (hsq ▸ hdeg) (i, l) (Finset.mem_univ _)

end Matrix
