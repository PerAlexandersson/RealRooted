/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetTransform
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# The three alphabet factors for long-cycle descents

The increasing and reversing permutations are excluded at cutoff at least three.
Consequently the binomial alphabet polynomial vanishes at `0`, `1`, and `-1`.
We factor these three roots and obtain the structural transform of the actual row.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

private theorem descentCount_zero_iff {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    σ.descentCount = 0 ↔ σ = 1 := by
  classical
  rw [descents_eq_card, card_filter_eq_zero_iff]
  simp only [mem_univ, true_implies, not_lt]
  constructor
  · intro h
    have hm : StrictMono σ := Fin.strictMono_iff_lt_succ.mpr fun i =>
      lt_of_le_of_ne (h i) (fun he => Fin.castSucc_lt_succ.ne (σ.injective he))
    exact Equiv.ext fun i => congrFun hm.eq_id i
  · rintro rfl i
    exact Fin.castSucc_lt_succ.le

private theorem descentCount_full_iff {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    σ.descentCount = m ↔ σ = Fin.revPerm := by
  classical
  rw [descents_eq_card]
  conv_lhs => rhs; rw [← (show (univ : Finset (Fin m)).card = m by simp)]
  rw [card_filter_eq_iff]
  simp only [mem_univ, true_implies]
  constructor
  · intro h
    have ha : StrictAnti σ := Fin.strictAnti_iff_succ_lt.mpr h
    have he := (Fin.rev_strictAnti.comp ha).eq_id
    apply Equiv.ext
    intro i
    simpa using congrArg Fin.rev (congrFun he i)
  · rintro rfl i
    exact Fin.rev_strictAnti Fin.castSucc_lt_succ

/-- The constant and maximal-descent coefficients vanish for cutoffs at least three. -/
theorem extreme_coefficients_zero (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    (descentPolynomial (m + 1) k).coeff 0 = 0 ∧
      (descentPolynomial (m + 1) k).coeff m = 0 := by
  constructor <;> rw [coeff_descentPolynomial] <;> apply sum_eq_zero <;>
    intro σ _ <;> apply ite_eq_right <;> rintro ⟨ha, hd⟩
  · obtain rfl := (descentCount_zero_iff σ).mp hd
    exact ne_fixed_of_allowed ha (by lia) 0 rfl
  · obtain rfl := (descentCount_full_iff σ).mp hd
    have hh := ha 0 2 (by decide) (by lia)
    exact hh (by simp [pow_two, Equiv.Perm.mul_apply])

private theorem alphabet_eval (n k : ℕ) (q : ℝ) :
    (descentAlphabetPolynomial n k).eval q = ∑ i ∈ range n,
      ((descentPolynomial n k).coeff i : ℝ) * Ring.choose (q + n - 1 - i) n := by
  simp only [descentAlphabetPolynomial, eval_finsetSum, eval_mul, eval_C]
  apply sum_congr rfl
  intro i _
  congr 1
  change (evalRingHom q) (Ring.choose _ _) = _
  rw [Ring.map_choose]
  simp only [coe_evalRingHom, eval_sub, eval_add, eval_X, eval_natCast, eval_one]

private theorem alphabet_eval_zero {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (descentAlphabetPolynomial n k).eval 0 = 0 := by
  rw [alphabet_eval]
  apply sum_eq_zero
  intro i hi
  have hin := mem_range.mp hi
  have ha : ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)]
    norm_num
  rw [zero_add, ← ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by lia)]
  simp

private theorem alphabet_eval_one (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    (descentAlphabetPolynomial (m + 1) k).eval 1 = 0 := by
  rw [alphabet_eval]
  apply sum_eq_zero
  intro i hi
  by_cases hz : i = 0
  · rw [hz, (extreme_coefficients_zero m hk).1, Int.cast_zero, zero_mul]
  · have hin := mem_range.mp hi
    have ha : ((m + 1 - i : ℕ) : ℝ) = 1 + (m + 1 : ℕ) - 1 - i := by
      rw [Nat.cast_sub (by lia)]
      push_cast
      ring
    rw [← ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by lia)]
    simp

private theorem alphabet_eval_neg_one (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    (descentAlphabetPolynomial (m + 2) k).eval (-1) = 0 := by
  rw [alphabet_eval]
  apply sum_eq_zero
  intro i hi
  by_cases hz : i = m + 1
  · rw [hz, (extreme_coefficients_zero (m + 1) hk).2, Int.cast_zero, zero_mul]
  · have hin := mem_range.mp hi
    have ha : ((m - i : ℕ) : ℝ) = -1 + (m + 2 : ℕ) - 1 - i := by
      rw [Nat.cast_sub (by lia)]
      push_cast
      ring
    rw [← ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by lia)]
    simp

private theorem natDegree_choose_linear_le (b : ℝ) (n : ℕ) :
    (Ring.choose (X + C b : ℝ[X]) n).natDegree ≤ n := by
  have hs (j : ℕ) : ((descPochhammer ℤ j).smeval (X + C b : ℝ[X])).natDegree ≤ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [descPochhammer_succ_right, smeval_mul]
      apply natDegree_mul_le.trans
      have hl : ((X - (j : ℤ[X])).smeval (X + C b : ℝ[X])).natDegree ≤ 1 := by
        simp only [smeval_sub, smeval_X, smeval_natCast]
        apply (natDegree_sub_le _ _).trans
        exact max_le (by simp) (by simp)
      lia
  have he := Ring.descPochhammer_eq_factorial_smul_choose (X + C b : ℝ[X]) n
  rw [nsmul_eq_mul, ← C_eq_natCast] at he
  rw [← natDegree_C_mul (by positivity : (n.factorial : ℝ) ≠ 0), ← he]
  exact hs n

/-- The alphabet degree is at most the permutation size. -/
theorem natDegree_descentAlphabetPolynomial_le (n k : ℕ) :
    (descentAlphabetPolynomial n k).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_C_mul_le _ _).trans
  have he : (X + (n : ℝ[X]) - 1 - (i : ℝ[X])) = X + C ((n : ℝ) - 1 - i) := by
    simp only [map_sub, map_natCast, map_one]
    ring
  rw [he]
  exact natDegree_choose_linear_le _ _

/-- Every cutoff at least three has the three alphabet factors used by the
structural transfer. The remaining polynomial has degree at most `n-3`. -/
theorem exists_alphabet_quotient (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ∃ Q : ℝ[X], descentAlphabetPolynomial (m + 3) k = X * (X ^ 2 - 1) * Q ∧
      Q.natDegree ≤ m := by
  let f := descentAlphabetPolynomial (m + 3) k
  have h0 : f.eval 0 = 0 := alphabet_eval_zero (by lia) k
  have h1 : f.eval 1 = 0 := alphabet_eval_one (m + 2) hk
  have hm : f.eval (-1) = 0 := alphabet_eval_neg_one (m + 1) hk
  obtain ⟨R, hR⟩ : X ∣ f := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
  have hR1 : R.IsRoot 1 := by rw [hR, eval_mul, eval_X, one_mul] at h1; exact h1
  obtain ⟨S, hS⟩ := dvd_iff_isRoot.mpr hR1
  have hSm : S.IsRoot (-1) := by
    rw [hR, hS, eval_mul, eval_mul, eval_X, eval_sub, eval_X, eval_C] at hm
    change S.eval (-1) = 0
    linarith
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hSm
  have hf : f = X * (X ^ 2 - 1) * Q := by
    rw [hR, hS, hQ]
    simp only [map_neg, map_one]
    ring
  refine ⟨Q, hf, ?_⟩
  by_cases hz : Q = 0
  · simp [hz]
  · have hb : (X * (X ^ 2 - 1) : ℝ[X]).natDegree = 3 := by compute_degree <;> norm_num
    have hn : (X * (X ^ 2 - 1) : ℝ[X]) ≠ 0 :=
      ne_zero_of_natDegree_gt (show 0 < (X * (X ^ 2 - 1) : ℝ[X]).natDegree by
        rw [hb]; norm_num)
    have hd := natDegree_descentAlphabetPolynomial_le (m + 3) k
    change f.natDegree ≤ m + 3 at hd
    rw [hf, natDegree_mul hn hz, hb] at hd
    lia

/-- The actual permutation row has the structural operator representation,
with no alphabet-factorization hypothesis supplied by the caller. -/
theorem exists_interval_transform (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ∃ Q : ℝ[X], Q.natDegree ≤ m ∧
      descentAlphabetPolynomial (m + 3) k = X * (X ^ 2 - 1) * Q ∧
      realDescentPolynomial (m + 3) k =
        C 6 * X * mobiusTransform m 1 1 (-1) 1 (intervalSpectralApply 4 Q 1) := by
  obtain ⟨Q, hf, hd⟩ := exists_alphabet_quotient m hk
  refine ⟨Q, hd, hf, realDescentPolynomial_eq_interval_transform Q hf ?_⟩
  rwa [intervalSpectralApply_one_natDegree 4 (by norm_num)]

end RealRooted.LongCycleDescents.Structural
