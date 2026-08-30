import RealRooted.Favard
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

/-!
# Real-rootedness of shifted Jacobi polynomials

This file applies the general Favard recurrence theorem to the monic shifted
Jacobi family. The coefficient algebra and positivity of the recurrence
coefficients live in `RealRooted.Mathlib.RingTheory.Polynomial.Jacobi`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The monic shifted Jacobi family satisfies the Favard recurrence with its
explicit diagonal and subdiagonal coefficients. -/
theorem shiftedJacobiMonic_satisfiesFavardRecurrence (α β : ℝ)
    (hα : -1 < α) (hβ : -1 < β) :
    SatisfiesFavardRecurrence
      (fun n => shiftedJacobiMonic n α β)
      (fun n => shiftedJacobiDiag n α β)
      (fun n => shiftedJacobiSubdiag n α β) := by
  refine ⟨shiftedJacobiMonic_zero α β, ?_, ?_⟩
  · have hsum : α + β + 2 ≠ 0 := by linarith
    simpa [shiftedJacobiDiag] using shiftedJacobiMonic_one α β hsum
  · intro n
    simpa only [Nat.add_sub_cancel] using
      shiftedJacobiMonic_recurrence (n + 1) α β (by lia) hα hβ

/-- Consecutive monic shifted Jacobi polynomials are in proper position when
both parameters exceed `-1`. -/
theorem shiftedJacobiMonic_prec_succ (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    Prec (shiftedJacobiMonic n α β) (shiftedJacobiMonic (n + 1) α β) := by
  apply favardInterlacing (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
  · intro k
    exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ

/-- A monic shifted Jacobi polynomial is nonzero when both parameters exceed
`-1`. -/
theorem shiftedJacobiMonic_ne_zero (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobiMonic n α β ≠ 0 :=
  (shiftedJacobiMonic_prec_succ n hα hβ).1.1

/-- A monic shifted Jacobi polynomial splits over `ℝ` when both parameters
exceed `-1`. -/
theorem shiftedJacobiMonic_splits (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiMonic n α β).Splits :=
  (shiftedJacobiMonic_prec_succ n hα hβ).1.2

/-- The roots of a monic shifted Jacobi polynomial are simple when both
parameters exceed `-1`. -/
theorem shiftedJacobiMonic_roots_nodup (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiMonic n α β).roots.Nodup := by
  apply roots_nodup_of_favard
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
  intro k
  exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ

private theorem shiftedJacobi_leadingScale_ne_zero (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n ≠ 0 := by
  intro hscale
  apply (monic_shiftedJacobiMonic n hα hβ).ne_zero
  simp [shiftedJacobiMonic, hscale]

/-- A shifted Jacobi polynomial is nonzero when both parameters exceed
`-1`. -/
theorem shiftedJacobi_ne_zero (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobi n α β ≠ 0 := by
  intro hzero
  apply (monic_shiftedJacobiMonic n hα hβ).ne_zero
  simp [shiftedJacobiMonic, hzero]

/-- The roots of a shifted Jacobi polynomial are simple when both parameters
exceed `-1`. -/
theorem shiftedJacobi_roots_nodup (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobi n α β).roots.Nodup := by
  have hscale := shiftedJacobi_leadingScale_ne_zero n hα hβ
  have hroots :
      (shiftedJacobiMonic n α β).roots = (shiftedJacobi n α β).roots := by
    rw [shiftedJacobiMonic]
    exact roots_C_mul _ (inv_ne_zero hscale)
  rw [← hroots]
  exact shiftedJacobiMonic_roots_nodup n hα hβ

/-- A shifted Jacobi polynomial splits over `ℝ` when both parameters exceed
`-1`. -/
theorem shiftedJacobi_splits (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobi n α β).Splits := by
  let c : ℝ := (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n
  have hc : c ≠ 0 := by
    exact shiftedJacobi_leadingScale_ne_zero n hα hβ
  have hrecover :
      shiftedJacobi n α β = C c * shiftedJacobiMonic n α β := by
    change shiftedJacobi n α β = C c * (C c⁻¹ * shiftedJacobi n α β)
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]
    simp
  rw [hrecover]
  exact (shiftedJacobiMonic_splits n hα hβ).C_mul c

/-- After negating the variable, a shifted Jacobi polynomial has nonnegative
coefficients when both parameters exceed `-1`. -/
theorem shiftedJacobi_comp_neg_X_hasNonnegCoeffs (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    HasNonnegCoeffs ((shiftedJacobi n α β).comp (-X)) := by
  intro k
  rw [show (-X : ℝ[X]) = C (-1) * X by simp]
  rw [Polynomial.comp_C_mul_X_coeff, coeff_shiftedJacobi]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have hleft : 0 < Ring.choose (n + α) (n - k) := by
      apply Polynomial.ring_choose_pos
      rw [Nat.cast_sub hk]
      have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
      linarith
    have hright : 0 < Ring.choose (n + α + β + k) k := by
      cases k with
      | zero => simp
      | succ d =>
          apply Polynomial.ring_choose_pos
          have hn : 1 ≤ n := by lia
          have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
          norm_num only [Nat.cast_add, Nat.cast_one]
          linarith
    rw [show
      (-1 : ℝ) ^ k * Ring.choose (n + α) (n - k) *
          Ring.choose (n + α + β + k) k * (-1 : ℝ) ^ k =
        ((-1 : ℝ) ^ k) ^ 2 *
          (Ring.choose (n + α) (n - k) *
            Ring.choose (n + α + β + k) k) by ring]
    exact mul_nonneg (sq_nonneg _) (mul_pos hleft hright).le
  · simp [hk]

/-- Every real root of a shifted Jacobi polynomial is nonnegative when both
parameters exceed `-1`. -/
theorem shiftedJacobi_isRoot_nonneg (n : ℕ) {α β r : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobi n α β).IsRoot r) :
    0 ≤ r := by
  have hcomp : ((shiftedJacobi n α β).comp (-X)).IsRoot (-r) := by
    simpa [Polynomial.IsRoot.def] using hr
  have hcomp_ne : (shiftedJacobi n α β).comp (-X) ≠ 0 := by
    intro hzero
    apply shiftedJacobi_ne_zero n hα hβ
    exact Polynomial.comp_neg_X_eq_zero_iff.mp hzero
  have hnonpos := isRoot_nonpos_of_hasNonnegCoeffs
    (shiftedJacobi_comp_neg_X_hasNonnegCoeffs n hα hβ) hcomp_ne hcomp
  linarith

/-- Every real root of a shifted Jacobi polynomial is at most one when both
parameters exceed `-1`. -/
theorem shiftedJacobi_isRoot_le_one (n : ℕ) {α β r : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobi n α β).IsRoot r) :
    r ≤ 1 := by
  have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have heval := congrArg (fun p : ℝ[X] => p.eval r)
    (Polynomial.shiftedJacobi_reflection n α β)
  have hswap : (shiftedJacobi n β α).IsRoot (1 - r) := by
    rw [Polynomial.IsRoot.def]
    rw [Polynomial.IsRoot.def] at hr
    simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_one, eval_X] at heval
    rw [hr] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left hsign
  linarith [shiftedJacobi_isRoot_nonneg n hβ hα hswap]

/-- Every real root of a shifted Jacobi polynomial lies in the open unit
interval when both parameters exceed `-1`. -/
theorem shiftedJacobi_isRoot_mem_Ioo (n : ℕ) {α β r : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobi n α β).IsRoot r) :
    r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hr_nonneg := shiftedJacobi_isRoot_nonneg n hα hβ hr
  have hr_le_one := shiftedJacobi_isRoot_le_one n hα hβ hr
  constructor
  · apply lt_of_le_of_ne hr_nonneg
    intro hr_zero
    rw [← hr_zero, Polynomial.IsRoot.def, shiftedJacobi_eval_zero] at hr
    exact (Polynomial.ring_choose_pos (by linarith : (n : ℝ) - 1 < n + α)).ne' hr
  · apply lt_of_le_of_ne hr_le_one
    intro hr_one
    rw [hr_one, Polynomial.IsRoot.def, shiftedJacobi_eval_one] at hr
    exact (mul_ne_zero (pow_ne_zero n (by norm_num))
      (Polynomial.ring_choose_pos (by linarith : (n : ℝ) - 1 < n + β)).ne') hr

/-- Initial segments of the monic shifted Jacobi family, listed in reverse
degree order, form generalized Sturm sequences. -/
theorem shiftedJacobiMonic_isGeneralizedSturmSeq (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    IsGeneralizedSturmSeq
      ((List.range (n + 1)).reverse.map (fun k => shiftedJacobiMonic k α β)) := by
  apply isGeneralizedSturmSeq_reverse_range_map_of_favard
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
  · intro k
    exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ

end RealRooted
