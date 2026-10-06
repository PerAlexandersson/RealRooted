import RealRooted.FactorialCompression.RootGeometry

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The common factorial-compression kernel family

The polynomial family `h r` is the common Schur--Szegő kernel used by the
factorial-compression operator.  This module owns its coefficient formulas,
recurrence, degree, negative-root geometry, and adjacent strict interlacing.
-/

open Polynomial RealRooted
open scoped BigOperators

noncomputable section

namespace RealRooted.FactorialCompression

def h (r : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (r / 2 + 1),
    C ((Nat.factorial r : ℝ) /
      ((Nat.factorial j : ℝ) * (Nat.factorial (r - 2 * j) : ℝ))) * X ^ j

theorem coeff_h (r k : ℕ) :
    (h r).coeff k = if 2 * k ≤ r then
      (Nat.factorial r : ℝ) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (r - 2 * k) : ℝ)) else 0 := by
  classical
  have hi : k ≤ r / 2 ↔ 2 * k ≤ r := by lia
  simp [h, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Nat.lt_succ_iff, hi]

/-- A coefficient lowering identity with the zero boundary included. -/
theorem h_coeff_lower (r k : ℕ) :
    ((r : ℝ) + 1 - 2 * (k : ℝ)) * (h (r + 1)).coeff k =
      ((r : ℝ) + 1) * (h r).coeff k := by
  by_cases hk : 2 * k ≤ r
  · have hk' : 2 * k ≤ r + 1 := by lia
    have hi : r + 1 - 2 * k = (r - 2 * k) + 1 := by lia
    have hc : ((r - 2 * k : ℕ) : ℝ) + 1 = (r : ℝ) + 1 - 2 * (k : ℝ) := by
      have he : r = (r - 2 * k) + 2 * k := by lia
      have heq := congrArg (fun n : ℕ => (n : ℝ)) he
      push_cast at heq
      linarith
    rw [coeff_h, if_pos hk', coeff_h, if_pos hk, hi]
    simp only [Nat.factorial_succ]
    push_cast
    rw [hc]
    have hd : (Nat.factorial (r - 2 * k) : ℝ) ≠ 0 := by positivity
    have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have ha : (r : ℝ) + 1 - 2 * (k : ℝ) ≠ 0 := by
      rw [← hc]
      positivity
    field_simp
  · by_cases hk' : 2 * k ≤ r + 1
    · have he : 2 * k = r + 1 := by lia
      have hc : (r : ℝ) + 1 - 2 * (k : ℝ) = 0 := by
        have := congrArg (fun n : ℕ => (n : ℝ)) he
        push_cast at this
        linarith
      simp [coeff_h, hk, hk', hc]
    · simp [coeff_h, hk, hk']

theorem h_coeff_shift (r k : ℕ) :
    ((k : ℝ) + 1) * (h (r + 2)).coeff (k + 1) =
      ((r : ℝ) + 2) * ((r : ℝ) + 1) * (h r).coeff k := by
  have hi : 2 * (k + 1) ≤ r + 2 ↔ 2 * k ≤ r := by lia
  by_cases hk : 2 * k ≤ r
  · have hd : r + 2 - 2 * (k + 1) = r - 2 * k := by lia
    rw [coeff_h, if_pos (hi.mpr hk), coeff_h, if_pos hk, hd]
    simp only [show r + 2 = (r + 1) + 1 by lia, Nat.factorial_succ]
    push_cast
    have hdne : (Nat.factorial (r - 2 * k) : ℝ) ≠ 0 := by positivity
    have hkne : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hkn : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · simp [coeff_h, hk, hi]

@[simp] theorem h_coeff_zero (r : ℕ) : (h r).coeff 0 = 1 := by
  rw [coeff_h]
  simp only [mul_zero, Nat.zero_le, if_true, Nat.factorial_zero, Nat.cast_one,
    one_mul, Nat.sub_zero]
  exact div_self (by positivity)

theorem h_coeff_pos (r k : ℕ) (hk : 2 * k ≤ r) : 0 < (h r).coeff k := by
  rw [coeff_h, if_pos hk]
  positivity

theorem h_nonneg (r : ℕ) : HasNonnegCoeffs (h r) := by
  intro k
  rw [coeff_h]
  split <;> positivity

theorem h_ne_zero (r : ℕ) : h r ≠ 0 := by
  intro heq
  have hz := h_coeff_zero r
  simp [heq] at hz

theorem h_pos_leading (r : ℕ) : 0 < (h r).leadingCoeff :=
  (h_nonneg r).pos_leadingCoeff (h_ne_zero r)

theorem h_natDegree (r : ℕ) : (h r).natDegree = r / 2 := by
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_h, if_neg (by lia)]
  · apply le_natDegree_of_ne_zero
    exact ne_of_gt (h_coeff_pos r (r / 2) (by lia))

@[simp] theorem h_one : h 1 = 1 := by
  ext k
  cases k with
  | zero => simp
  | succ k => simp [coeff_h, coeff_one, show ¬ 2 * (k + 1) ≤ 1 by lia]

theorem h_two_factor : h 2 = C (2 : ℝ) * (X - C (-1 / 2 : ℝ)) := by
  ext k
  cases k with
  | zero => norm_num [coeff_h]
  | succ k =>
      cases k with
      | zero => norm_num [coeff_h]
      | succ k => simp [coeff_h, coeff_X, show ¬ 2 * (k + 1 + 1) ≤ 2 by lia,
          show k + 1 + 1 ≠ 1 by lia]

theorem h_two_roots : (h 2).roots = {-1 / 2} := by
  rw [h_two_factor, roots_C_mul _ (by norm_num), roots_X_sub_C]

private theorem factorial_real_pred (r : ℕ) (hr : 1 ≤ r) :
    (Nat.factorial r : ℝ) = (r : ℝ) * (Nat.factorial (r - 1) : ℝ) := by
  have heq : r = (r - 1) + 1 := by lia
  conv_lhs => rw [heq, Nat.factorial_succ]
  push_cast
  congr 1
  exact_mod_cast (show (r - 1) + 1 = r by lia)

private theorem h_recurrence_coeff_succ (r k : ℕ) (hr : 1 ≤ r) :
    (h (r + 1)).coeff (k + 1) = (h r).coeff (k + 1) +
      (2 * (r : ℝ)) * (h (r - 1)).coeff k := by
  by_cases hguard : 2 * (k + 1) ≤ r + 1
  · have hprev : 2 * k ≤ r - 1 := by lia
    by_cases hmid : 2 * (k + 1) ≤ r
    · have hd : r + 1 - 2 * (k + 1) = (r - 2 * (k + 1)) + 1 := by lia
      have he : r - 1 - 2 * k = (r - 2 * (k + 1)) + 1 := by lia
      have hrreal : (r : ℝ) = ((r - 2 * (k + 1) : ℕ) : ℝ) + 2 * (k : ℝ) + 2 := by
        exact_mod_cast (show r = (r - 2 * (k + 1)) + 2 * k + 2 by lia)
      rw [coeff_h, if_pos hguard, coeff_h, if_pos hmid, coeff_h, if_pos hprev,
        hd, he]
      simp only [Nat.factorial_succ]
      push_cast
      simp only [factorial_real_pred r hr, hrreal]
      have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hdfac : (Nat.factorial (r - 2 * (k + 1)) : ℝ) ≠ 0 := by positivity
      have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
      have hdpos : ((r - 2 * (k + 1) : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · have hbound : 2 * (k + 1) = r + 1 := by lia
      have hd : r + 1 - 2 * (k + 1) = 0 := by lia
      have he : r - 1 - 2 * k = 0 := by lia
      have hrreal : (r : ℝ) = 2 * (k : ℝ) + 1 := by
        exact_mod_cast (show r = 2 * k + 1 by lia)
      rw [coeff_h, if_pos hguard, coeff_h, if_neg hmid, coeff_h, if_pos hprev,
        hd, he, Nat.factorial_zero]
      simp only [Nat.factorial_succ]
      push_cast
      simp only [factorial_real_pred r hr, hrreal]
      have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  · have hmid : ¬ 2 * (k + 1) ≤ r := by lia
    have hprev : ¬ 2 * k ≤ r - 1 := by lia
    simp [coeff_h, hguard, hmid, hprev]

/-- Closed-coefficient derivation of factorial-compression equation (4.4). -/
theorem h_recurrence (r : ℕ) (hr : 1 ≤ r) :
    h (r + 1) = h r + C (2 * (r : ℝ)) * X * h (r - 1) := by
  ext k
  cases k with
  | zero => simp [mul_assoc]
  | succ k =>
      simpa [mul_assoc] using h_recurrence_coeff_succ r k hr

private theorem h_base_geometry :
    SimpleNegativeRoots (h 2) ∧ StrictRootInterl (h 1) (h 2) := by
  have hsimple : SimpleNegativeRoots (h 2) := by
    refine ⟨h_ne_zero 2, Splits.of_natDegree_eq_one (by simpa using h_natDegree 2), ?_, ?_⟩
    · simp [h_two_roots]
    · intro r hr
      simp only [h_two_roots, Multiset.mem_singleton] at hr
      subst r
      norm_num
  refine ⟨hsimple, h_pos_leading 1, h_pos_leading 2, ?_, hsimple.2.1,
    [], [-1 / 2], by simp, by simp, ?_, ?_, Or.inl ⟨by simp, True.intro⟩⟩
  · simp
  · simp
  · simp [h_two_roots]

private theorem h_geometry (r : ℕ) (hr : 1 ≤ r) :
    SimpleNegativeRoots (h (r + 1)) ∧ StrictRootInterl (h r) (h (r + 1)) := by
  induction r, hr using Nat.le_induction with
  | base => exact h_base_geometry
  | succ r hr ih =>
      apply root_sign_criterion ih.1 (h_pos_leading (r + 1))
        (by rw [h_natDegree]; lia) (h_nonneg (r + 2))
        (by rw [h_coeff_zero]; norm_num) (h_pos_leading (r + 2))
        (by rw [h_natDegree, h_natDegree]; lia)
      intro s hs
      have hsneg : s < 0 := ih.1.2.2.2 s ((mem_roots ih.1.1).mpr hs)
      have hratio : 0 < (h r).eval s / (h (r + 1)).derivative.eval s :=
        ih.2.right_root_ratio_pos hs
      have heval : (h (r + 2)).eval s =
          2 * ((r + 1 : ℕ) : ℝ) * s * (h r).eval s := by
        rw [show r + 2 = (r + 1) + 1 by lia, h_recurrence (r + 1) (by lia)]
        simp [hs.eq_zero, show r + 1 - 1 = r by lia]
      rw [heval, mul_div_assoc]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by positivity) hsneg) hratio

/-- All simple-negative kernel roots, without a finite-index bound. -/
theorem h_simple_negative (r : ℕ) (hr : 2 ≤ r) : SimpleNegativeRoots (h r) := by
  simpa [show r - 1 + 1 = r by lia] using (h_geometry (r - 1) (by lia)).1

/-- Includes the factorial-compression's explicit constant/linear first pair. -/
theorem h_strict_interl (r : ℕ) (hr : 1 ≤ r) :
    StrictRootInterl (h r) (h (r + 1)) := (h_geometry r hr).2

end RealRooted.FactorialCompression
