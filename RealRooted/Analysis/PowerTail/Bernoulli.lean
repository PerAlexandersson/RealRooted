import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities

/-!
# Bernoulli steps for reciprocal-power tails

The one-step estimate underlying finite telescoping bounds for reciprocal-power
tails with an arbitrary positive spacing.
-/

namespace RealRooted.Analysis.PowerTail

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A positive shifted power dominates its first Bernoulli term. -/
theorem binom_step_w {A w : K} (hA : 0 < A) (hw : 0 < w) (r : ℕ) :
    A ^ (r + 1) + w * ((r : K) + 1) * A ^ r ≤ (A + w) ^ (r + 1) := by
  have hb : 1 + ((r : K) + 1) * (w / A) ≤ (1 + w / A) ^ (r + 1) := by
    have hge : (-2 : K) ≤ w / A := by
      have : (0 : K) < w / A := by positivity
      linarith
    simpa using one_add_mul_le_pow (a := w / A) hge (r + 1)
  have hApos : (0 : K) < A ^ (r + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hb hApos.le
  have hrw : (1 + w / A) ^ (r + 1) * A ^ (r + 1) = (A + w) ^ (r + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hrw] at hmul
  refine le_trans (le_of_eq ?_) hmul
  field_simp
  ring

/-- The reciprocal-power difference supplied by one positive step. -/
theorem step_ineq_w {A w : K} (hA : 0 < A) (hw : 0 < w) (r : ℕ) :
    w * ((r : K) + 1) / (A + w) ^ (r + 2)
      ≤ 1 / A ^ (r + 1) - 1 / (A + w) ^ (r + 1) := by
  have hB : (0 : K) < A + w := by linarith
  have hAp : (0 : K) < A ^ (r + 1) := by positivity
  have hBp : (0 : K) < (A + w) ^ (r + 1) := by positivity
  have hBp2 : (0 : K) < (A + w) ^ (r + 2) := by positivity
  have hbin := binom_step_w hA hw r
  have hcore : w * ((r : K) + 1) * A ^ (r + 1)
      ≤ (A + w) * ((A + w) ^ (r + 1) - A ^ (r + 1)) := by
    have h1 : w * ((r : K) + 1) * A ^ r
        ≤ (A + w) ^ (r + 1) - A ^ (r + 1) := by
      linarith
    have h2 : (A + w) * (w * ((r : K) + 1) * A ^ r)
        ≤ (A + w) * ((A + w) ^ (r + 1) - A ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hB)
    have h3 : w * ((r : K) + 1) * A ^ (r + 1)
        ≤ (A + w) * (w * ((r : K) + 1) * A ^ r) := by
      have hAr : A ^ (r + 1) = A * A ^ r := by ring
      rw [hAr]
      have hnn : (0 : K) ≤ w * ((r : K) + 1) * A ^ r := by positivity
      nlinarith
    linarith
  rw [div_sub_div _ _ (ne_of_gt hAp) (ne_of_gt hBp),
    div_le_div_iff₀ hBp2 (by positivity)]
  rw [show (A + w) ^ (r + 2) = (A + w) * (A + w) ^ (r + 1) by ring]
  have hfin := mul_le_mul_of_nonneg_right hcore hBp.le
  nlinarith [hfin]

end RealRooted.Analysis.PowerTail
