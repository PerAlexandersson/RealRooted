module

public import RealRooted.Applications.BinderVecchi.UniformChow
public import RealRooted.Applications.BinderVecchi.UniformMatroid
public import RealRooted.Applications.OEIS.QuarticGamma
public import RealRooted.Tactic.RowInterlacing

/-!
# Parametric row tactics

Regression tests for fixed real parameters in first-order derivative and three-term
recurrences.  The final examples record the current status of the four families named in
issue #2049 whose defining equations do not expose a supported recurrence.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.ParametricRowExamples

noncomputable section

/-- A weighted derivative recurrence. -/
def weightedEulerianRows (q : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C q * X * (weightedEulerianRows q n).derivative +
      (1 + X) * weightedEulerianRows q n

example (q : ℝ) (n : ℕ) :
    (weightedEulerianRows q n).natDegree = n := by
  rr_row_natDegree

example {q : ℝ} (hq : 0 < q) (n : ℕ) :
    HasNonnegCoeffs (weightedEulerianRows q n) := by
  rr_row_nonneg_coeffs

example {q : ℝ} (hq : 0 < q) (n : ℕ) :
    Interlaces (weightedEulerianRows q n) (weightedEulerianRows q (n + 1)) := by
  rr_row_interlaces

example : True := by
  fail_if_success
    have _ : ∀ (q : ℝ) (n : ℕ), HasNonnegCoeffs (weightedEulerianRows q n) := by
      intro q n
      rr_row_nonneg_coeffs
  trivial

/-- A positive-lag three-term family. -/
def weightedLagRows (q : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (1 + X) * weightedLagRows q (n + 1) + C q * X * weightedLagRows q n

example (q : ℝ) (n : ℕ) :
    (weightedLagRows q n).natDegree = n := by
  rr_row_natDegree

example {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    HasNonnegCoeffs (weightedLagRows q n) := by
  rr_row_nonneg_coeffs

example {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    Interlaces (weightedLagRows q n) (weightedLagRows q (n + 1)) := by
  rr_row_interlaces

example : True := by
  fail_if_success
    have _ : ∀ (q : ℝ) (n : ℕ), HasNonnegCoeffs (weightedLagRows q n) := by
      intro q n
      rr_row_nonneg_coeffs
  trivial

example : True := by
  fail_if_success
    have _ : Interlaces (weightedLagRows (-4) 1) (weightedLagRows (-4) 2) := by
      rr_row_interlaces
  trivial

/-! ## Issue #2049 application probes

These definitions currently hide their useful recurrence behind another family, a closed
form, or a transform.  The negative probes ensure that merely recognizing fixed parameters
does not make an unsupported route succeed.
-/

open RealRooted.Applications.OEIS

example : True := by
  fail_if_success
    have _ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
        HasNonnegCoeffs (QuarticGamma.polynomial a b n) := by
      rr_row_nonneg_coeffs
  trivial

example : True := by
  fail_if_success
    have _ (r n i : ℕ) : (RealRooted.BinderVecchi.refinedHodgePoincare r n i).Splits := by
      rr_row_splits
  trivial

example : True := by
  fail_if_success
    have _ (r n : ℕ) : (RealRooted.UniformChow.augChowUniform r n).Splits := by
      rr_row_splits
  trivial

end

end RealRooted.Tactic.ParametricRowExamples
