import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Rescale
import Mathlib.Analysis.Real.Sqrt

/-!
# Real square-root normalization of quadratic recurrences

This opt-in specialization of `quadraticRescale_isSolution` records the
algebraic normalization used for the A272471 recurrence.  It does not provide
Chebyshev closed forms, trigonometric identities, or analytic estimates.
-/

namespace LinearRecurrence

/-- A positive real constant term can be normalized to `-1` by rescaling with
its positive square root. -/
theorem quadraticRescale_sqrt_isSolution {p w : ℝ} {D : ℕ → ℝ} (hw : 0 < w)
    (hD : (quadratic p (-w)).IsSolution D) :
    (quadratic (p / Real.sqrt w) (-1)).IsSolution
      (quadraticRescale (Real.sqrt w) D) := by
  have hs : Real.sqrt w ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hw)
  have hsq : Real.sqrt w ^ 2 = w := by
    rw [pow_two]
    exact Real.mul_self_sqrt hw.le
  have h := quadraticRescale_isSolution (p := p) (q := -w)
    (s := Real.sqrt w) hs hD
  rw [hsq] at h
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hq : -w / w = (-1 : ℝ) := by
    rw [neg_div, div_self hw0]
  rw [hq] at h
  exact h

end LinearRecurrence
