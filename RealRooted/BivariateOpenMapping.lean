import RealRooted.Mathlib.Analysis.Complex.OpenMapping
import RealRooted.PartialSymmetrization

/-!
# Open mapping for bivariate multiaffine quotients

This file supplies the local nonconstancy input for the open-mapping step in
Borcea--Brändén, Part II, Lemma 1.4.
-/

open Filter Metric Set
open scoped Topology

namespace RealRooted

/-- A nonzero cross determinant makes the bivariate quotient injective wherever
both denominators are nonzero. -/
theorem bivariateQuotient_ne_of_ne
    (a b c d z t : ℂ) (hcross : a * d ≠ b * c)
    (hdenz : c + d * z ≠ 0) (hdent : c + d * t ≠ 0) (hzt : z ≠ t) :
    (a + b * z) / (c + d * z) ≠
      (a + b * t) / (c + d * t) := by
  intro heq
  have hmul := (div_eq_div_iff hdenz hdent).mp heq
  have hzero : (a * d - b * c) * (t - z) = 0 := by
    linear_combination hmul
  exact (mul_ne_zero (sub_ne_zero.mpr hcross)
    (sub_ne_zero.mpr hzt.symm)) hzero

/-- Under the denominator half-plane hypothesis, a nonzero cross determinant
rules out local eventual constancy of the bivariate quotient. -/
theorem bivariateQuotient_not_eventually_constant
    (a b c d z : ℂ) (hcross : a * d ≠ b * c)
    (hcd : 0 < (c / d).im) (hz : 0 < z.im) :
    ¬∀ᶠ t in 𝓝 z,
      (a + b * t) / (c + d * t) = (a + b * z) / (c + d * z) := by
  intro hconst
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hconst
  let t : ℂ := z + (ε / 2 : ℝ)
  have htball : t ∈ ball z ε := by
    rw [mem_ball]
    simp [t, Real.norm_eq_abs, abs_of_pos hε]
    linarith
  have heq := hball htball
  have htne : z ≠ t := by
    intro heq'
    have hre := congrArg Complex.re heq'
    simp [t] at hre
    linarith
  apply bivariateQuotient_ne_of_ne a b c d z t hcross
  · exact add_mul_ne_zero_of_im_div_pos c d z hcd (le_of_lt hz)
  · apply add_mul_ne_zero_of_im_div_pos c d t hcd
    simpa only [t, Complex.add_im, Complex.ofReal_im, add_zero] using le_of_lt hz
  · exact htne
  · change (a + b * t) / (c + d * t) =
      (a + b * z) / (c + d * z) at heq
    exact heq.symm

end RealRooted
