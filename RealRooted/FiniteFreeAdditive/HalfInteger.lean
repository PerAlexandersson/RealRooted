import RealRooted.FiniteFreeAdditive
import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.RectangularConvolution

/-!
# Half-integer kernels for finite-free additive convolution

This file relates the finite-free additive kernel to a generalized rectangular
kernel built from descending Pochhammer ratios.  It proves only coefficient
identities.  Polynomial convolution identities and root-preservation results
are deliberately left to later layers.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The generalized rectangular coefficient kernel with real shift `α`. -/
def generalizedRectangularConvolutionGamma (α : ℝ) (n i j : ℕ) : ℝ :=
  Polynomial.descPochhammerRatio (n : ℝ) i j *
    Polynomial.descPochhammerRatio ((n : ℝ) + α) i j

/-- Inside the degree triangle, the finite-free additive kernel is its
natural-parameter descending-Pochhammer ratio. -/
theorem finiteFreeAdditiveConvolutionGamma_eq_descPochhammerRatio (d i j : ℕ)
    (hij : i + j ≤ d) :
    finiteFreeAdditiveConvolutionGamma d i j =
      Polynomial.descPochhammerRatio (d : ℝ) i j := by
  rw [finiteFreeAdditiveConvolutionGamma_eq_descFactorial_ratio d i j hij]
  unfold Polynomial.descPochhammerRatio
  rw [descPochhammer_eval_eq_descFactorial,
    descPochhammer_eval_eq_descFactorial,
    descPochhammer_eval_eq_descFactorial]

/-- At a natural parameter, the generalized Pochhammer kernel recovers the
existing rectangular additive-convolution kernel inside its degree triangle. -/
theorem generalizedRectangularConvolutionGamma_nat_eq_rectangular (m n i j : ℕ)
    (hij : i + j ≤ n) :
    generalizedRectangularConvolutionGamma (m : ℝ) n i j =
      rectangularConvolutionGamma m n i j := by
  unfold generalizedRectangularConvolutionGamma
  rw [show (n : ℝ) + (m : ℝ) = (n + m : ℕ) by push_cast; ring]
  rw [← finiteFreeAdditiveConvolutionGamma_eq_descPochhammerRatio n i j hij,
    ← finiteFreeAdditiveConvolutionGamma_eq_descPochhammerRatio (n + m) i j (by lia)]
  rfl

/-- The even finite-free additive kernel is the generalized rectangular
kernel at shift `-1 / 2`. -/
theorem finiteFreeAdditiveConvolutionGamma_even_eq_generalized (n i j : ℕ)
    (hij : i + j ≤ n) :
    finiteFreeAdditiveConvolutionGamma (2 * n) (2 * i) (2 * j) =
      generalizedRectangularConvolutionGamma (-(1 / 2 : ℝ)) n i j := by
  rw [finiteFreeAdditiveConvolutionGamma_eq_descPochhammerRatio _ _ _ (by lia)]
  unfold generalizedRectangularConvolutionGamma
  convert Polynomial.descPochhammerRatio_two_mul (n : ℝ) i j using 1 <;>
    push_cast <;> ring_nf

/-- The odd finite-free additive kernel is the generalized rectangular
kernel at shift `1 / 2`. -/
theorem finiteFreeAdditiveConvolutionGamma_odd_eq_generalized (n i j : ℕ)
    (hij : i + j ≤ n) :
    finiteFreeAdditiveConvolutionGamma (2 * n + 1) (2 * i) (2 * j) =
      generalizedRectangularConvolutionGamma (1 / 2 : ℝ) n i j := by
  rw [finiteFreeAdditiveConvolutionGamma_eq_descPochhammerRatio _ _ _ (by lia)]
  unfold generalizedRectangularConvolutionGamma
  convert Polynomial.descPochhammerRatio_two_mul ((n : ℝ) + 1 / 2) i j using 1 <;>
    push_cast <;> ring_nf

end

end RealRooted
