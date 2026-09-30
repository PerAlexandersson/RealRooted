import RealRooted.Derivative
import RealRooted.WagnerX

/-!
# Wagner `X`-multiplication interlacing bridges

The forward and reverse interlacing transports associated with multiplying
a nonnegative-coefficient polynomial by `X`.
-/

open Polynomial

namespace RealRooted

/-- The derivative of a split nonnegative-coefficient polynomial preserves the
Wagner `X`-multiplication interlacing relation. -/
theorem strictInterl_X_derivative_X_self_of_splits_nonneg {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) (hfnn : HasNonnegCoeffs f) :
    StrictInterl (X * f.derivative) (X * f) := by
  have hder : StrictInterl f.derivative f := (derivative_interlaces hf hdeg).toStrictInterl
  exact hder.mul_X_both_of_roots_nonpos
    (roots_nonpos_of_nonneg_coeffs hder.1.2 hfnn.derivative)
    (roots_nonpos_of_nonneg_coeffs hf hfnn)

end RealRooted
