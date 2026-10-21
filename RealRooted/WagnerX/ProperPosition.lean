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
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) (_hfnn : HasNonnegCoeffs f) :
    StrictInterl (X * f.derivative) (X * f) := by
  have hder : StrictInterl f.derivative f :=
    (derivative_interlaces_of_natDegree_ne_zero hf (by lia)).toStrictInterl
  simpa using hder.mul_X_sub_C_both 0

end RealRooted
