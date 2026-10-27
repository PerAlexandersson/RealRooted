module

public import RealRooted.Derivative
public import RealRooted.WagnerX

/-!
# Wagner `X`-multiplication interlacing bridges

The forward and reverse interlacing transports associated with multiplying
a polynomial by `X`.
-/

public section

open Polynomial

namespace RealRooted

/-- The derivative of a split polynomial preserves the common-`X`
strict-interlacing relation in degree at least two. -/
theorem strictInterl_X_derivative_X_self_of_splits {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) :
    StrictInterl (X * f.derivative) (X * f) := by
  have hder : StrictInterl f.derivative f :=
    (derivative_interlaces_of_natDegree_ne_zero hf (by lia)).toStrictInterl
  simpa using hder.mul_X_sub_C_both 0

/-- Compatibility form retaining the former nonnegative-coefficient
hypothesis. -/
@[deprecated strictInterl_X_derivative_X_self_of_splits +typeChanged (since := "2026-10-21")]
theorem strictInterl_X_derivative_X_self_of_splits_nonneg {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) (_hfnn : HasNonnegCoeffs f) :
    StrictInterl (X * f.derivative) (X * f) :=
  strictInterl_X_derivative_X_self_of_splits hf hdeg

end RealRooted
