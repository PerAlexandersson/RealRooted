module

import RealRooted.AffineDerivative
public import RealRooted.Tactic.Finish
import RealRooted.SequenceClosure
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Affine-derivative family lemmas

Pointwise lifts of the affine-derivative interlacing theorem
`C c * f + (1 - X) * f.derivative`.
-/

public section

open Polynomial

namespace RealRooted

/-- A pointwise split family of positive-leading polynomials with nonpositive
roots is strictly interlaced by its affine derivatives when each scalar
exceeds the corresponding positive degree. -/
theorem strictInterl_affine_derivative_sequence {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroots_nonpos : ∀ n : Nat, ∀ r ∈ (P n).roots, r ≤ 0)
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat, StrictInterl
      (C (c n) * P n + (1 - X) * (P n).derivative)
      (P n) := fun n =>
  strictInterl_affine_derivative' (hsplits n) (hdeg n) (hpos n)
    (hroots_nonpos n) (hc n)

/-- Under the hypotheses of `strictInterl_affine_derivative_sequence`, every
affine derivative is nonzero and split. -/
theorem isRealRooted_of_strictInterl_affine_derivative_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroots_nonpos : ∀ n : Nat, ∀ r ∈ (P n).roots, r ≤ 0)
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat,
      C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 ∧
        (C (c n) * P n + (1 - X) * (P n).derivative).Splits :=
  left_isRealRooted_of_strictInterl_sequence <|
    strictInterl_affine_derivative_sequence hsplits hdeg hpos hroots_nonpos hc

/-- A pointwise split family with nonnegative coefficients is strictly
interlaced by its affine derivatives when each scalar exceeds the corresponding
positive degree. -/
theorem strictInterl_affine_derivative_nonneg_sequence {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat, StrictInterl
      (C (c n) * P n + (1 - X) * (P n).derivative)
      (P n) := fun n =>
  strictInterl_affine_derivative_of_nonnegCoeffs (hsplits n) (hdeg n) (hnn n) (hc n)

/-- Under the hypotheses of
`strictInterl_affine_derivative_nonneg_sequence`, every affine derivative is
nonzero and split. -/
theorem isRealRooted_of_strictInterl_affine_derivative_nonneg_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hc : ∀ n : Nat, ((P n).natDegree : ℝ) < c n) :
    ∀ n : Nat,
      C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 ∧
        (C (c n) * P n + (1 - X) * (P n).derivative).Splits :=
  left_isRealRooted_of_strictInterl_sequence <|
    strictInterl_affine_derivative_nonneg_sequence hsplits hdeg hnn hc

/-- For a pointwise positive-degree family, the top-degree coefficient of each
affine derivative is the scalar-minus-degree factor times the original leading
coefficient. -/
theorem coeff_affineDeriv_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).coeff (P n).natDegree =
        (c n - (P n).natDegree) * (P n).leadingCoeff := fun n =>
  coeff_affineDeriv (hdeg n) (c n)

/-- Affine derivatives preserve degree pointwise when the input is nonzero, has
positive degree, and the scalar differs from that degree. -/
theorem natDegree_affineDeriv_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).natDegree =
        (P n).natDegree := fun n =>
  natDegree_affineDeriv (hne n) (hdeg n) (hc n)

/-- Under the pointwise nonzero, positive-degree, and scalar-not-degree
hypotheses, the affine derivative has the expected leading coefficient. -/
theorem leadingCoeff_affineDeriv_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat,
      (C (c n) * P n + (1 - X) * (P n).derivative).leadingCoeff =
        (c n - (P n).natDegree) * (P n).leadingCoeff := fun n =>
  leadingCoeff_affineDeriv (hne n) (hdeg n) (hc n)

/-- Affine derivatives are pointwise nonzero when the input is nonzero, has
positive degree, and the scalar differs from that degree. -/
theorem affineDeriv_ne_zero_sequence
    {P : Nat → ℝ[X]} {c : Nat → ℝ}
    (hne : ∀ n : Nat, P n ≠ 0)
    (hdeg : ∀ n : Nat, 1 ≤ (P n).natDegree)
    (hc : ∀ n : Nat, c n ≠ ((P n).natDegree : ℝ)) :
    ∀ n : Nat, C (c n) * P n + (1 - X) * (P n).derivative ≠ 0 := fun n =>
  affineDeriv_ne_zero (hne n) (hdeg n) (hc n)

namespace Tactic

end Tactic
end RealRooted

