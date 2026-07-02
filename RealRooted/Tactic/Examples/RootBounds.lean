import RealRooted.Tactic.RootBounds

/-!
# `rr_root_nonpos` and `rr_sign_at_roots` examples

Regression tests for root-interval propagation from real-rootedness plus
nonnegative coefficients.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 := by
  rr_root_nonpos using hrr, hpnn, hr

example {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hpnn : HasNonnegCoeffs p) {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 := by
  rr_root_nonpos using hp_ne, hp_splits, hpnn, hr

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (C (3 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using
    realrooted := hrr,
    nonneg := hpnn

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (-(C (1 : ℝ)) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

end Tactic
end RealRooted
