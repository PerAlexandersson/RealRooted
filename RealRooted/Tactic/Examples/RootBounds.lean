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

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 := by
  rr_root_nonpos

example {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hpnn : HasNonnegCoeffs p) {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 := by
  rr_root_nonpos using hp_ne, hp_splits, hpnn, hr

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hder_ne : p.derivative ≠ 0) {r : ℝ} (hr : p.derivative.IsRoot r) :
    r ≤ 0 := by
  rr_derivative_root_nonpos using
    realrooted := hrr,
    nonneg := hpnn,
    derivative_ne := hder_ne,
    root := hr

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hder_ne : p.derivative ≠ 0) {r : ℝ} (hr : p.derivative.IsRoot r) :
    r ≤ 0 := by
  rr_derivative_root_nonpos

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (C (3 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using
    realrooted := hrr,
    nonneg := hpnn

example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → (-(C (1 : ℝ)) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

example {p q : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hq : ∀ r, p.IsRoot r → 0 ≤ q.eval r) :
    ∀ r, p.IsRoot r → (X * q : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_with_factor using hrr, hpnn, hq

example {p q : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hq : ∀ r, p.IsRoot r → 0 ≤ q.eval r) :
    ∀ r, p.IsRoot r → (X * q : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_with_factor using
    factor_nonneg := hq

example {p q : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hq : ∀ r, p.IsRoot r → 0 ≤ q.eval r) :
    ∀ r, p.IsRoot r → (C (3 : ℝ) * X * q : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_with_factor using
    realrooted := hrr,
    nonneg := hpnn,
    factor_nonneg := hq

example {p : ℝ[X]}
    (hhi : ∀ r, p.IsRoot r → r ≤ -1) :
    ∀ r, p.IsRoot r → (1 + X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_upper using hhi

example {p : ℝ[X]}
    (hhi : ∀ r, p.IsRoot r → r ≤ 1) :
    ∀ r, p.IsRoot r → (X - 1 : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_upper using
    root_upper := hhi

example {p : ℝ[X]}
    (hlo : ∀ r, p.IsRoot r → -1 ≤ r)
    (hhi : ∀ r, p.IsRoot r → r ≤ 0) :
    ∀ r, p.IsRoot r → (X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_window using hlo, hhi

example {p : ℝ[X]}
    (hlo : ∀ r, p.IsRoot r → -1 ≤ r)
    (hhi : ∀ r, p.IsRoot r → r ≤ -(1 / 2 : ℝ)) :
    ∀ r, p.IsRoot r →
      ((1 + X) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots_window using
    root_lower := hlo,
    root_upper := hhi

end Tactic
end RealRooted
