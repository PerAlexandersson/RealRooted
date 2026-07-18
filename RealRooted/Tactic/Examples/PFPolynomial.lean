import RealRooted.Tactic.PFPolynomial

open Polynomial

namespace RealRooted
namespace Tactic

example : IsPFPolynomial (0 : ℝ[X]) := by
  rr_pf_zero

example : IsPFPolynomial (1 : ℝ[X]) := by
  rr_pf_one

example : IsPFPolynomial (X : ℝ[X]) := by
  rr_pf_X

example : IsPFPolynomial (X + 1 : ℝ[X]) := by
  rr_pf_X_add_one

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasNonnegCoeffs p := by
  rr_pf_has_nonneg using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasNonnegCoeffs p := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p = 0 ∨ p.Splits := by
  rr_pf_zero_or_splits using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p = 0 ∨ p.Splits := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p.Splits := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    ∀ r ∈ p.roots, r ≤ 0 := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0) :
    p ≠ 0 ∧ p.Splits := by
  rr_pf using
    pf := hp,
    nonzero := hp0

example {p : ℝ[X]} (hnn : HasNonnegCoeffs p) (hsplits : p.Splits) :
    IsPFPolynomial p := by
  rr_pf_of_nonneg_splits using nonneg := hnn, splits := hsplits

example {p : ℝ[X]} (hnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    IsPFPolynomial p := by
  rr_pf_of_nonneg_zero_or_splits using nonneg := hnn, zero_or_splits := hrr

example {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (C a : ℝ[X]) := by
  rr_pf_C_nonneg using scalar_nonneg := ha

example {a : ℝ} {p : ℝ[X]} (ha : 0 < a) (hp : IsPFPolynomial p) :
    IsPFPolynomial (C a * p) := by
  rr_pf_const_mul using scalar_pos := ha, pf := hp

example {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (X + C a : ℝ[X]) := by
  rr_pf_X_add_C using scalar_nonneg := ha

example {m : ℕ} :
    IsPFPolynomial ((X : ℝ[X]) ^ m) := by
  rr_pf_X_pow using exponent := m

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (X * p) := by
  rr_pf_X_mul using pf := hp

example {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (p * q) := by
  rr_pf_mul using left_pf := hp, right_pf := hq

example {p : ℝ[X]} {n : ℕ} (hp : IsPFPolynomial p) :
    IsPFPolynomial (p ^ n) := by
  rr_pf_pow using pf := hp, exponent := n

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial p.derivative := by
  rr_pf_derivative using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial p.reverse := by
  rr_pf_reverse using pf := hp

example {D : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ D) :
    IsPFPolynomial (reciprocalShift D p) := by
  rr_pf_reciprocal_shift using pf := hp, degree := hdeg

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial ((X + 1) * p) := by
  rr_pf_mul_X_add_one using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Prec0 p p := by
  rr_pf_prec0_self using pf := hp

example {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (X * p) (X * q) := by
  rr_pf_prec0_X_mul_both using left_pf := hp, right_pf := hq, prec0 := hpq

end Tactic
end RealRooted
