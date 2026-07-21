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

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (P i) := by
  rr_pf_sequence_has_nonneg using pf := hP

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasNonnegCoeffs p := by
  rr_pf using pf := hp

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p = 0 ∨ p.Splits := by
  rr_pf_zero_or_splits using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, P i = 0 ∨ (P i).Splits := by
  rr_pf_sequence_zero_or_splits using pf := hP

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

example {P : Nat → ℝ[X]}
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hsplits : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, IsPFPolynomial (P i) := by
  rr_pf_sequence_of_nonneg_splits using
    nonneg := hnn,
    splits := hsplits

example {p : ℝ[X]} (hnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    IsPFPolynomial p := by
  rr_pf_of_nonneg_zero_or_splits using nonneg := hnn, zero_or_splits := hrr

example {P : Nat → ℝ[X]}
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hrr : ∀ i : Nat, P i = 0 ∨ (P i).Splits) :
    ∀ i : Nat, IsPFPolynomial (P i) := by
  rr_pf_sequence_of_nonneg_zero_or_splits using
    nonneg := hnn,
    zero_or_splits := hrr

example {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (C a : ℝ[X]) := by
  rr_pf_C_nonneg using scalar_nonneg := ha

example {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 ≤ a i) :
    ∀ i : Nat, IsPFPolynomial (C (a i) : ℝ[X]) := by
  rr_pf_sequence_C_nonneg using scalar_nonneg := ha

example {a : ℝ} {p : ℝ[X]} (ha : 0 < a) (hp : IsPFPolynomial p) :
    IsPFPolynomial (C a * p) := by
  rr_pf_const_mul using scalar_pos := ha, pf := hp

example {a : Nat → ℝ} {P : Nat → ℝ[X]}
    (ha : ∀ i : Nat, 0 < a i)
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (C (a i) * P i) := by
  rr_pf_sequence_const_mul using
    scalar_pos := ha,
    pf := hP

example {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (X + C a : ℝ[X]) := by
  rr_pf_X_add_C using scalar_nonneg := ha

example {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 ≤ a i) :
    ∀ i : Nat, IsPFPolynomial (X + C (a i) : ℝ[X]) := by
  rr_pf_sequence_X_add_C using scalar_nonneg := ha

example {m : ℕ} :
    IsPFPolynomial ((X : ℝ[X]) ^ m) := by
  rr_pf_X_pow using exponent := m

example {m : Nat → Nat} :
    ∀ i : Nat, IsPFPolynomial ((X : ℝ[X]) ^ m i) := by
  rr_pf_sequence_X_pow using exponent := m

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (X * p) := by
  rr_pf_X_mul using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (X * P i) := by
  rr_pf_sequence_X_mul using pf := hP

example {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (p * q) := by
  rr_pf_mul using left_pf := hp, right_pf := hq

example {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i)) :
    ∀ i : Nat, IsPFPolynomial (P i * Q i) := by
  rr_pf_sequence_mul using
    left_pf := hP,
    right_pf := hQ

example {p : ℝ[X]} {n : ℕ} (hp : IsPFPolynomial p) :
    IsPFPolynomial (p ^ n) := by
  rr_pf_pow using pf := hp, exponent := n

example {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial ((P i) ^ m i) := by
  rr_pf_sequence_pow using
    pf := hP,
    exponent := m

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial p.derivative := by
  rr_pf_derivative using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (P i).derivative := by
  rr_pf_sequence_derivative using pf := hP

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial p.reverse := by
  rr_pf_reverse using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (P i).reverse := by
  rr_pf_sequence_reverse using pf := hP

example {D : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ D) :
    IsPFPolynomial (reciprocalShift D p) := by
  rr_pf_reciprocal_shift using pf := hp, degree := hdeg

example {D : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ D i) :
    ∀ i : Nat, IsPFPolynomial (reciprocalShift (D i) (P i)) := by
  rr_pf_sequence_reciprocal_shift using
    pf := hP,
    degree := hdeg

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial ((X + 1) * p) := by
  rr_pf_mul_X_add_one using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial ((X + 1) * P i) := by
  rr_pf_sequence_mul_X_add_one using pf := hP

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Prec0 p p := by
  rr_pf_prec0_self using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, Prec0 (P i) (P i) := by
  rr_pf_sequence_prec0_self using pf := hP

example {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (X * p) (X * q) := by
  rr_pf_prec0_X_mul_both using left_pf := hp, right_pf := hq, prec0 := hpq

example {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hPQ : ∀ i : Nat, Prec0 (P i) (Q i)) :
    ∀ i : Nat, Prec0 (X * P i) (X * Q i) := by
  rr_pf_sequence_prec0_X_mul_both using
    left_pf := hP,
    right_pf := hQ,
    prec0 := hPQ

end Tactic
end RealRooted
