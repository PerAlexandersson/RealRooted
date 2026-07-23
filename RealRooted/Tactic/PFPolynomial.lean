import RealRooted.PFPolynomial

/-!
# PF-polynomial tactic frontends

Thin wrappers for standard closure operations on `IsPFPolynomial`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem pf_sequence_has_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (P i) := fun i =>
  RealRooted.IsPFPolynomial.hasNonnegCoeffs (hP i)

theorem pf_sequence_zero_or_splits
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, P i = 0 ∨ (P i).Splits := fun i =>
  RealRooted.IsPFPolynomial.eq_zero_or_splits (hP i)

theorem pf_sequence_realrooted
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hP0 : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits := fun i =>
  RealRooted.IsPFPolynomial.ne_zero_and_splits (hP i) (hP0 i)

theorem pf_sequence_of_nonneg_splits
    {P : Nat → ℝ[X]}
    (hPnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hPsplits : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, IsPFPolynomial (P i) := fun i =>
  RealRooted.IsPFPolynomial.of_realRooted_nonneg (hPnn i) (hPsplits i)

theorem pf_sequence_of_nonneg_zero_or_splits
    {P : Nat → ℝ[X]}
    (hPnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hPrr : ∀ i : Nat, P i = 0 ∨ (P i).Splits) :
    ∀ i : Nat, IsPFPolynomial (P i) := fun i =>
  RealRooted.IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hPnn i) (hPrr i)

theorem pf_sequence_C_nonneg
    {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 ≤ a i) :
    ∀ i : Nat, IsPFPolynomial (C (a i) : ℝ[X]) := fun i =>
  RealRooted.IsPFPolynomial.of_C_nonneg (ha i)

theorem pf_sequence_const_mul
    {a : Nat → ℝ} {P : Nat → ℝ[X]}
    (ha : ∀ i : Nat, 0 < a i)
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (C (a i) * P i) := fun i =>
  RealRooted.IsPFPolynomial.const_mul (ha i) (hP i)

theorem pf_sequence_X_add_C
    {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 ≤ a i) :
    ∀ i : Nat, IsPFPolynomial (X + C (a i) : ℝ[X]) := fun i =>
  RealRooted.isPFPolynomial_X_add_C (ha i)

theorem pf_sequence_X_pow
    {m : Nat → Nat} :
    ∀ i : Nat, IsPFPolynomial ((X : ℝ[X]) ^ m i) := fun i =>
  RealRooted.isPFPolynomial_X_pow (m i)

theorem pf_sequence_X_mul
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (X * P i) := fun i =>
  RealRooted.IsPFPolynomial.X_mul (hP i)

theorem pf_sequence_mul
    {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i)) :
    ∀ i : Nat, IsPFPolynomial (P i * Q i) := fun i =>
  RealRooted.IsPFPolynomial.mul (hP i) (hQ i)

theorem pf_sequence_pow
    {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial ((P i) ^ m i) := fun i =>
  RealRooted.IsPFPolynomial.pow (hP i) (m i)

theorem pf_sequence_derivative
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (P i).derivative := fun i =>
  RealRooted.IsPFPolynomial.derivative (hP i)

theorem pf_sequence_reverse
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (P i).reverse := fun i =>
  RealRooted.IsPFPolynomial.reverse (hP i)

theorem pf_sequence_reciprocal_shift
    {D : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ D i) :
    ∀ i : Nat, IsPFPolynomial (reciprocalShift (D i) (P i)) := fun i =>
  RealRooted.reciprocalShift_preserves_pf (hP i) (hdeg i)

theorem pf_sequence_mul_X_add_one
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial ((X + 1) * P i) := fun i =>
  RealRooted.isPFPolynomial_mul_X_add_one (hP i)

theorem pf_sequence_prec0_self
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, Prec0 (P i) (P i) := fun i =>
  RealRooted.IsPFPolynomial.prec0_self (hP i)

theorem pf_sequence_prec0_X_mul_both
    {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hPQ : ∀ i : Nat, Prec0 (P i) (Q i)) :
    ∀ i : Nat, Prec0 (X * P i) (X * Q i) := fun i =>
  RealRooted.prec0_X_mul_both_of_pf (hP i) (hQ i) (hPQ i)

syntax (name := rr_pf_zero_named) "rr_pf_zero" : tactic
syntax (name := rr_pf_one_named) "rr_pf_one" : tactic
syntax (name := rr_pf_X_named) "rr_pf_X" : tactic
syntax (name := rr_pf_X_add_one_named) "rr_pf_X_add_one" : tactic

syntax (name := rr_pf_using_named)
  "rr_pf" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_using_nonzero_named)
  "rr_pf" " using "
    "pf" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_pf_has_nonneg_named)
  "rr_pf_has_nonneg" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_has_nonneg_named)
  "rr_pf_sequence_has_nonneg" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_zero_or_splits_named)
  "rr_pf_zero_or_splits" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_zero_or_splits_named)
  "rr_pf_sequence_zero_or_splits" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_realrooted_named)
  "rr_pf_sequence_realrooted" " using "
    "pf" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_pf_of_nonneg_splits_named)
  "rr_pf_of_nonneg_splits" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_pf_sequence_of_nonneg_splits_named)
  "rr_pf_sequence_of_nonneg_splits" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_pf_of_nonneg_zero_or_splits_named)
  "rr_pf_of_nonneg_zero_or_splits" " using "
    "nonneg" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic

syntax (name := rr_pf_sequence_of_nonneg_zero_or_splits_named)
  "rr_pf_sequence_of_nonneg_zero_or_splits" " using "
    "nonneg" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic

syntax (name := rr_pf_C_nonneg_named)
  "rr_pf_C_nonneg" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_pf_sequence_C_nonneg_named)
  "rr_pf_sequence_C_nonneg" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_pf_const_mul_named)
  "rr_pf_const_mul" " using "
    "scalar_pos" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_const_mul_named)
  "rr_pf_sequence_const_mul" " using "
    "scalar_pos" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_pf_X_add_C_named)
  "rr_pf_X_add_C" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_pf_sequence_X_add_C_named)
  "rr_pf_sequence_X_add_C" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_pf_X_pow_named)
  "rr_pf_X_pow" " using " "exponent" ":=" term :
  tactic

syntax (name := rr_pf_sequence_X_pow_named)
  "rr_pf_sequence_X_pow" " using " "exponent" ":=" term :
  tactic

syntax (name := rr_pf_X_mul_named)
  "rr_pf_X_mul" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_X_mul_named)
  "rr_pf_sequence_X_mul" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_mul_named)
  "rr_pf_mul" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_mul_named)
  "rr_pf_sequence_mul" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

syntax (name := rr_pf_pow_named)
  "rr_pf_pow" " using "
    "pf" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_pf_sequence_pow_named)
  "rr_pf_sequence_pow" " using "
    "pf" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_pf_derivative_named)
  "rr_pf_derivative" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_derivative_named)
  "rr_pf_sequence_derivative" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_reverse_named)
  "rr_pf_reverse" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_reverse_named)
  "rr_pf_sequence_reverse" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_reciprocal_shift_named)
  "rr_pf_reciprocal_shift" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_pf_sequence_reciprocal_shift_named)
  "rr_pf_sequence_reciprocal_shift" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_pf_mul_X_add_one_named)
  "rr_pf_mul_X_add_one" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_mul_X_add_one_named)
  "rr_pf_sequence_mul_X_add_one" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_prec0_self_named)
  "rr_pf_prec0_self" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_sequence_prec0_self_named)
  "rr_pf_sequence_prec0_self" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_prec0_X_mul_both_named)
  "rr_pf_prec0_X_mul_both" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

syntax (name := rr_pf_sequence_prec0_X_mul_both_named)
  "rr_pf_sequence_prec0_X_mul_both" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_pf_zero) =>
      `(tactic| exact RealRooted.IsPFPolynomial.zero)
  | `(tactic| rr_pf_one) =>
      `(tactic| exact RealRooted.IsPFPolynomial.one)
  | `(tactic| rr_pf_X) =>
      `(tactic| exact RealRooted.isPFPolynomial_X)
  | `(tactic| rr_pf_X_add_one) =>
      `(tactic| exact RealRooted.isPFPolynomial_X_add_one)
  | `(tactic| rr_pf using pf := $hp:term) =>
      `(tactic|
        first
          | exact $hp
          | exact RealRooted.IsPFPolynomial.hasNonnegCoeffs $hp
          | exact RealRooted.IsPFPolynomial.eq_zero_or_splits $hp
          | exact RealRooted.IsPFPolynomial.roots_nonpos $hp
          | (rcases RealRooted.IsPFPolynomial.eq_zero_or_splits $hp with hzero | hsplits
             · rw [hzero]
               simp
             · exact hsplits))
  | `(tactic|
      rr_pf using
        pf := $hp:term,
        nonzero := $hp0:term) =>
      `(tactic|
        first
          | rr_pf using pf := $hp
          | exact $hp0
          | exact RealRooted.IsPFPolynomial.ne_zero_and_splits $hp $hp0)
  | `(tactic| rr_pf_has_nonneg using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.hasNonnegCoeffs $hp)
  | `(tactic| rr_pf_sequence_has_nonneg using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_has_nonneg $hp)
  | `(tactic| rr_pf_zero_or_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.eq_zero_or_splits $hp)
  | `(tactic| rr_pf_sequence_zero_or_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_zero_or_splits $hp)
  | `(tactic|
      rr_pf_sequence_realrooted using
        pf := $hp:term,
        nonzero := $hp0:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_realrooted $hp $hp0)
  | `(tactic|
      rr_pf_of_nonneg_splits using
        nonneg := $hnn:term,
        splits := $hsplits:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.of_realRooted_nonneg $hnn $hsplits)
  | `(tactic|
      rr_pf_sequence_of_nonneg_splits using
        nonneg := $hnn:term,
        splits := $hsplits:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_of_nonneg_splits $hnn $hsplits)
  | `(tactic|
      rr_pf_of_nonneg_zero_or_splits using
        nonneg := $hnn:term,
        zero_or_splits := $hrr:term) =>
      `(tactic|
        exact RealRooted.IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
          $hnn $hrr)
  | `(tactic|
      rr_pf_sequence_of_nonneg_zero_or_splits using
        nonneg := $hnn:term,
        zero_or_splits := $hrr:term) =>
      `(tactic|
        exact RealRooted.Tactic.pf_sequence_of_nonneg_zero_or_splits
          $hnn $hrr)
  | `(tactic| rr_pf_C_nonneg using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.of_C_nonneg $ha)
  | `(tactic| rr_pf_sequence_C_nonneg using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_C_nonneg $ha)
  | `(tactic|
      rr_pf_const_mul using
        scalar_pos := $ha:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.const_mul $ha $hp)
  | `(tactic|
      rr_pf_sequence_const_mul using
        scalar_pos := $ha:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_const_mul $ha $hp)
  | `(tactic| rr_pf_X_add_C using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_X_add_C $ha)
  | `(tactic| rr_pf_sequence_X_add_C using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_X_add_C $ha)
  | `(tactic| rr_pf_X_pow using exponent := $n:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_X_pow $n)
  | `(tactic| rr_pf_sequence_X_pow using exponent := $n:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_X_pow (m := $n))
  | `(tactic| rr_pf_X_mul using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.X_mul $hp)
  | `(tactic| rr_pf_sequence_X_mul using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_X_mul $hp)
  | `(tactic|
      rr_pf_mul using
        left_pf := $hp:term,
        right_pf := $hq:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.mul $hp $hq)
  | `(tactic|
      rr_pf_sequence_mul using
        left_pf := $hp:term,
        right_pf := $hq:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_mul $hp $hq)
  | `(tactic|
      rr_pf_pow using
        pf := $hp:term,
        exponent := $n:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.pow $hp $n)
  | `(tactic|
      rr_pf_sequence_pow using
        pf := $hp:term,
        exponent := $n:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_pow (m := $n) $hp)
  | `(tactic| rr_pf_derivative using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.derivative $hp)
  | `(tactic| rr_pf_sequence_derivative using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_derivative $hp)
  | `(tactic| rr_pf_reverse using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.reverse $hp)
  | `(tactic| rr_pf_sequence_reverse using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_reverse $hp)
  | `(tactic|
      rr_pf_reciprocal_shift using
        pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.reciprocalShift_preserves_pf $hp $hdeg)
  | `(tactic|
      rr_pf_sequence_reciprocal_shift using
        pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_reciprocal_shift $hp $hdeg)
  | `(tactic| rr_pf_mul_X_add_one using pf := $hp:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_mul_X_add_one $hp)
  | `(tactic| rr_pf_sequence_mul_X_add_one using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_mul_X_add_one $hp)
  | `(tactic| rr_pf_prec0_self using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.prec0_self $hp)
  | `(tactic| rr_pf_sequence_prec0_self using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_prec0_self $hp)
  | `(tactic|
      rr_pf_prec0_X_mul_both using
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.prec0_X_mul_both_of_pf $hp $hq $hpq)
  | `(tactic|
      rr_pf_sequence_prec0_X_mul_both using
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic|
        exact RealRooted.Tactic.pf_sequence_prec0_X_mul_both
          $hp $hq $hpq)

end Tactic
end RealRooted
