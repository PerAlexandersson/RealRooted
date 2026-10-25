module

public import RealRooted.PFPolynomial

/-!
# PF-polynomial tactic frontends and model transport

The model transport theorem preserves PF rows and consecutive `Interl` through
pointwise sequence identification. The remaining declarations are thin tactic
wrappers for standard closure operations on `IsPFPolynomial`.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- Transfer PF rows and consecutive zero-aware proper position from a
rowwise equal model sequence. -/
theorem pf_and_interl_of_model_sequence
    {P Q : Nat → ℝ[X]}
    (hmodel :
      (∀ n : Nat, IsPFPolynomial (Q n)) ∧
        ∀ n : Nat, Interl (Q n) (Q (n + 1)))
    (hidentify : ∀ n : Nat, P n = Q n) :
    (∀ n : Nat, IsPFPolynomial (P n)) ∧
      ∀ n : Nat, Interl (P n) (P (n + 1)) := by
  constructor
  · intro n
    rw [hidentify n]
    exact hmodel.1 n
  · intro n
    rw [hidentify n, hidentify (n + 1)]
    exact hmodel.2 n

namespace Tactic

theorem pf_splits
    {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    p.Splits := by
  rcases RealRooted.IsPFPolynomial.eq_zero_or_splits hp with rfl | hsplits
  · simp
  · exact hsplits

theorem pf_sequence_has_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (P i) := fun i =>
  RealRooted.IsPFPolynomial.hasNonnegCoeffs (hP i)

theorem pf_sequence_splits
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, (P i).Splits := fun i =>
  pf_splits (hP i)

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

/-- A family of PF polynomials has Pólya-frequency coefficient sequences. -/
theorem pf_sequence_to_coefficient_sequence
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPolyaFreqSeq (fun n => (P i).coeff n) := fun i =>
  RealRooted.IsPFPolynomial.to_sequence (hP i)

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

theorem pf_sequence_interl_self
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, Interl (P i) (P i) := fun i =>
  RealRooted.IsPFPolynomial.interl_self (hP i)

theorem interl_sequence_mul_X_both
    {P Q : Nat → ℝ[X]} (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ i : Nat, Interl (X * P i) (X * Q i) := fun i =>
  (hPQ i).mul_X_both

/-- Closes `IsPFPolynomial 0`. -/
syntax (name := rr_pf_zero_named) "rr_pf_zero" : tactic
/-- Closes `IsPFPolynomial 1`. -/
syntax (name := rr_pf_one_named) "rr_pf_one" : tactic
/-- Closes `IsPFPolynomial X`. -/
syntax (name := rr_pf_X_named) "rr_pf_X" : tactic
/-- Closes `IsPFPolynomial (X + 1)`. -/
syntax (name := rr_pf_X_add_one_named) "rr_pf_X_add_one" : tactic

/-- Closes a goal about `p` from `pf : IsPFPolynomial p`, trying in turn `pf` itself,
`HasNonnegCoeffs p`, `p = 0 ∨ p.Splits`, the nonpositivity of the roots of `p`, `p.Splits`, and the
PF property of the coefficient sequence of `p`. -/
syntax (name := rr_pf_using_named)
  "rr_pf" " using " "pf" ":=" term :
  tactic

/-- Variant of `rr_pf using ...` that also takes `nonzero : p ≠ 0`, so that it can close `p ≠ 0` and
`p ≠ 0 ∧ p.Splits`. -/
syntax (name := rr_pf_using_nonzero_named)
  "rr_pf" " using "
    "pf" ":=" term ","
    "nonzero" ":=" term :
  tactic

/-- Closes `HasNonnegCoeffs p` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_has_nonneg_named)
  "rr_pf_has_nonneg" " using " "pf" ":=" term :
  tactic

/-- Closes `p.Splits` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_splits_named)
  "rr_pf_splits" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_has_nonneg`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_has_nonneg_named)
  "rr_pf_sequence_has_nonneg" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_splits`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_splits_named)
  "rr_pf_sequence_splits" " using " "pf" ":=" term :
  tactic

/-- Closes `p = 0 ∨ p.Splits` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_zero_or_splits_named)
  "rr_pf_zero_or_splits" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_zero_or_splits`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_zero_or_splits_named)
  "rr_pf_sequence_zero_or_splits" " using " "pf" ":=" term :
  tactic

/-- Closes `∀ i, P i ≠ 0 ∧ (P i).Splits` from `pf : ∀ i, IsPFPolynomial (P i)` and
`nonzero : ∀ i, P i ≠ 0`. -/
syntax (name := rr_pf_sequence_realrooted_named)
  "rr_pf_sequence_realrooted" " using "
    "pf" ":=" term ","
    "nonzero" ":=" term :
  tactic

/-- Closes `IsPolyaFreqSeq (fun n => p.coeff n)` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_to_coefficient_sequence_named)
  "rr_pf_to_coefficient_sequence" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_to_coefficient_sequence`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pf_sequence_to_coefficient_sequence_named)
  "rr_pf_sequence_to_coefficient_sequence" " using " "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial p` from `nonneg : HasNonnegCoeffs p` and `splits : p.Splits`. -/
syntax (name := rr_pf_of_nonneg_splits_named)
  "rr_pf_of_nonneg_splits" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Sequence form of `rr_pf_of_nonneg_splits`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_of_nonneg_splits_named)
  "rr_pf_sequence_of_nonneg_splits" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Closes `IsPFPolynomial p` from `nonneg : HasNonnegCoeffs p` and
`zero_or_splits : p = 0 ∨ p.Splits`. -/
syntax (name := rr_pf_of_nonneg_zero_or_splits_named)
  "rr_pf_of_nonneg_zero_or_splits" " using "
    "nonneg" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic

/-- Sequence form of `rr_pf_of_nonneg_zero_or_splits`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pf_sequence_of_nonneg_zero_or_splits_named)
  "rr_pf_sequence_of_nonneg_zero_or_splits" " using "
    "nonneg" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (C a)` from `scalar_nonneg : 0 ≤ a`. -/
syntax (name := rr_pf_C_nonneg_named)
  "rr_pf_C_nonneg" " using " "scalar_nonneg" ":=" term :
  tactic

/-- Sequence form of `rr_pf_C_nonneg`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_C_nonneg_named)
  "rr_pf_sequence_C_nonneg" " using " "scalar_nonneg" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (C a * p)` from `scalar_pos : 0 < a` and `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_const_mul_named)
  "rr_pf_const_mul" " using "
    "scalar_pos" ":=" term ","
    "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_const_mul`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_const_mul_named)
  "rr_pf_sequence_const_mul" " using "
    "scalar_pos" ":=" term ","
    "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (X + C a)` from `scalar_nonneg : 0 ≤ a`. -/
syntax (name := rr_pf_X_add_C_named)
  "rr_pf_X_add_C" " using " "scalar_nonneg" ":=" term :
  tactic

/-- Sequence form of `rr_pf_X_add_C`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_X_add_C_named)
  "rr_pf_sequence_X_add_C" " using " "scalar_nonneg" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (X ^ m)` for the given `exponent : m`. -/
syntax (name := rr_pf_X_pow_named)
  "rr_pf_X_pow" " using " "exponent" ":=" term :
  tactic

/-- Sequence form of `rr_pf_X_pow`: closes `∀ i, IsPFPolynomial (X ^ m i)` for the `exponent : m`, a
function `ℕ → ℕ`. -/
syntax (name := rr_pf_sequence_X_pow_named)
  "rr_pf_sequence_X_pow" " using " "exponent" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (X * p)` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_X_mul_named)
  "rr_pf_X_mul" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_X_mul`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_X_mul_named)
  "rr_pf_sequence_X_mul" " using " "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (p * q)` from `left_pf : IsPFPolynomial p` and
`right_pf : IsPFPolynomial q`. -/
syntax (name := rr_pf_mul_named)
  "rr_pf_mul" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_mul`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_mul_named)
  "rr_pf_sequence_mul" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (p ^ m)` from `pf : IsPFPolynomial p` and the `exponent : m`. -/
syntax (name := rr_pf_pow_named)
  "rr_pf_pow" " using "
    "pf" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Sequence form of `rr_pf_pow`: closes `∀ i, IsPFPolynomial (P i ^ m i)` from
`pf : ∀ i, IsPFPolynomial (P i)` and the `exponent : m`, a function `ℕ → ℕ`. -/
syntax (name := rr_pf_sequence_pow_named)
  "rr_pf_sequence_pow" " using "
    "pf" ":=" term ","
    "exponent" ":=" term :
  tactic

/-- Closes `IsPFPolynomial p.derivative` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_derivative_named)
  "rr_pf_derivative" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_derivative`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_derivative_named)
  "rr_pf_sequence_derivative" " using " "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial p.reverse` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_reverse_named)
  "rr_pf_reverse" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_reverse`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_reverse_named)
  "rr_pf_sequence_reverse" " using " "pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (reciprocalShift D p)` from `pf : IsPFPolynomial p` and
`degree : p.natDegree ≤ D`. -/
syntax (name := rr_pf_reciprocal_shift_named)
  "rr_pf_reciprocal_shift" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Sequence form of `rr_pf_reciprocal_shift`: closes
`∀ i, IsPFPolynomial (reciprocalShift (D i) (P i))` from `pf : ∀ i, IsPFPolynomial (P i)` and
`degree : ∀ i, (P i).natDegree ≤ D i`. -/
syntax (name := rr_pf_sequence_reciprocal_shift_named)
  "rr_pf_sequence_reciprocal_shift" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Closes `IsPFPolynomial ((X + 1) * p)` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_mul_X_add_one_named)
  "rr_pf_mul_X_add_one" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_mul_X_add_one`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_mul_X_add_one_named)
  "rr_pf_sequence_mul_X_add_one" " using " "pf" ":=" term :
  tactic

/-- Closes `Interl p p` from `pf : IsPFPolynomial p`. -/
syntax (name := rr_pf_interl_self_named)
  "rr_pf_interl_self" " using " "pf" ":=" term :
  tactic

/-- Sequence form of `rr_pf_interl_self`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pf_sequence_interl_self_named)
  "rr_pf_sequence_interl_self" " using " "pf" ":=" term :
  tactic

/-- Closes `Interl (X * p) (X * q)` from `interl : Interl p q`.
The former `left_pf`, `right_pf`, `interl` syntax remains accepted for compatibility. -/
syntax (name := rr_pf_interl_X_mul_both_named)
  "rr_pf_interl_X_mul_both" " using " "interl" ":=" term :
  tactic

@[tactic_alt rr_pf_interl_X_mul_both_named]
syntax (name := rrPfInterlXMulBothCompat)
  "rr_pf_interl_X_mul_both" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "interl" ":=" term :
  tactic

/-- Sequence form of `rr_pf_interl_X_mul_both`: the same interlacing certificate
for every index `i : Nat`. The former PF-certificate fields remain accepted. -/
syntax (name := rr_pf_sequence_interl_X_mul_both_named)
  "rr_pf_sequence_interl_X_mul_both" " using " "interl" ":=" term :
  tactic

@[tactic_alt rr_pf_sequence_interl_X_mul_both_named]
syntax (name := rrPfSequenceInterlXMulBothCompat)
  "rr_pf_sequence_interl_X_mul_both" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "interl" ":=" term :
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
          | exact RealRooted.Tactic.pf_splits $hp
          | exact RealRooted.IsPFPolynomial.to_sequence $hp)
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
  | `(tactic| rr_pf_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_splits $hp)
  | `(tactic| rr_pf_sequence_has_nonneg using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_has_nonneg $hp)
  | `(tactic| rr_pf_sequence_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_splits $hp)
  | `(tactic| rr_pf_zero_or_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.eq_zero_or_splits $hp)
  | `(tactic| rr_pf_sequence_zero_or_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_zero_or_splits $hp)
  | `(tactic|
      rr_pf_sequence_realrooted using
        pf := $hp:term,
        nonzero := $hp0:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_realrooted $hp $hp0)
  | `(tactic| rr_pf_to_coefficient_sequence using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.to_sequence $hp)
  | `(tactic| rr_pf_sequence_to_coefficient_sequence using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_to_coefficient_sequence $hp)
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
  | `(tactic| rr_pf_interl_self using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.interl_self $hp)
  | `(tactic| rr_pf_sequence_interl_self using pf := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.pf_sequence_interl_self $hp)
  | `(tactic| rr_pf_interl_X_mul_both using interl := $hpq:term) =>
      `(tactic| exact RealRooted.Interl.mul_X_both $hpq)
  | `(tactic|
      rr_pf_interl_X_mul_both using
        left_pf := $_hp:term,
        right_pf := $_hq:term,
        interl := $hpq:term) =>
      `(tactic| exact RealRooted.Interl.mul_X_both $hpq)
  | `(tactic| rr_pf_sequence_interl_X_mul_both using interl := $hpq:term) =>
      `(tactic| exact RealRooted.Tactic.interl_sequence_mul_X_both $hpq)
  | `(tactic|
      rr_pf_sequence_interl_X_mul_both using
        left_pf := $_hp:term,
        right_pf := $_hq:term,
        interl := $hpq:term) =>
      `(tactic| exact RealRooted.Tactic.interl_sequence_mul_X_both $hpq)

end Tactic
end RealRooted
namespace RealRooted

end RealRooted

namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
