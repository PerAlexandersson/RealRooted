module

public import RealRooted.PFPolynomial
import RealRooted.WagnerX.ListInterlacing

/-!
# PF-polynomial tactic frontends and model transport

The model transport theorem preserves PF rows and consecutive `Interl` through
pointwise sequence identification. The remaining declarations expose the
standard consequences of an `IsPFPolynomial` hypothesis directly as theorems.
-/

public section

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

/-- Every PF polynomial splits, including the zero polynomial. -/
theorem pf_splits
    {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    p.Splits := by
  rcases RealRooted.IsPFPolynomial.eq_zero_or_splits hp with rfl | hsplits
  · simp
  · exact hsplits

/-- A pointwise PF family has nonnegative coefficients at every index. -/
theorem pf_sequence_has_nonneg
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (P i) := fun i =>
  RealRooted.IsPFPolynomial.hasNonnegCoeffs (hP i)

/-- Every member of a pointwise PF family splits. -/
theorem pf_sequence_splits
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, (P i).Splits := fun i =>
  pf_splits (hP i)

/-- Every member of a pointwise PF family is zero or splits. -/
theorem pf_sequence_zero_or_splits
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, P i = 0 ∨ (P i).Splits := fun i =>
  RealRooted.IsPFPolynomial.eq_zero_or_splits (hP i)

/-- A pointwise nonzero PF family consists of nonzero split polynomials. -/
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

/-- Pointwise nonnegative coefficients and splitting make a family PF. -/
theorem pf_sequence_of_nonneg_splits
    {P : Nat → ℝ[X]}
    (hPnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hPsplits : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, IsPFPolynomial (P i) := fun i =>
  RealRooted.IsPFPolynomial.of_realRooted_nonneg (hPnn i) (hPsplits i)

/-- Pointwise nonnegative coefficients and zero-or-splitting make a family PF. -/
theorem pf_sequence_of_nonneg_zero_or_splits
    {P : Nat → ℝ[X]}
    (hPnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hPrr : ∀ i : Nat, P i = 0 ∨ (P i).Splits) :
    ∀ i : Nat, IsPFPolynomial (P i) := fun i =>
  RealRooted.IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hPnn i) (hPrr i)

/-- Nonnegative constants form a pointwise PF family. -/
theorem pf_sequence_C_nonneg
    {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 ≤ a i) :
    ∀ i : Nat, IsPFPolynomial (C (a i) : ℝ[X]) := fun i =>
  RealRooted.IsPFPolynomial.of_C_nonneg (ha i)

/-- Multiplying a pointwise PF family by positive scalars preserves the PF property. -/
theorem pf_sequence_const_mul
    {a : Nat → ℝ} {P : Nat → ℝ[X]}
    (ha : ∀ i : Nat, 0 < a i)
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (C (a i) * P i) := fun i =>
  RealRooted.IsPFPolynomial.const_mul (ha i) (hP i)

/-- The polynomials `X + C (a i)` form a PF family when every `a i` is nonnegative. -/
theorem pf_sequence_X_add_C
    {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 ≤ a i) :
    ∀ i : Nat, IsPFPolynomial (X + C (a i) : ℝ[X]) := fun i =>
  RealRooted.isPFPolynomial_X_add_C (ha i)

/-- Arbitrary pointwise powers of `X` form a PF family. -/
theorem pf_sequence_X_pow
    {m : Nat → Nat} :
    ∀ i : Nat, IsPFPolynomial ((X : ℝ[X]) ^ m i) := fun i =>
  RealRooted.isPFPolynomial_X_pow (m i)

/-- Multiplication by `X` preserves a pointwise PF family. -/
theorem pf_sequence_X_mul
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (X * P i) := fun i =>
  RealRooted.IsPFPolynomial.X_mul (hP i)

/-- Pointwise products of two PF families are PF. -/
theorem pf_sequence_mul
    {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i)) :
    ∀ i : Nat, IsPFPolynomial (P i * Q i) := fun i =>
  RealRooted.IsPFPolynomial.mul (hP i) (hQ i)

/-- Pointwise natural powers of a PF family are PF. -/
theorem pf_sequence_pow
    {P : Nat → ℝ[X]} {m : Nat → Nat}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial ((P i) ^ m i) := fun i =>
  RealRooted.IsPFPolynomial.pow (hP i) (m i)

/-- Pointwise differentiation preserves a PF family. -/
theorem pf_sequence_derivative
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (P i).derivative := fun i =>
  RealRooted.IsPFPolynomial.derivative (hP i)

/-- Pointwise reversal preserves a PF family. -/
theorem pf_sequence_reverse
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (P i).reverse := fun i =>
  RealRooted.IsPFPolynomial.reverse (hP i)

/-- Pointwise reciprocal shifts preserve a PF family when the shifts bound the degrees. -/
theorem pf_sequence_reciprocal_shift
    {D : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ D i) :
    ∀ i : Nat, IsPFPolynomial (reciprocalShift (D i) (P i)) := fun i =>
  RealRooted.reciprocalShift_preserves_pf (hP i) (hdeg i)

/-- Pointwise multiplication by `X + 1` preserves a PF family. -/
theorem pf_sequence_mul_X_add_one
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial ((X + 1) * P i) := fun i =>
  RealRooted.isPFPolynomial_mul_X_add_one (hP i)

/-- Every member of a pointwise PF family is in zero-aware proper position with itself. -/
theorem pf_sequence_interl_self
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, Interl (P i) (P i) := fun i =>
  RealRooted.IsPFPolynomial.interl_self (hP i)

/-- Multiplying both members of a pointwise `Interl` relation by `X` preserves it. -/
theorem interl_sequence_mul_X_both
    {P Q : Nat → ℝ[X]} (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ i : Nat, Interl (X * P i) (X * Q i) := fun i =>
  (hPQ i).mul_X_both

end Tactic
end RealRooted

