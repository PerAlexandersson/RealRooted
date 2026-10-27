module

public import RealRooted.Derivative
public import RealRooted.Tactic.Finish
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Derivative tactic frontends

Thin wrappers for derivative interlacing and routine derivative side goals.
-/

public section

open Lean.Elab.Tactic
open Polynomial

namespace RealRooted
namespace Tactic

/-- A sequence of splitting polynomials of nonzero degree is pointwise interlaced by its
derivative. -/
theorem derivative_sequence_interlaces
    {P : Nat → ℝ[X]}
    (hsplits : ∀ i : Nat, (P i).Splits)
    (hdeg : ∀ i : Nat, (P i).natDegree ≠ 0) :
    ∀ i : Nat, Interlaces (P i).derivative (P i) := fun i =>
  RealRooted.derivative_interlaces_of_natDegree_ne_zero (hsplits i) (hdeg i)

/-- The derivative strictly interlaces a splitting polynomial of nonzero degree. -/
theorem derivative_strictInterl {p : ℝ[X]}
    (hsplits : p.Splits) (hdeg : p.natDegree ≠ 0) :
    StrictInterl p.derivative p :=
  (RealRooted.derivative_interlaces_of_natDegree_ne_zero hsplits hdeg).toStrictInterl

/-- A sequence of splitting polynomials of nonzero degree is pointwise strictly interlaced by
its derivative. -/
theorem derivative_sequence_strictInterl
    {P : Nat → ℝ[X]}
    (hsplits : ∀ i : Nat, (P i).Splits)
    (hdeg : ∀ i : Nat, (P i).natDegree ≠ 0) :
    ∀ i : Nat, StrictInterl (P i).derivative (P i) := fun i =>
  RealRooted.Tactic.derivative_strictInterl (hsplits i) (hdeg i)

/-- The derivatives of a sequence of polynomials with nonnegative coefficients also have
nonnegative coefficients. -/
theorem nonnegCoeffs_sequence_derivative
    {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (P i).derivative := fun i =>
  RealRooted.HasNonnegCoeffs.derivative (hP i)

/-- The derivatives of a sequence with positive leading coefficients and nonzero degrees have
positive leading coefficients. -/
theorem pos_lc_sequence_derivative
    {P : Nat → ℝ[X]}
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≠ 0) :
    ∀ i : Nat, HasPosLeadingCoeff (P i).derivative := fun i =>
  RealRooted.HasPosLeadingCoeff.derivative (hpos i) (hdeg i)

/-- The derivatives of a sequence of polynomials of nonzero degree are nonzero. -/
theorem derivative_sequence_ne_zero
    {P : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (P i).natDegree ≠ 0) :
    ∀ i : Nat, (P i).derivative ≠ 0 := fun i =>
  Polynomial.derivative_ne_zero.mpr (hdeg i)

end Tactic
end RealRooted
