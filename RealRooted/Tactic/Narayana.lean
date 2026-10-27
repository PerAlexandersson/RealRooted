module

public import RealRooted.NarayanaTransformation
public import RealRooted.Tactic.PFPolynomial

/-!
# Narayana polynomial tactic frontends

Thin wrappers around the generalized Narayana polynomial PF and consecutive
proper-position theorems.  Each tactic also has a field-free form that infers
the parameter and degree from the goal.
-/

public section

namespace RealRooted
namespace Tactic

/-- Every polynomial in the sequence `narayanaPolynomial (m n) (d n)` is a PF polynomial. -/
theorem narayanaPolynomial_sequence_pf (m d : Nat → ℕ) :
    ∀ n : Nat, IsPFPolynomial (narayanaPolynomial (m n) (d n)) := fun n =>
  RealRooted.narayanaPolynomialRootLocation (m n) (d n)

/-- Every polynomial in the sequence `narayanaPolynomial (m n) (d n)` has nonnegative
coefficients. -/
theorem narayanaPolynomial_sequence_nonneg_coeffs (m d : Nat → ℕ) :
    ∀ n : Nat, HasNonnegCoeffs (narayanaPolynomial (m n) (d n)) :=
  pf_sequence_has_nonneg (narayanaPolynomial_sequence_pf m d)

/-- Every polynomial in the sequence `narayanaPolynomial (m n) (d n)` splits over `ℝ`. -/
theorem narayanaPolynomial_sequence_splits (m d : Nat → ℕ) :
    ∀ n : Nat, (narayanaPolynomial (m n) (d n)).Splits :=
  pf_sequence_splits (narayanaPolynomial_sequence_pf m d)

/-- Every polynomial in the sequence `narayanaPolynomial (m n) (d n)` has only nonpositive
roots. -/
theorem narayanaPolynomial_sequence_nonpos_roots (m d : Nat → ℕ) :
    ∀ n : Nat, HasOnlyNonposRoots (narayanaPolynomial (m n) (d n)) := fun n =>
  RealRooted.IsPFPolynomial.hasOnlyNonposRoots
    (narayanaPolynomial_sequence_pf m d n)

end Tactic
end RealRooted
