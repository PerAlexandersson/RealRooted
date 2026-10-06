import RealRooted.Tactic.Narayana

namespace RealRooted
namespace Tactic

example {m n : ℕ} :
    IsPFPolynomial (narayanaPolynomial m n) := by
  rr_narayana_polynomial_pf using
    parameter := m,
    degree := n

example {m n : ℕ} :
    HasNonnegCoeffs (narayanaPolynomial m n) := by
  rr_narayana_polynomial_nonneg_coeffs using
    parameter := m,
    degree := n

example {m n : ℕ} :
    (narayanaPolynomial m n).Splits := by
  rr_narayana_polynomial_splits using
    parameter := m,
    degree := n

example {m n : ℕ} :
    HasOnlyNonposRoots (narayanaPolynomial m n) := by
  rr_narayana_polynomial_nonpos_roots using
    parameter := m,
    degree := n

example {m n : ℕ} :
    StrictInterl (narayanaPolynomial m (n + 1)) (narayanaPolynomial m (n + 2)) := by
  rr_narayana_polynomial_strict_interl_succ using
    parameter := m,
    degree := n

example {m d : Nat → ℕ} :
    ∀ n : Nat, IsPFPolynomial (narayanaPolynomial (m n) (d n)) := by
  rr_narayana_polynomial_sequence_pf using
    parameter := m,
    degree := d

example {m d : Nat → ℕ} :
    ∀ n : Nat, HasNonnegCoeffs (narayanaPolynomial (m n) (d n)) := by
  rr_narayana_polynomial_sequence_nonneg_coeffs using
    parameter := m,
    degree := d

example {m d : Nat → ℕ} :
    ∀ n : Nat, (narayanaPolynomial (m n) (d n)).Splits := by
  rr_narayana_polynomial_sequence_splits using
    parameter := m,
    degree := d

example {m d : Nat → ℕ} :
    ∀ n : Nat, HasOnlyNonposRoots (narayanaPolynomial (m n) (d n)) := by
  rr_narayana_polynomial_sequence_nonpos_roots using
    parameter := m,
    degree := d

/-! Field-free forms: the parameter and degree are read off the goal. -/

example {m n : ℕ} : IsPFPolynomial (narayanaPolynomial m n) := by
  rr_narayana_polynomial_pf

example : HasNonnegCoeffs (narayanaPolynomial 2 3) := by
  rr_narayana_polynomial_nonneg_coeffs

example {m n : ℕ} : (narayanaPolynomial m n).Splits := by
  rr_narayana_polynomial_splits

example {m n : ℕ} : HasOnlyNonposRoots (narayanaPolynomial m n) := by
  rr_narayana_polynomial_nonpos_roots

example {m n : ℕ} :
    StrictInterl (narayanaPolynomial m (n + 1)) (narayanaPolynomial m (n + 2)) := by
  rr_narayana_polynomial_strict_interl_succ

example {m d : Nat → ℕ} :
    ∀ n : Nat, IsPFPolynomial (narayanaPolynomial (m n) (d n)) := by
  rr_narayana_polynomial_sequence_pf

example : ∀ n : Nat, HasNonnegCoeffs (narayanaPolynomial 2 (n + 1)) := by
  rr_narayana_polynomial_sequence_nonneg_coeffs

example {m d : Nat → ℕ} :
    ∀ n : Nat, (narayanaPolynomial (m n) (d n)).Splits := by
  rr_narayana_polynomial_sequence_splits

example {m d : Nat → ℕ} :
    ∀ n : Nat, HasOnlyNonposRoots (narayanaPolynomial (m n) (d n)) := by
  rr_narayana_polynomial_sequence_nonpos_roots

end Tactic
end RealRooted
