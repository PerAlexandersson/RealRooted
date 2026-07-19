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

end Tactic
end RealRooted
