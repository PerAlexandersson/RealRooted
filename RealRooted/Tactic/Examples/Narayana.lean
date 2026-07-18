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

end Tactic
end RealRooted
