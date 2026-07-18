import RealRooted.NarayanaTransformation

/-!
# Narayana polynomial tactic frontends

Thin wrappers around the generalized Narayana polynomial PF theorem.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_narayana_polynomial_pf_named)
  "rr_narayana_polynomial_pf" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_nonneg_coeffs_named)
  "rr_narayana_polynomial_nonneg_coeffs" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_splits_named)
  "rr_narayana_polynomial_splits" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_nonpos_roots_named)
  "rr_narayana_polynomial_nonpos_roots" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_narayana_polynomial_pf using
        parameter := $m:term,
        degree := $n:term) =>
      `(tactic| exact RealRooted.narayanaPolynomialRootLocation $m $n)
  | `(tactic|
      rr_narayana_polynomial_nonneg_coeffs using
        parameter := $m:term,
        degree := $n:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_narayanaPolynomial $m $n)
  | `(tactic|
      rr_narayana_polynomial_splits using
        parameter := $m:term,
        degree := $n:term) =>
      `(tactic| exact RealRooted.splits_narayanaPolynomial $m $n)
  | `(tactic|
      rr_narayana_polynomial_nonpos_roots using
        parameter := $m:term,
        degree := $n:term) =>
      `(tactic|
        exact
          RealRooted.IsPFPolynomial.hasOnlyNonposRoots
            (RealRooted.narayanaPolynomialRootLocation $m $n))

end Tactic
end RealRooted
