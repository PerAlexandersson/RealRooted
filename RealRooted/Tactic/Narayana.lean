import RealRooted.NarayanaTransformation
import RealRooted.Tactic.PFPolynomial

/-!
# Narayana polynomial tactic frontends

Thin wrappers around the generalized Narayana polynomial PF and consecutive
proper-position theorems.
-/

namespace RealRooted
namespace Tactic

theorem narayanaPolynomial_sequence_pf (m d : Nat → ℕ) :
    ∀ n : Nat, IsPFPolynomial (narayanaPolynomial (m n) (d n)) := fun n =>
  RealRooted.narayanaPolynomialRootLocation (m n) (d n)

theorem narayanaPolynomial_sequence_nonneg_coeffs (m d : Nat → ℕ) :
    ∀ n : Nat, HasNonnegCoeffs (narayanaPolynomial (m n) (d n)) :=
  pf_sequence_has_nonneg (narayanaPolynomial_sequence_pf m d)

theorem narayanaPolynomial_sequence_splits (m d : Nat → ℕ) :
    ∀ n : Nat, (narayanaPolynomial (m n) (d n)).Splits :=
  pf_sequence_splits (narayanaPolynomial_sequence_pf m d)

theorem narayanaPolynomial_sequence_nonpos_roots (m d : Nat → ℕ) :
    ∀ n : Nat, HasOnlyNonposRoots (narayanaPolynomial (m n) (d n)) := fun n =>
  RealRooted.IsPFPolynomial.hasOnlyNonposRoots
    (narayanaPolynomial_sequence_pf m d n)

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

syntax (name := rr_narayana_polynomial_prec_succ_named)
  "rr_narayana_polynomial_prec_succ" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_sequence_pf_named)
  "rr_narayana_polynomial_sequence_pf" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_sequence_nonneg_coeffs_named)
  "rr_narayana_polynomial_sequence_nonneg_coeffs" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_sequence_splits_named)
  "rr_narayana_polynomial_sequence_splits" " using "
    "parameter" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_narayana_polynomial_sequence_nonpos_roots_named)
  "rr_narayana_polynomial_sequence_nonpos_roots" " using "
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
  | `(tactic|
      rr_narayana_polynomial_prec_succ using
        parameter := $m:term,
        degree := $n:term) =>
      `(tactic| exact RealRooted.prec_narayanaPolynomial_succ $m $n)
  | `(tactic|
      rr_narayana_polynomial_sequence_pf using
        parameter := $m:term,
        degree := $d:term) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_pf $m $d)
  | `(tactic|
      rr_narayana_polynomial_sequence_nonneg_coeffs using
        parameter := $m:term,
        degree := $d:term) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_nonneg_coeffs $m $d)
  | `(tactic|
      rr_narayana_polynomial_sequence_splits using
        parameter := $m:term,
        degree := $d:term) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_splits $m $d)
  | `(tactic|
      rr_narayana_polynomial_sequence_nonpos_roots using
        parameter := $m:term,
        degree := $d:term) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_nonpos_roots $m $d)

end Tactic
end RealRooted
