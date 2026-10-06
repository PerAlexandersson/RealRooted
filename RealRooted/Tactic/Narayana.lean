import RealRooted.NarayanaTransformation
import RealRooted.Tactic.PFPolynomial

/-!
# Narayana polynomial tactic frontends

Thin wrappers around the generalized Narayana polynomial PF and consecutive
proper-position theorems.  Each tactic also has a field-free form that infers
the parameter and degree from the goal.
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

syntax (name := rr_narayana_polynomial_strict_interl_succ_named)
  "rr_narayana_polynomial_strict_interl_succ" " using "
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

syntax (name := rr_narayana_polynomial_pf_inferred)
  "rr_narayana_polynomial_pf" : tactic

syntax (name := rr_narayana_polynomial_nonneg_coeffs_inferred)
  "rr_narayana_polynomial_nonneg_coeffs" : tactic

syntax (name := rr_narayana_polynomial_splits_inferred)
  "rr_narayana_polynomial_splits" : tactic

syntax (name := rr_narayana_polynomial_nonpos_roots_inferred)
  "rr_narayana_polynomial_nonpos_roots" : tactic

syntax (name := rr_narayana_polynomial_strict_interl_succ_inferred)
  "rr_narayana_polynomial_strict_interl_succ" : tactic

syntax (name := rr_narayana_polynomial_sequence_pf_inferred)
  "rr_narayana_polynomial_sequence_pf" : tactic

syntax (name := rr_narayana_polynomial_sequence_nonneg_coeffs_inferred)
  "rr_narayana_polynomial_sequence_nonneg_coeffs" : tactic

syntax (name := rr_narayana_polynomial_sequence_splits_inferred)
  "rr_narayana_polynomial_sequence_splits" : tactic

syntax (name := rr_narayana_polynomial_sequence_nonpos_roots_inferred)
  "rr_narayana_polynomial_sequence_nonpos_roots" : tactic

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
      rr_narayana_polynomial_strict_interl_succ using
        parameter := $m:term,
        degree := $n:term) =>
      `(tactic| exact RealRooted.strictInterl_narayanaPolynomial_succ $m $n)
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
  | `(tactic| rr_narayana_polynomial_pf) =>
      `(tactic| exact RealRooted.narayanaPolynomialRootLocation _ _)
  | `(tactic| rr_narayana_polynomial_nonneg_coeffs) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_narayanaPolynomial _ _)
  | `(tactic| rr_narayana_polynomial_splits) =>
      `(tactic| exact RealRooted.splits_narayanaPolynomial _ _)
  | `(tactic| rr_narayana_polynomial_nonpos_roots) =>
      `(tactic|
        exact
          RealRooted.IsPFPolynomial.hasOnlyNonposRoots
            (RealRooted.narayanaPolynomialRootLocation _ _))
  | `(tactic| rr_narayana_polynomial_strict_interl_succ) =>
      `(tactic| exact RealRooted.strictInterl_narayanaPolynomial_succ _ _)
  | `(tactic| rr_narayana_polynomial_sequence_pf) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_pf _ _)
  | `(tactic| rr_narayana_polynomial_sequence_nonneg_coeffs) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_nonneg_coeffs _ _)
  | `(tactic| rr_narayana_polynomial_sequence_splits) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_splits _ _)
  | `(tactic| rr_narayana_polynomial_sequence_nonpos_roots) =>
      `(tactic| exact RealRooted.Tactic.narayanaPolynomial_sequence_nonpos_roots _ _)

end Tactic
end RealRooted
