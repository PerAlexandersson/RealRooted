import RealRooted.Hadamard

/-!
# Hadamard and Schur--Szego tactic frontends

Thin wrappers around the checked finite Schur--Szego and Hadamard PF backends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem schurSzegoComp_splits_of_nonzero {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rcases schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
      hf hfdeg hpdeg hsplits with hzero | hsplits
  · exact (hout hzero).elim
  · exact hsplits

syntax (name := rr_schur_szego_nonzero_statement_named)
  "rr_schur_szego_nonzero_statement" : tactic

syntax (name := rr_schur_szego_statement_named)
  "rr_schur_szego_statement" : tactic

syntax (name := rr_hadamard_pf_statement_named)
  "rr_hadamard_pf_statement" : tactic

syntax (name := rr_hadamard_nonneg_realrooted_statement_named)
  "rr_hadamard_nonneg_realrooted_statement" : tactic

syntax (name := rr_schur_szego_named)
  "rr_schur_szego" " using "
    "pf_factor" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_schur_szego_splits_named)
  "rr_schur_szego_splits" " using "
    "pf_factor" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_nonzero_named)
  "rr_schur_szego_nonzero" " using "
    "pf_factor" ":=" term ","
    "pf_nonzero" ":=" term ","
    "pf_degree" ":=" term ","
    "input_nonzero" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_hadamard_pf_named)
  "rr_hadamard_pf" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

syntax (name := rr_hadamard_nonneg_realrooted_named)
  "rr_hadamard_nonneg_realrooted" " using "
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "left_realrooted" ":=" term ","
    "right_realrooted" ":=" term :
  tactic

syntax (name := rr_hadamard_nonneg_coeffs_named)
  "rr_hadamard_nonneg_coeffs" " using "
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_schur_szego_nonzero_statement) =>
      `(tactic| exact RealRooted.finiteSchurSzegoCompositionNonzero)
  | `(tactic| rr_schur_szego_statement) =>
      `(tactic| exact RealRooted.finiteSchurSzegoComposition)
  | `(tactic| rr_hadamard_pf_statement) =>
      `(tactic| exact RealRooted.schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec)
  | `(tactic| rr_hadamard_nonneg_realrooted_statement) =>
      `(tactic| exact RealRooted.garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec)
  | `(tactic|
      rr_schur_szego using
        pf_factor := $hf:term,
        pf_degree := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact RealRooted.schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
          $hf $hfdeg $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_splits using
        pf_factor := $hf:term,
        pf_degree := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact RealRooted.Tactic.schurSzegoComp_splits_of_nonzero
          $hf $hfdeg $hpdeg $hsplits $hout)
  | `(tactic|
      rr_schur_szego_nonzero using
        pf_factor := $hf:term,
        pf_nonzero := $hf0:term,
        pf_degree := $hfdeg:term,
        input_nonzero := $hp0:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact RealRooted.finiteSchurSzegoCompositionNonzero
          $hf $hf0 $hfdeg $hp0 $hpdeg $hsplits)
  | `(tactic|
      rr_hadamard_pf using
        left_pf := $hp:term,
        right_pf := $hq:term) =>
      `(tactic|
        exact RealRooted.hadamardProduct_preserves_pf_of_nonnegPrec $hp $hq)
  | `(tactic|
      rr_hadamard_nonneg_realrooted using
        left_nonneg := $hpnn:term,
        right_nonneg := $hqnn:term,
        left_realrooted := $hp:term,
        right_realrooted := $hq:term) =>
      `(tactic|
        exact RealRooted.garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec
          $hpnn $hqnn $hp $hq)
  | `(tactic|
      rr_hadamard_nonneg_coeffs using
        left_nonneg := $hpnn:term,
        right_nonneg := $hqnn:term) =>
      `(tactic|
        exact RealRooted.HasNonnegCoeffs.hadamardProduct $hpnn $hqnn)

end Tactic
end RealRooted
