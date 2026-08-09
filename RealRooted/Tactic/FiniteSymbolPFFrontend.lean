import RealRooted.Tactic.FiniteSymbolPF

/-!
# Finite-symbol PF-bidiagonal tactic frontends

The residual-stability tactics are checked algebraic helpers. Tactics that
produce PF preservers are explicitly marked `legacy`: they require the false
homogeneous finite-symbol premise retired in issue #314. New proofs should use
`RealRooted.Tactic.PFBidiagonal`, whose unmatched backend remains explicit.
-/

open Polynomial

namespace RealRooted
namespace Tactic

open FiniteSymbolPF

syntax (name := rr_fsp_legacy_finite_symbol_backend_named)
  "rr_fsp_legacy_finite_symbol_backend" " using "
    "bb_backend" ":=" term ","
    "stable" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_stable_of_residual_factor_named)
  "rr_fsp_stable_of_residual_factor" " using "
    "factor" ":=" term ","
    "residual_stable" ":=" term :
  tactic

syntax (name := rr_fsp_stable_of_residual_certificate_named)
  "rr_fsp_stable_of_residual_certificate" " using "
    "certificate" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_preserver_of_residual_certificate_named)
  "rr_fsp_legacy_preserver_of_residual_certificate" " using "
    "bb_backend" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_quadratic_preserver_named)
  "rr_fsp_legacy_quadratic_preserver" " using "
    "bb_backend" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_quadratic_preserver_on_degree_named)
  "rr_fsp_legacy_quadratic_preserver_on_degree" " using "
    "bb_backend" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_second_derivative_preserver_named)
  "rr_fsp_legacy_second_derivative_preserver" " using "
    "bb_backend" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_second_derivative_preserver_on_degree_named)
  "rr_fsp_legacy_second_derivative_preserver_on_degree" " using "
    "bb_backend" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_shifted_second_derivative_preserver_named)
  "rr_fsp_legacy_shifted_second_derivative_preserver" " using "
    "bb_backend" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_legacy_second_derivative_sequence_named)
  "rr_fsp_legacy_second_derivative_sequence" " using "
    "bb_backend" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

syntax (name := rr_fsp_legacy_shifted_second_derivative_sequence_named)
  "rr_fsp_legacy_shifted_second_derivative_sequence" " using "
    "bb_backend" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_fsp_legacy_finite_symbol_backend using
        bb_backend := $hBB:term,
        stable := $hstab:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact FiniteSymbolPF.legacy_finite_symbol_pf_bidiagonal_backend
          $hBB $hstab $halpha $hbeta)
  | `(tactic|
      rr_fsp_stable_of_residual_factor using
        factor := $hfac:term,
        residual_stable := $hres:term) =>
      `(tactic|
        exact FiniteSymbolPF.finiteSymbol_stable_of_residual_factor $hfac $hres)
  | `(tactic|
      rr_fsp_stable_of_residual_certificate using
        certificate := $hcert:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.finiteSymbol_stable_of_residual_certificate $hcert)
  | `(tactic|
      rr_fsp_legacy_preserver_of_residual_certificate using
        bb_backend := $hBB:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.legacy_bidiagonalPFPreserver_of_finiteSymbol_residual_certificate
            $hBB $hcert)
  | `(tactic|
      rr_fsp_legacy_quadratic_preserver using
        bb_backend := $hBB:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.legacy_quadraticBidiagonalPFPreserver_of_residual_certificate
            $hBB _ _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_legacy_quadratic_preserver_on_degree using
        bb_backend := $hBB:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.legacy_quadraticBidiagonalPFPreserver_of_residual_certificate_on_degree
            $hBB _ _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_legacy_second_derivative_preserver using
        bb_backend := $hBB:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.legacy_secondDerivativeBidiagonalPFPreserver_of_residual_certificate
            $hBB _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_legacy_second_derivative_preserver_on_degree using
        bb_backend := $hBB:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          legacy_secondDerivativeBidiagonalPFPreserver_of_residual_certificate_on_degree
            $hBB _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_legacy_shifted_second_derivative_preserver using
        bb_backend := $hBB:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.legacy_shiftedSecondDerivativeBidiagonalPFPreserver_of_residual_certificate
            $hBB _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_legacy_second_derivative_sequence using
        bb_backend := $hBB:term,
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.legacy_isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence
            $hBB $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_fsp_legacy_second_derivative_sequence using
        bb_backend := $hBB:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.legacy_isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from
            $hBB $N $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_fsp_legacy_shifted_second_derivative_sequence using
        bb_backend := $hBB:term,
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.legacy_isPFPolynomial_of_shiftedSecondDerivativeBidiagonalForm_sequence
            $hBB $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_fsp_legacy_shifted_second_derivative_sequence using
        bb_backend := $hBB:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (legacy_isPFPolynomial_of_shiftedSecondDerivativeBidiagonalForm_sequence_from
            $hBB $N $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)

end Tactic
end RealRooted
