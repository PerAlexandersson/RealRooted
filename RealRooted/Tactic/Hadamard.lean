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
  exact Or.resolve_left
    (schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
      hf hfdeg hpdeg hsplits)
    hout

theorem schurSzegoComp_splits_of_level_le_two {n : ℕ} {f p : ℝ[X]}
    (hn : n ≤ 2)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  exact Or.resolve_left
    (finiteSchurSzegoComposition_of_natDegree_le_two
      hn hf hfdeg hpdeg hsplits)
    hout

theorem schurSzegoComp_splits_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  exact Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hf hfdeg hpdeg hsplits)
    hout

theorem schurSzegoComp_splits_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  exact Or.resolve_left
    (finiteSchurSzegoComposition_of_factors_natDegree_le_two
      hf hfdeg hpdeg hsplits)
    hout

theorem schurSzegoComp_splits_of_pf_factor_natDegree_le_three_cubicDiscr
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p))
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  exact Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
      hf hfdeg hpdeg hsplits hdisc)
    hout

theorem schurSzegoComp_splits_of_pf_factor_natDegree_le_three_cubicNum
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  exact Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
      hn hf hfdeg hpdeg hsplits hnum)
    hout

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

syntax (name := rr_schur_szego_level_le_two_named)
  "rr_schur_szego_level_le_two" " using "
    "level_le_two" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_schur_szego_level_le_two_splits_named)
  "rr_schur_szego_level_le_two_splits" " using "
    "level_le_two" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_two_named)
  "rr_schur_szego_pf_factor_degree_le_two" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_two" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_two_splits_named)
  "rr_schur_szego_pf_factor_degree_le_two_splits" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_two" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_factors_degree_le_two_named)
  "rr_schur_szego_factors_degree_le_two" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_two" ":=" term ","
    "input_degree_le_two" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_schur_szego_factors_degree_le_two_splits_named)
  "rr_schur_szego_factors_degree_le_two_splits" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_two" ":=" term ","
    "input_degree_le_two" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_cubic_named)
  "rr_schur_szego_pf_factor_degree_le_three_cubic" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "cubic_discriminant" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_cubic_splits_named)
  "rr_schur_szego_pf_factor_degree_le_three_cubic_splits" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "cubic_discriminant" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_num_named)
  "rr_schur_szego_pf_factor_degree_le_three_num" " using "
    "level_ge_three" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "cubic_numerator" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_num_splits_named)
  "rr_schur_szego_pf_factor_degree_le_three_num_splits" " using "
    "level_ge_three" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "cubic_numerator" ":=" term ","
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
      rr_schur_szego_level_le_two using
        level_le_two := $hn:term,
        pf_factor := $hf:term,
        pf_degree := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact RealRooted.finiteSchurSzegoComposition_of_natDegree_le_two
          $hn $hf $hfdeg $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_level_le_two_splits using
        level_le_two := $hn:term,
        pf_factor := $hf:term,
        pf_degree := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact RealRooted.Tactic.schurSzegoComp_splits_of_level_le_two
          $hn $hf $hfdeg $hpdeg $hsplits $hout)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_two using
        pf_factor := $hf:term,
        pf_degree_le_two := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact
          RealRooted.finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
            $hf $hfdeg $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_two_splits using
        pf_factor := $hf:term,
        pf_degree_le_two := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.schurSzegoComp_splits_of_pf_factor_natDegree_le_two
            $hf $hfdeg $hpdeg $hsplits $hout)
  | `(tactic|
      rr_schur_szego_factors_degree_le_two using
        pf_factor := $hf:term,
        pf_degree_le_two := $hfdeg:term,
        input_degree_le_two := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact RealRooted.finiteSchurSzegoComposition_of_factors_natDegree_le_two
          $hf $hfdeg $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_factors_degree_le_two_splits using
        pf_factor := $hf:term,
        pf_degree_le_two := $hfdeg:term,
        input_degree_le_two := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact RealRooted.Tactic.schurSzegoComp_splits_of_factors_natDegree_le_two
          $hf $hfdeg $hpdeg $hsplits $hout)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_cubic using
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        cubic_discriminant := $hdisc:term) =>
      `(tactic|
        exact
          RealRooted.finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
            $hf $hfdeg $hpdeg $hsplits $hdisc)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_cubic_splits using
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        cubic_discriminant := $hdisc:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.schurSzegoComp_splits_of_pf_factor_natDegree_le_three_cubicDiscr
            $hf $hfdeg $hpdeg $hsplits $hdisc $hout)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_num using
        level_ge_three := $hn:term,
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        cubic_numerator := $hnum:term) =>
      `(tactic|
        exact
          finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
            $hn $hf $hfdeg $hpdeg $hsplits $hnum)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_num_splits using
        level_ge_three := $hn:term,
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        cubic_numerator := $hnum:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.schurSzegoComp_splits_of_pf_factor_natDegree_le_three_cubicNum
            $hn $hf $hfdeg $hpdeg $hsplits $hnum $hout)
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
