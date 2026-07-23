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
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial hf hfdeg hpdeg hsplits) hout

theorem schurSzegoComp_splits_of_level_le_two {n : ℕ} {f p : ℝ[X]}
    (hn : n ≤ 2)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
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
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
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
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
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
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
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
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
      hn hf hfdeg hpdeg hsplits hnum)
    hout

theorem schurSzegoComp_splits_of_pf_factor_degree_le_three_diagonalBase
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
      hbase hn hf hfdeg hpdeg hsplits)
    hout

theorem schurSzegoComp_zero_or_splits_of_diagonalBase_leftDegree
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_of_pfCubicDiscrDiagonalNonneg
    hbase hf hfdeg hfn hpdeg hsplits

theorem schurSzegoComp_splits_of_pf_factor_degree_le_three_diagonalBase_leftDegree
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (schurSzegoComp_zero_or_splits_of_diagonalBase_leftDegree
      hbase hf hfdeg hfn hpdeg hsplits)
    hout

theorem schurSzegoComp_splits_of_pf_factor_degree_le_three_num_leftDegree
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
      hf hfdeg hfn hpdeg hsplits hnum)
    hout

theorem schurSzegoComp_sequence_zero_or_splits {N : Nat → ℕ}
    {F P : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ N i)
    (hPdeg : ∀ i : Nat, (P i).natDegree ≤ N i)
    (hPsplits : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      schurSzegoComp (N i) (F i) (P i) = 0 ∨
        (schurSzegoComp (N i) (F i) (P i)).Splits := fun i =>
  schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
    (hF i) (hFdeg i) (hPdeg i) (hPsplits i)

theorem schurSzegoComp_sequence_splits {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ N i)
    (hPdeg : ∀ i : Nat, (P i).natDegree ≤ N i)
    (hPsplits : ∀ i : Nat, (P i).Splits)
    (hout : ∀ i : Nat, schurSzegoComp (N i) (F i) (P i) ≠ 0) :
    ∀ i : Nat, (schurSzegoComp (N i) (F i) (P i)).Splits := fun i =>
  schurSzegoComp_splits_of_nonzero
    (hF i) (hFdeg i) (hPdeg i) (hPsplits i) (hout i)

theorem hadamardProduct_sequence_pf {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i)) :
    ∀ i : Nat, IsPFPolynomial (hadamardProduct (P i) (Q i)) := fun i =>
  hadamardProduct_preserves_pf_of_nonnegPrec (hP i) (hQ i)

theorem hadamardProduct_sequence_nonneg_realrooted {P Q : Nat → ℝ[X]}
    (hPnonneg : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQnonneg : ∀ i : Nat, HasNonnegCoeffs (Q i))
    (hP : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hQ : ∀ i : Nat, Q i ≠ 0 ∧ (Q i).Splits) :
    ∀ i : Nat,
      (hadamardProduct (P i) (Q i) = 0 ∨
          (hadamardProduct (P i) (Q i)).Splits) ∧
        HasNonnegCoeffs (hadamardProduct (P i) (Q i)) ∧
        ∀ r ∈ (hadamardProduct (P i) (Q i)).roots, r ≤ 0 := fun i =>
  garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec
    (hPnonneg i) (hQnonneg i) (hP i) (hQ i)

theorem hadamardProduct_sequence_nonneg_coeffs {P Q : Nat → ℝ[X]}
    (hPnonneg : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQnonneg : ∀ i : Nat, HasNonnegCoeffs (Q i)) :
    ∀ i : Nat, HasNonnegCoeffs (hadamardProduct (P i) (Q i)) := fun i =>
  HasNonnegCoeffs.hadamardProduct (hPnonneg i) (hQnonneg i)

theorem hadamardProduct_prec0_of_nonneg_prec {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f)
    (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p)
    (hq : HasNonnegCoeffs q)
    (hfg : Prec f g)
    (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) :=
  garloffWagnerHadamardNonnegPrec hf hg hp hq hfg hpq

theorem hadamardProduct_sequence_prec0 {F G P Q : Nat → ℝ[X]}
    (hF : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hG : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQ : ∀ i : Nat, HasNonnegCoeffs (Q i))
    (hFG : ∀ i : Nat, Prec (F i) (G i))
    (hPQ : ∀ i : Nat, Prec (P i) (Q i)) :
    ∀ i : Nat,
      Prec0 (hadamardProduct (F i) (P i)) (hadamardProduct (G i) (Q i)) :=
  fun i =>
    hadamardProduct_prec0_of_nonneg_prec
      (hF i) (hG i) (hP i) (hQ i) (hFG i) (hPQ i)

syntax (name := rr_schur_szego_nonzero_statement_named)
  "rr_schur_szego_nonzero_statement" : tactic

syntax (name := rr_schur_szego_statement_named)
  "rr_schur_szego_statement" : tactic

syntax (name := rr_schur_szego_pf_cubic_diagonal_base_named)
  "rr_schur_szego_pf_cubic_diagonal_base" " using "
    "schur_szego" ":=" term :
  tactic

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

syntax (name := rr_schur_szego_pf_factor_degree_le_three_diagonal_base_named)
  "rr_schur_szego_pf_factor_degree_le_three_diagonal_base" " using "
    "diagonal_base" ":=" term ","
    "level_ge_three" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_diagonal_base_splits_named)
  "rr_schur_szego_pf_factor_degree_le_three_diagonal_base_splits" " using "
    "diagonal_base" ":=" term ","
    "level_ge_three" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree_named)
  "rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree" " using "
    "diagonal_base" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax
  (name := rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree_splits_named)
  "rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree_splits"
    " using "
    "diagonal_base" ":=" term ","
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_num_left_degree_named)
  "rr_schur_szego_pf_factor_degree_le_three_num_left_degree" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "cubic_numerator" ":=" term :
  tactic

syntax (name := rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits_named)
  "rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits" " using "
    "pf_factor" ":=" term ","
    "pf_degree_le_three" ":=" term ","
    "pf_degree" ":=" term ","
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

syntax (name := rr_schur_szego_sequence_named)
  "rr_schur_szego_sequence" " using "
    "pf_factor" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term :
  tactic

syntax (name := rr_schur_szego_sequence_splits_named)
  "rr_schur_szego_sequence_splits" " using "
    "pf_factor" ":=" term ","
    "pf_degree" ":=" term ","
    "input_degree" ":=" term ","
    "input_splits" ":=" term ","
    "nonzero" ":=" term :
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

syntax (name := rr_hadamard_prec0_named)
  "rr_hadamard_prec0" " using "
    "first_left_nonneg" ":=" term ","
    "first_right_nonneg" ":=" term ","
    "second_left_nonneg" ":=" term ","
    "second_right_nonneg" ":=" term ","
    "first_prec" ":=" term ","
    "second_prec" ":=" term :
  tactic

syntax (name := rr_hadamard_sequence_pf_named)
  "rr_hadamard_sequence_pf" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

syntax (name := rr_hadamard_sequence_nonneg_realrooted_named)
  "rr_hadamard_sequence_nonneg_realrooted" " using "
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "left_realrooted" ":=" term ","
    "right_realrooted" ":=" term :
  tactic

syntax (name := rr_hadamard_sequence_nonneg_coeffs_named)
  "rr_hadamard_sequence_nonneg_coeffs" " using "
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_hadamard_sequence_prec0_named)
  "rr_hadamard_sequence_prec0" " using "
    "first_left_nonneg" ":=" term ","
    "first_right_nonneg" ":=" term ","
    "second_left_nonneg" ":=" term ","
    "second_right_nonneg" ":=" term ","
    "first_prec" ":=" term ","
    "second_prec" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_schur_szego_nonzero_statement) =>
      `(tactic| exact RealRooted.finiteSchurSzegoCompositionNonzero)
  | `(tactic| rr_schur_szego_statement) =>
      `(tactic| exact RealRooted.finiteSchurSzegoComposition)
  | `(tactic|
      rr_schur_szego_pf_cubic_diagonal_base using
        schur_szego := $hSZ:term) =>
      `(tactic|
        exact RealRooted.pfCubicDiscrDiagonalNonnegStatement_of_schurSzego
          $hSZ)
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
      rr_schur_szego_pf_factor_degree_le_three_diagonal_base using
        diagonal_base := $hbase:term,
        level_ge_three := $hn:term,
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact
          finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
            $hbase $hn $hf $hfdeg $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_diagonal_base_splits using
        diagonal_base := $hbase:term,
        level_ge_three := $hn:term,
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.schurSzegoComp_splits_of_pf_factor_degree_le_three_diagonalBase
            $hbase $hn $hf $hfdeg $hpdeg $hsplits $hout)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree using
        diagonal_base := $hbase:term,
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        pf_degree := $hfn:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact
          schurSzegoComp_zero_or_splits_of_diagonalBase_leftDegree
            $hbase $hf $hfdeg $hfn $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree_splits
        using
        diagonal_base := $hbase:term,
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        pf_degree := $hfn:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact
          schurSzegoComp_splits_of_pf_factor_degree_le_three_diagonalBase_leftDegree
            $hbase $hf $hfdeg $hfn $hpdeg $hsplits $hout)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_num_left_degree using
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        pf_degree := $hfn:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        cubic_numerator := $hnum:term) =>
      `(tactic|
        exact
          finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
            $hf $hfdeg $hfn $hpdeg $hsplits $hnum)
  | `(tactic|
      rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits using
        pf_factor := $hf:term,
        pf_degree_le_three := $hfdeg:term,
        pf_degree := $hfn:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        cubic_numerator := $hnum:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.schurSzegoComp_splits_of_pf_factor_degree_le_three_num_leftDegree
            $hf $hfdeg $hfn $hpdeg $hsplits $hnum $hout)
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
      rr_schur_szego_sequence using
        pf_factor := $hf:term,
        pf_degree := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term) =>
      `(tactic|
        exact RealRooted.Tactic.schurSzegoComp_sequence_zero_or_splits
          $hf $hfdeg $hpdeg $hsplits)
  | `(tactic|
      rr_schur_szego_sequence_splits using
        pf_factor := $hf:term,
        pf_degree := $hfdeg:term,
        input_degree := $hpdeg:term,
        input_splits := $hsplits:term,
        nonzero := $hout:term) =>
      `(tactic|
        exact RealRooted.Tactic.schurSzegoComp_sequence_splits
          $hf $hfdeg $hpdeg $hsplits $hout)
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
  | `(tactic|
      rr_hadamard_prec0 using
        first_left_nonneg := $hf:term,
        first_right_nonneg := $hg:term,
        second_left_nonneg := $hp:term,
        second_right_nonneg := $hq:term,
        first_prec := $hfg:term,
        second_prec := $hpq:term) =>
      `(tactic|
        exact RealRooted.Tactic.hadamardProduct_prec0_of_nonneg_prec
          $hf $hg $hp $hq $hfg $hpq)
  | `(tactic|
      rr_hadamard_sequence_pf using
        left_pf := $hp:term,
        right_pf := $hq:term) =>
      `(tactic|
        exact RealRooted.Tactic.hadamardProduct_sequence_pf $hp $hq)
  | `(tactic|
      rr_hadamard_sequence_nonneg_realrooted using
        left_nonneg := $hpnn:term,
        right_nonneg := $hqnn:term,
        left_realrooted := $hp:term,
        right_realrooted := $hq:term) =>
      `(tactic|
        exact RealRooted.Tactic.hadamardProduct_sequence_nonneg_realrooted
          $hpnn $hqnn $hp $hq)
  | `(tactic|
      rr_hadamard_sequence_nonneg_coeffs using
        left_nonneg := $hpnn:term,
        right_nonneg := $hqnn:term) =>
      `(tactic|
        exact RealRooted.Tactic.hadamardProduct_sequence_nonneg_coeffs
          $hpnn $hqnn)
  | `(tactic|
      rr_hadamard_sequence_prec0 using
        first_left_nonneg := $hf:term,
        first_right_nonneg := $hg:term,
        second_left_nonneg := $hp:term,
        second_right_nonneg := $hq:term,
        first_prec := $hfg:term,
        second_prec := $hpq:term) =>
      `(tactic|
        exact RealRooted.Tactic.hadamardProduct_sequence_prec0
          $hf $hg $hp $hq $hfg $hpq)

end Tactic
end RealRooted
