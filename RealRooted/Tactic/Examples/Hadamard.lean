import RealRooted.Tactic.Hadamard

open Polynomial

namespace RealRooted
namespace Tactic

example :
    finiteSchurSzegoCompositionNonzeroStatement := by
  rr_schur_szego_nonzero_statement

example :
    finiteSchurSzegoCompositionStatement := by
  rr_schur_szego_statement

example (hSZ : finiteSchurSzegoCompositionStatement) :
    pfCubicDiscrDiagonalNonnegStatement := by
  rr_schur_szego_pf_cubic_diagonal_base using
    schur_szego := hSZ

example :
    schurPolyaWagnerHadamardPFStatement := by
  rr_hadamard_pf_statement

example :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  rr_hadamard_nonneg_realrooted_statement

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego using
    pf_factor := hf,
    pf_degree := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_splits using
    pf_factor := hf,
    pf_degree := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    (hfdeg : f.natDegree ≤ n)
    (hp0 : p ≠ 0)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_nonzero using
    pf_factor := hf,
    pf_nonzero := hf0,
    pf_degree := hfdeg,
    input_nonzero := hp0,
    input_degree := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hn : n ≤ 2)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_level_le_two using
    level_le_two := hn,
    pf_factor := hf,
    pf_degree := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hn : n ≤ 2)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_level_le_two_splits using
    level_le_two := hn,
    pf_factor := hf,
    pf_degree := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_two using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_two_splits using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_factors_degree_le_two using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree_le_two := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_factors_degree_le_two_splits using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree_le_two := hpdeg,
    input_splits := hsplits,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_cubic using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_discriminant := hdisc

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p))
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_cubic_splits using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_discriminant := hdisc,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hn : 3 ≤ n)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num using
    level_ge_three := hn,
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum

example {n : ℕ} {f p : ℝ[X]}
    (hn : 3 ≤ n)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num_splits using
    level_ge_three := hn,
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    (hn : 3 ≤ n)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_diagonal_base using
    diagonal_base := hbase,
    level_ge_three := hn,
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    (hn : 3 ≤ n)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_diagonal_base_splits using
    diagonal_base := hbase,
    level_ge_three := hn,
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree using
    diagonal_base := hbase,
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits

example {n : ℕ} {f p : ℝ[X]}
    (hbase : pfCubicDiscrDiagonalNonnegStatement)
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_diagonal_base_left_degree_splits
    using
    diagonal_base := hbase,
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits,
    nonzero := hout

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num_left_degree using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum

example {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum,
    nonzero := hout

example {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  rr_hadamard_pf using
    left_pf := hp,
    right_pf := hq

example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0 := by
  rr_hadamard_nonneg_realrooted using
    left_nonneg := hpnn,
    right_nonneg := hqnn,
    left_realrooted := hp,
    right_realrooted := hq

example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  rr_hadamard_nonneg_coeffs using
    left_nonneg := hpnn,
    right_nonneg := hqnn

end Tactic
end RealRooted
