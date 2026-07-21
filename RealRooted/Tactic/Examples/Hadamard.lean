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

example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ N i)
    (hPdeg : ∀ i : Nat, (P i).natDegree ≤ N i)
    (hPsplits : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      schurSzegoComp (N i) (F i) (P i) = 0 ∨
        (schurSzegoComp (N i) (F i) (P i)).Splits := by
  rr_schur_szego_sequence using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits

example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ N i)
    (hPdeg : ∀ i : Nat, (P i).natDegree ≤ N i)
    (hPsplits : ∀ i : Nat, (P i).Splits)
    (hout : ∀ i : Nat, schurSzegoComp (N i) (F i) (P i) ≠ 0) :
    ∀ i : Nat, (schurSzegoComp (N i) (F i) (P i)).Splits := by
  rr_schur_szego_sequence_splits using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits,
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

example {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f)
    (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p)
    (hq : HasNonnegCoeffs q)
    (hfg : Prec f g)
    (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rr_hadamard_prec0 using
    first_left_nonneg := hf,
    first_right_nonneg := hg,
    second_left_nonneg := hp,
    second_right_nonneg := hq,
    first_prec := hfg,
    second_prec := hpq

example {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i)) :
    ∀ i : Nat, IsPFPolynomial (hadamardProduct (P i) (Q i)) := by
  rr_hadamard_sequence_pf using
    left_pf := hP,
    right_pf := hQ

example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQnn : ∀ i : Nat, HasNonnegCoeffs (Q i))
    (hP : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hQ : ∀ i : Nat, Q i ≠ 0 ∧ (Q i).Splits) :
    ∀ i : Nat,
      (hadamardProduct (P i) (Q i) = 0 ∨
          (hadamardProduct (P i) (Q i)).Splits) ∧
        HasNonnegCoeffs (hadamardProduct (P i) (Q i)) ∧
        ∀ r ∈ (hadamardProduct (P i) (Q i)).roots, r ≤ 0 := by
  rr_hadamard_sequence_nonneg_realrooted using
    left_nonneg := hPnn,
    right_nonneg := hQnn,
    left_realrooted := hP,
    right_realrooted := hQ

example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQnn : ∀ i : Nat, HasNonnegCoeffs (Q i)) :
    ∀ i : Nat, HasNonnegCoeffs (hadamardProduct (P i) (Q i)) := by
  rr_hadamard_sequence_nonneg_coeffs using
    left_nonneg := hPnn,
    right_nonneg := hQnn

example {F G P Q : Nat → ℝ[X]}
    (hF : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hG : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQ : ∀ i : Nat, HasNonnegCoeffs (Q i))
    (hFG : ∀ i : Nat, Prec (F i) (G i))
    (hPQ : ∀ i : Nat, Prec (P i) (Q i)) :
    ∀ i : Nat,
      Prec0 (hadamardProduct (F i) (P i)) (hadamardProduct (G i) (Q i)) := by
  rr_hadamard_sequence_prec0 using
    first_left_nonneg := hF,
    first_right_nonneg := hG,
    second_left_nonneg := hP,
    second_right_nonneg := hQ,
    first_prec := hFG,
    second_prec := hPQ

end Tactic
end RealRooted
