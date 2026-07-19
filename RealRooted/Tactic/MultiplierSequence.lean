import RealRooted.MultiplierSequence

/-!
# Multiplier-sequence tactic frontends

Thin wrappers for diagonal operators, Jensen polynomials, and finite
multiplier-sequence preservation facts.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem jensenPolynomial_sequence_nonneg
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hGamma : ∀ i k, 0 ≤ Gamma i k) :
    ∀ i : Nat, HasNonnegCoeffs (jensenPolynomial (N i) (Gamma i)) := fun i =>
  hasNonnegCoeffs_jensenPolynomial (hGamma i)

theorem jensenPolynomial_sequence_natDegree_le
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ) :
    ∀ i : Nat, (jensenPolynomial (N i) (Gamma i)).natDegree ≤ N i := fun i =>
  natDegree_jensenPolynomial_le (N i) (Gamma i)

theorem jensenPolynomial_sequence_pf_of_finite_multiplier
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i)) := fun i =>
  isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
    (hGamma i) (hmult i)

theorem jensenPolynomial_sequence_pf_of_finite_pf_multiplier
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hmult : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i)) := fun i =>
  isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence (hmult i)

theorem finiteMultiplierSequence_sequence_mono
    {M N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hMN : ∀ i : Nat, M i ≤ N i)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFiniteMultiplierSequence (M i) (Gamma i) := fun i =>
  IsFiniteMultiplierSequence.mono (hMN i) (hmult i)

theorem finitePFMultiplierSequence_sequence_mono
    {M N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hMN : ∀ i : Nat, M i ≤ N i)
    (hmult : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (M i) (Gamma i) := fun i =>
  IsFinitePFMultiplierSequence.mono (hMN i) (hmult i)

theorem finiteMultiplierSequence_sequence_mul
    {N : Nat → ℕ} {Gamma Delta : Nat → ℕ → ℝ}
    (hGamma : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i))
    (hDelta : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Delta i)) :
    ∀ i : Nat, IsFiniteMultiplierSequence (N i)
      (fun k => Gamma i k * Delta i k) := fun i =>
  IsFiniteMultiplierSequence.mul (hGamma i) (hDelta i)

theorem finitePFMultiplierSequence_sequence_mul
    {N : Nat → ℕ} {Gamma Delta : Nat → ℕ → ℝ}
    (hGamma : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i))
    (hDelta : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Delta i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i)
      (fun k => Gamma i k * Delta i k) := fun i =>
  IsFinitePFMultiplierSequence.mul (hGamma i) (hDelta i)

theorem finitePFMultiplierSequence_sequence_of_finite_multiplier
    (N : Nat → ℕ) (Gamma : Nat → ℕ → ℝ)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i) := fun i =>
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence
    (hGamma i) (hmult i)

theorem finiteMultiplierSequence_sequence_le_two_of_jensen_pf
    {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hN : ∀ i : Nat, N i ≤ 2)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hjensen : ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))) :
    ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i) := fun i =>
  isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    (hN i) (hGamma i) (hjensen i)

theorem finitePFMultiplierSequence_sequence_le_two_of_jensen_pf
    {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hN : ∀ i : Nat, N i ≤ 2)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hjensen : ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i) := fun i =>
  isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    (hN i) (hGamma i) (hjensen i)

syntax (name := rr_diagonal_nonneg_named)
  "rr_diagonal_nonneg" " using "
    "nonneg" ":=" term ","
    "sequence_nonneg" ":=" term :
  tactic

syntax (name := rr_diagonal_natDegree_le_named)
  "rr_diagonal_natDegree_le" :
  tactic

syntax (name := rr_diagonal_add_named)
  "rr_diagonal_add" :
  tactic

syntax (name := rr_diagonal_sub_named)
  "rr_diagonal_sub" :
  tactic

syntax (name := rr_diagonal_neg_named)
  "rr_diagonal_neg" :
  tactic

syntax (name := rr_diagonal_C_mul_named)
  "rr_diagonal_C_mul" :
  tactic

syntax (name := rr_diagonal_comp_named)
  "rr_diagonal_comp" :
  tactic

syntax (name := rr_diagonal_comm_named)
  "rr_diagonal_comm" :
  tactic

syntax (name := rr_diagonal_splits_cubic_named)
  "rr_diagonal_splits_cubic" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

syntax (name := rr_diagonal_splits_le_three_named)
  "rr_diagonal_splits_le_three" " using "
    "degree_le" ":=" term ","
    "discriminant" ":=" term :
  tactic

syntax (name := rr_jensen_nonneg_named)
  "rr_jensen_nonneg" " using " "sequence_nonneg" ":=" term :
  tactic

syntax (name := rr_jensen_sequence_nonneg_named)
  "rr_jensen_sequence_nonneg" " using "
    "level" ":=" term ","
    "sequence_nonneg" ":=" term :
  tactic

syntax (name := rr_jensen_natDegree_le_named)
  "rr_jensen_natDegree_le" :
  tactic

syntax (name := rr_jensen_sequence_natDegree_le_named)
  "rr_jensen_sequence_natDegree_le" " using "
    "level" ":=" term ","
    "sequence" ":=" term :
  tactic

syntax (name := rr_jensen_zero_iff_named)
  "rr_jensen_zero_iff" :
  tactic

syntax (name := rr_jensen_as_diagonal_X_add_one_pow_named)
  "rr_jensen_as_diagonal_X_add_one_pow" :
  tactic

syntax (name := rr_jensen_mul_sequence_as_diagonal_named)
  "rr_jensen_mul_sequence_as_diagonal" :
  tactic

syntax (name := rr_jensen_quadratic_sequence_factor_named)
  "rr_jensen_quadratic_sequence_factor" " using " "degree_ge_two" ":=" term :
  tactic

syntax (name := rr_jensen_cubic_discr_named)
  "rr_jensen_cubic_discr" :
  tactic

syntax (name := rr_jensen_three_discr_nonneg_named)
  "rr_jensen_three_discr_nonneg" " using " "zero_or_splits" ":=" term :
  tactic

syntax (name := rr_jensen_pf_three_discr_nonneg_named)
  "rr_jensen_pf_three_discr_nonneg" " using " "pf" ":=" term :
  tactic

syntax (name := rr_jensen_three_discr_iff_zero_or_splits_named)
  "rr_jensen_three_discr_iff_zero_or_splits" :
  tactic

syntax (name := rr_jensen_three_log_concave_named)
  "rr_jensen_three_log_concave" " using " "zero_or_splits" ":=" term :
  tactic

syntax (name := rr_jensen_pf_three_log_concave_named)
  "rr_jensen_pf_three_log_concave" " using " "pf" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_mono_named)
  "rr_finite_multiplier_mono" " using "
    "degree_le" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_mono_named)
  "rr_finite_pf_multiplier_mono" " using "
    "degree_le" ":=" term ","
    "pf_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_sequence_mono_named)
  "rr_finite_multiplier_sequence_mono" " using "
    "degree_le" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_sequence_mono_named)
  "rr_finite_pf_multiplier_sequence_mono" " using "
    "degree_le" ":=" term ","
    "pf_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_mul_named)
  "rr_finite_multiplier_mul" " using "
    "left_multiplier" ":=" term ","
    "right_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_mul_named)
  "rr_finite_pf_multiplier_mul" " using "
    "left_pf_multiplier" ":=" term ","
    "right_pf_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_sequence_mul_named)
  "rr_finite_multiplier_sequence_mul" " using "
    "left_multiplier" ":=" term ","
    "right_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_sequence_mul_named)
  "rr_finite_pf_multiplier_sequence_mul" " using "
    "left_pf_multiplier" ":=" term ","
    "right_pf_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_const_named)
  "rr_finite_multiplier_const" :
  tactic

syntax (name := rr_finite_pf_multiplier_const_named)
  "rr_finite_pf_multiplier_const" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_one_named)
  "rr_finite_multiplier_one" :
  tactic

syntax (name := rr_finite_pf_multiplier_one_named)
  "rr_finite_pf_multiplier_one" :
  tactic

syntax (name := rr_finite_multiplier_zero_named)
  "rr_finite_multiplier_zero" :
  tactic

syntax (name := rr_finite_pf_multiplier_zero_named)
  "rr_finite_pf_multiplier_zero" :
  tactic

syntax (name := rr_finite_multiplier_le_one_named)
  "rr_finite_multiplier_le_one" " using " "degree_le_one" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_degree_zero_named)
  "rr_finite_multiplier_degree_zero" :
  tactic

syntax (name := rr_finite_multiplier_degree_one_named)
  "rr_finite_multiplier_degree_one" :
  tactic

syntax (name := rr_finite_multiplier_le_two_of_jensen_pf_named)
  "rr_finite_multiplier_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_degree_two_of_jensen_pf_named)
  "rr_finite_multiplier_degree_two_of_jensen_pf" " using "
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

syntax (name := rr_jensen_pf_of_finite_multiplier_named)
  "rr_jensen_pf_of_finite_multiplier" " using "
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_jensen_sequence_pf_of_finite_multiplier_named)
  "rr_jensen_sequence_pf_of_finite_multiplier" " using "
    "level" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_jensen_pf_of_finite_pf_multiplier_named)
  "rr_jensen_pf_of_finite_pf_multiplier" " using " "pf_multiplier" ":=" term :
  tactic

syntax (name := rr_jensen_sequence_pf_of_finite_pf_multiplier_named)
  "rr_jensen_sequence_pf_of_finite_pf_multiplier" " using "
    "level" ":=" term ","
    "pf_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_three_log_concave_named)
  "rr_finite_multiplier_three_log_concave" " using "
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_three_log_concave_named)
  "rr_finite_pf_multiplier_three_log_concave" " using "
    "pf_multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_of_finite_multiplier_named)
  "rr_finite_pf_multiplier_of_finite_multiplier" " using "
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_sequence_of_finite_multiplier_named)
  "rr_finite_pf_multiplier_sequence_of_finite_multiplier" " using "
    "level" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_le_one_named)
  "rr_finite_pf_multiplier_le_one" " using "
    "degree_le_one" ":=" term ","
    "sequence_nonneg" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_degree_zero_named)
  "rr_finite_pf_multiplier_degree_zero" " using " "sequence_nonneg" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_degree_one_named)
  "rr_finite_pf_multiplier_degree_one" " using " "sequence_nonneg" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_le_two_of_jensen_pf_named)
  "rr_finite_pf_multiplier_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_degree_two_of_jensen_pf_named)
  "rr_finite_pf_multiplier_degree_two_of_jensen_pf" " using "
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

syntax (name := rr_finite_multiplier_sequence_le_two_of_jensen_pf_named)
  "rr_finite_multiplier_sequence_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

syntax (name := rr_finite_pf_multiplier_sequence_le_two_of_jensen_pf_named)
  "rr_finite_pf_multiplier_sequence_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_diagonal_nonneg using
        nonneg := $hp:term,
        sequence_nonneg := $hgamma:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.diagonalOperator $hp $hgamma)
  | `(tactic| rr_diagonal_natDegree_le) =>
      `(tactic| exact RealRooted.natDegree_diagonalOperator_le _ _)
  | `(tactic| rr_diagonal_add) =>
      `(tactic| exact RealRooted.diagonalOperator_add _ _ _)
  | `(tactic| rr_diagonal_sub) =>
      `(tactic| exact RealRooted.diagonalOperator_sub _ _ _)
  | `(tactic| rr_diagonal_neg) =>
      `(tactic| exact RealRooted.diagonalOperator_neg _ _)
  | `(tactic| rr_diagonal_C_mul) =>
      `(tactic| exact RealRooted.diagonalOperator_C_mul _ _ _)
  | `(tactic| rr_diagonal_comp) =>
      `(tactic| exact RealRooted.diagonalOperator_comp _ _ _)
  | `(tactic| rr_diagonal_comm) =>
      `(tactic| exact RealRooted.diagonalOperator_comm _ _ _)
  | `(tactic|
      rr_diagonal_splits_cubic using
        degree := $hdeg:term,
        discriminant := $hdisc:term) =>
      `(tactic|
        exact RealRooted.diagonalOperator_splits_of_natDegree_three_cubicDiscr_nonneg
          $hdeg $hdisc)
  | `(tactic|
      rr_diagonal_splits_le_three using
        degree_le := $hdeg:term,
        discriminant := $hdisc:term) =>
      `(tactic|
        exact RealRooted.diagonalOperator_splits_of_natDegree_le_three_cubicDiscr_nonneg
          $hdeg $hdisc)
  | `(tactic| rr_jensen_nonneg using sequence_nonneg := $hgamma:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_jensenPolynomial $hgamma)
  | `(tactic|
      rr_jensen_sequence_nonneg using
        level := $N:term,
        sequence_nonneg := $hgamma:term) =>
      `(tactic|
        exact RealRooted.Tactic.jensenPolynomial_sequence_nonneg
          $N _ $hgamma)
  | `(tactic| rr_jensen_natDegree_le) =>
      `(tactic| exact RealRooted.natDegree_jensenPolynomial_le _ _)
  | `(tactic|
      rr_jensen_sequence_natDegree_le using
        level := $N:term,
        sequence := $Gamma:term) =>
      `(tactic|
        exact RealRooted.Tactic.jensenPolynomial_sequence_natDegree_le
          $N $Gamma)
  | `(tactic| rr_jensen_zero_iff) =>
      `(tactic| exact RealRooted.jensenPolynomial_eq_zero_iff)
  | `(tactic| rr_jensen_as_diagonal_X_add_one_pow) =>
      `(tactic| exact RealRooted.jensenPolynomial_eq_diagonalOperator_X_add_one_pow _ _)
  | `(tactic| rr_jensen_mul_sequence_as_diagonal) =>
      `(tactic| exact RealRooted.jensenPolynomial_mul_sequence_eq_diagonalOperator _ _ _)
  | `(tactic| rr_jensen_quadratic_sequence_factor using degree_ge_two := $hd:term) =>
      `(tactic| exact RealRooted.jensenPolynomial_quadratic_sequence_factor _ _ _ _ $hd)
  | `(tactic| rr_jensen_cubic_discr) =>
      `(tactic| exact RealRooted.cubicDiscr_jensenPolynomial_three _)
  | `(tactic| rr_jensen_three_discr_nonneg using zero_or_splits := $hs:term) =>
      `(tactic|
        exact RealRooted.cubicDiscr_jensenPolynomial_three_nonneg_of_eq_zero_or_splits
          $hs)
  | `(tactic| rr_jensen_pf_three_discr_nonneg using pf := $hj:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.cubicDiscr_jensenPolynomial_three_nonneg $hj)
  | `(tactic| rr_jensen_three_discr_iff_zero_or_splits) =>
      `(tactic| exact RealRooted.cubicDiscr_jensenPolynomial_three_nonneg_iff_eq_zero_or_splits)
  | `(tactic| rr_jensen_three_log_concave using zero_or_splits := $hs:term) =>
      `(tactic| exact RealRooted.jensenPolynomial_three_logConcave_of_eq_zero_or_splits $hs)
  | `(tactic| rr_jensen_pf_three_log_concave using pf := $hj:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.jensenPolynomial_three_logConcave $hj)
  | `(tactic|
      rr_finite_multiplier_mono using
        degree_le := $hmn:term,
        multiplier := $h:term) =>
      `(tactic| exact RealRooted.IsFiniteMultiplierSequence.mono $hmn $h)
  | `(tactic|
      rr_finite_pf_multiplier_mono using
        degree_le := $hmn:term,
        pf_multiplier := $h:term) =>
      `(tactic| exact RealRooted.IsFinitePFMultiplierSequence.mono $hmn $h)
  | `(tactic|
      rr_finite_multiplier_sequence_mono using
        degree_le := $hmn:term,
        multiplier := $h:term) =>
      `(tactic|
        exact RealRooted.Tactic.finiteMultiplierSequence_sequence_mono
          $hmn $h)
  | `(tactic|
      rr_finite_pf_multiplier_sequence_mono using
        degree_le := $hmn:term,
        pf_multiplier := $h:term) =>
      `(tactic|
        exact RealRooted.Tactic.finitePFMultiplierSequence_sequence_mono
          $hmn $h)
  | `(tactic|
      rr_finite_multiplier_mul using
        left_multiplier := $hgamma:term,
        right_multiplier := $hdelta:term) =>
      `(tactic| exact RealRooted.IsFiniteMultiplierSequence.mul $hgamma $hdelta)
  | `(tactic|
      rr_finite_pf_multiplier_mul using
        left_pf_multiplier := $hgamma:term,
        right_pf_multiplier := $hdelta:term) =>
      `(tactic| exact RealRooted.IsFinitePFMultiplierSequence.mul $hgamma $hdelta)
  | `(tactic|
      rr_finite_multiplier_sequence_mul using
        left_multiplier := $hgamma:term,
        right_multiplier := $hdelta:term) =>
      `(tactic|
        exact RealRooted.Tactic.finiteMultiplierSequence_sequence_mul
          $hgamma $hdelta)
  | `(tactic|
      rr_finite_pf_multiplier_sequence_mul using
        left_pf_multiplier := $hgamma:term,
        right_pf_multiplier := $hdelta:term) =>
      `(tactic|
        exact RealRooted.Tactic.finitePFMultiplierSequence_sequence_mul
          $hgamma $hdelta)
  | `(tactic| rr_finite_multiplier_const) =>
      `(tactic| exact RealRooted.isFiniteMultiplierSequence_const_sequence _ _)
  | `(tactic| rr_finite_pf_multiplier_const using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.isFinitePFMultiplierSequence_const_sequence $ha)
  | `(tactic| rr_finite_multiplier_one) =>
      `(tactic| exact RealRooted.isFiniteMultiplierSequence_one_sequence _)
  | `(tactic| rr_finite_pf_multiplier_one) =>
      `(tactic| exact RealRooted.isFinitePFMultiplierSequence_one_sequence _)
  | `(tactic| rr_finite_multiplier_zero) =>
      `(tactic| exact RealRooted.isFiniteMultiplierSequence_zero_sequence _)
  | `(tactic| rr_finite_pf_multiplier_zero) =>
      `(tactic| exact RealRooted.isFinitePFMultiplierSequence_zero_sequence _)
  | `(tactic| rr_finite_multiplier_le_one using degree_le_one := $hn:term) =>
      `(tactic| exact RealRooted.isFiniteMultiplierSequence_of_natDegree_le_one $hn _)
  | `(tactic| rr_finite_multiplier_degree_zero) =>
      `(tactic| exact RealRooted.isFiniteMultiplierSequence_natDegree_zero _)
  | `(tactic| rr_finite_multiplier_degree_one) =>
      `(tactic| exact RealRooted.isFiniteMultiplierSequence_natDegree_one _)
  | `(tactic|
      rr_finite_multiplier_le_two_of_jensen_pf using
        degree_le_two := $hn:term,
        sequence_nonneg := $hgamma:term,
        jensen_pf := $hj:term) =>
      `(tactic|
        exact RealRooted.isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
          $hn $hgamma $hj)
  | `(tactic|
      rr_finite_multiplier_degree_two_of_jensen_pf using
        sequence_nonneg := $hgamma:term,
        jensen_pf := $hj:term) =>
      `(tactic|
        exact RealRooted.isFiniteMultiplierSequence_natDegree_two_of_isPF_jensenPolynomial
          $hgamma $hj)
  | `(tactic|
      rr_jensen_pf_of_finite_multiplier using
        sequence_nonneg := $hgamma:term,
        multiplier := $hmult:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
          $hgamma $hmult)
  | `(tactic|
      rr_jensen_sequence_pf_of_finite_multiplier using
        level := $N:term,
        sequence_nonneg := $hgamma:term,
        multiplier := $hmult:term) =>
      `(tactic|
        exact RealRooted.Tactic.jensenPolynomial_sequence_pf_of_finite_multiplier
          $N _ $hgamma $hmult)
  | `(tactic| rr_jensen_pf_of_finite_pf_multiplier using pf_multiplier := $hmult:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
          $hmult)
  | `(tactic|
      rr_jensen_sequence_pf_of_finite_pf_multiplier using
        level := $N:term,
        pf_multiplier := $hmult:term) =>
      `(tactic|
        exact RealRooted.Tactic.jensenPolynomial_sequence_pf_of_finite_pf_multiplier
          $N _ $hmult)
  | `(tactic|
      rr_finite_multiplier_three_log_concave using
        sequence_nonneg := $hgamma:term,
        multiplier := $hmult:term) =>
      `(tactic| exact RealRooted.finiteMultiplierSequence_three_logConcave $hgamma $hmult)
  | `(tactic|
      rr_finite_pf_multiplier_three_log_concave using
        pf_multiplier := $hmult:term) =>
      `(tactic| exact RealRooted.finitePFMultiplierSequence_three_logConcave $hmult)
  | `(tactic|
      rr_finite_pf_multiplier_of_finite_multiplier using
        sequence_nonneg := $hgamma:term,
        multiplier := $hmult:term) =>
      `(tactic|
        exact RealRooted.isFinitePFMultiplierSequence_of_finiteMultiplierSequence
          $hgamma $hmult)
  | `(tactic|
      rr_finite_pf_multiplier_sequence_of_finite_multiplier using
        level := $N:term,
        sequence_nonneg := $hgamma:term,
        multiplier := $hmult:term) =>
      `(tactic|
        exact RealRooted.Tactic.finitePFMultiplierSequence_sequence_of_finite_multiplier
          $N _ $hgamma $hmult)
  | `(tactic|
      rr_finite_pf_multiplier_le_one using
        degree_le_one := $hn:term,
        sequence_nonneg := $hgamma:term) =>
      `(tactic|
        exact RealRooted.isFinitePFMultiplierSequence_of_natDegree_le_one
          $hn $hgamma)
  | `(tactic|
      rr_finite_pf_multiplier_degree_zero using
        sequence_nonneg := $hgamma:term) =>
      `(tactic| exact RealRooted.isFinitePFMultiplierSequence_natDegree_zero $hgamma)
  | `(tactic|
      rr_finite_pf_multiplier_degree_one using
        sequence_nonneg := $hgamma:term) =>
      `(tactic| exact RealRooted.isFinitePFMultiplierSequence_natDegree_one $hgamma)
  | `(tactic|
      rr_finite_pf_multiplier_le_two_of_jensen_pf using
        degree_le_two := $hn:term,
        sequence_nonneg := $hgamma:term,
        jensen_pf := $hj:term) =>
      `(tactic|
        exact RealRooted.isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
          $hn $hgamma $hj)
  | `(tactic|
      rr_finite_pf_multiplier_degree_two_of_jensen_pf using
        sequence_nonneg := $hgamma:term,
        jensen_pf := $hj:term) =>
      `(tactic|
        exact RealRooted.isFinitePFMultiplierSequence_natDegree_two_of_isPF_jensenPolynomial
          $hgamma $hj)
  | `(tactic|
      rr_finite_multiplier_sequence_le_two_of_jensen_pf using
        degree_le_two := $hn:term,
        sequence_nonneg := $hgamma:term,
        jensen_pf := $hj:term) =>
      `(tactic|
        exact RealRooted.Tactic.finiteMultiplierSequence_sequence_le_two_of_jensen_pf
          $hn $hgamma $hj)
  | `(tactic|
      rr_finite_pf_multiplier_sequence_le_two_of_jensen_pf using
        degree_le_two := $hn:term,
        sequence_nonneg := $hgamma:term,
        jensen_pf := $hj:term) =>
      `(tactic|
        exact RealRooted.Tactic.finitePFMultiplierSequence_sequence_le_two_of_jensen_pf
          $hn $hgamma $hj)

end Tactic
end RealRooted
