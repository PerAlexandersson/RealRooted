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

/-- Closes `HasNonnegCoeffs (diagonalOperator gamma p)` from `nonneg : HasNonnegCoeffs p` and
`sequence_nonneg : ∀ k, 0 ≤ gamma k`. -/
syntax (name := rr_diagonal_nonneg_named)
  "rr_diagonal_nonneg" " using "
    "nonneg" ":=" term ","
    "sequence_nonneg" ":=" term :
  tactic

/-- Closes `(diagonalOperator gamma p).natDegree ≤ p.natDegree`. -/
syntax (name := rr_diagonal_natDegree_le_named)
  "rr_diagonal_natDegree_le" :
  tactic

/-- Closes
`diagonalOperator gamma (p + q) = diagonalOperator gamma p + diagonalOperator gamma q`. -/
syntax (name := rr_diagonal_add_named)
  "rr_diagonal_add" :
  tactic

/-- Closes
`diagonalOperator gamma (p - q) = diagonalOperator gamma p - diagonalOperator gamma q`. -/
syntax (name := rr_diagonal_sub_named)
  "rr_diagonal_sub" :
  tactic

/-- Closes `diagonalOperator gamma (-p) = -diagonalOperator gamma p`. -/
syntax (name := rr_diagonal_neg_named)
  "rr_diagonal_neg" :
  tactic

/-- Closes `diagonalOperator gamma (C a * p) = C a * diagonalOperator gamma p`. -/
syntax (name := rr_diagonal_C_mul_named)
  "rr_diagonal_C_mul" :
  tactic

/-- Closes `diagonalOperator gamma (diagonalOperator delta p) = diagonalOperator (gamma * delta) p`,
where `gamma * delta` stands for `fun n => gamma n * delta n`. -/
syntax (name := rr_diagonal_comp_named)
  "rr_diagonal_comp" :
  tactic

/-- Closes `diagonalOperator gamma (diagonalOperator delta p) = diagonalOperator delta
(diagonalOperator gamma p)`. -/
syntax (name := rr_diagonal_comm_named)
  "rr_diagonal_comm" :
  tactic

/-- Closes `(diagonalOperator gamma p).Splits` from
`degree : (diagonalOperator gamma p).natDegree = 3` and
`discriminant : 0 ≤ cubicDiscr (diagonalOperator gamma p)`. -/
syntax (name := rr_diagonal_splits_cubic_named)
  "rr_diagonal_splits_cubic" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

/-- Closes `(diagonalOperator gamma p).Splits` from
`degree_le : (diagonalOperator gamma p).natDegree ≤ 3` and
`discriminant : 0 ≤ cubicDiscr (diagonalOperator gamma p)`. -/
syntax (name := rr_diagonal_splits_le_three_named)
  "rr_diagonal_splits_le_three" " using "
    "degree_le" ":=" term ","
    "discriminant" ":=" term :
  tactic

/-- Closes `HasNonnegCoeffs (jensenPolynomial n gamma)` from
`sequence_nonneg : ∀ k, 0 ≤ gamma k`. -/
syntax (name := rr_jensen_nonneg_named)
  "rr_jensen_nonneg" " using " "sequence_nonneg" ":=" term :
  tactic

/-- Closes `∀ i, HasNonnegCoeffs (jensenPolynomial (N i) (Gamma i))` from the `level` sequence `N`
and `sequence_nonneg : ∀ i k, 0 ≤ Gamma i k`. -/
syntax (name := rr_jensen_sequence_nonneg_named)
  "rr_jensen_sequence_nonneg" " using "
    "level" ":=" term ","
    "sequence_nonneg" ":=" term :
  tactic

/-- Closes `(jensenPolynomial n gamma).natDegree ≤ n`. -/
syntax (name := rr_jensen_natDegree_le_named)
  "rr_jensen_natDegree_le" :
  tactic

/-- Closes `∀ i, (jensenPolynomial (N i) (Gamma i)).natDegree ≤ N i` for the `level` sequence `N`
and the `sequence` `Gamma`. -/
syntax (name := rr_jensen_sequence_natDegree_le_named)
  "rr_jensen_sequence_natDegree_le" " using "
    "level" ":=" term ","
    "sequence" ":=" term :
  tactic

/-- Closes `jensenPolynomial n gamma = 0 ↔ ∀ k ≤ n, gamma k = 0`. -/
syntax (name := rr_jensen_zero_iff_named)
  "rr_jensen_zero_iff" :
  tactic

/-- Closes `jensenPolynomial n gamma = diagonalOperator gamma ((X + 1) ^ n)`. -/
syntax (name := rr_jensen_as_diagonal_X_add_one_pow_named)
  "rr_jensen_as_diagonal_X_add_one_pow" :
  tactic

/-- Closes `jensenPolynomial n (fun k => gamma k * delta k) = diagonalOperator gamma
(jensenPolynomial n delta)`. -/
syntax (name := rr_jensen_mul_sequence_as_diagonal_named)
  "rr_jensen_mul_sequence_as_diagonal" :
  tactic

/-- Closes the factorization of the Jensen polynomial of `fun k => a * k ^ 2 + b * k + c` as
`(X + 1) ^ (d - 2)` times a quadratic, from `degree_ge_two : 2 ≤ d`. -/
syntax (name := rr_jensen_quadratic_sequence_factor_named)
  "rr_jensen_quadratic_sequence_factor" " using " "degree_ge_two" ":=" term :
  tactic

/-- Closes the closed formula for `cubicDiscr (jensenPolynomial 3 gamma)` in terms of `gamma 0`,
`gamma 1`, `gamma 2` and `gamma 3`. -/
syntax (name := rr_jensen_cubic_discr_named)
  "rr_jensen_cubic_discr" :
  tactic

/-- Closes `0 ≤ cubicDiscr (jensenPolynomial 3 gamma)` from `zero_or_splits`, which says that the
Jensen polynomial is zero or splits. -/
syntax (name := rr_jensen_three_discr_nonneg_named)
  "rr_jensen_three_discr_nonneg" " using " "zero_or_splits" ":=" term :
  tactic

/-- Closes `0 ≤ cubicDiscr (jensenPolynomial 3 gamma)` from
`pf : IsPFPolynomial (jensenPolynomial 3 gamma)`. -/
syntax (name := rr_jensen_pf_three_discr_nonneg_named)
  "rr_jensen_pf_three_discr_nonneg" " using " "pf" ":=" term :
  tactic

/-- Closes `0 ≤ cubicDiscr (jensenPolynomial 3 gamma) ↔ jensenPolynomial 3 gamma = 0 ∨
(jensenPolynomial 3 gamma).Splits`. -/
syntax (name := rr_jensen_three_discr_iff_zero_or_splits_named)
  "rr_jensen_three_discr_iff_zero_or_splits" :
  tactic

/-- Closes `gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧ gamma 1 * gamma 3 ≤ gamma 2 ^ 2` from `zero_or_splits`
for `jensenPolynomial 3 gamma`. -/
syntax (name := rr_jensen_three_log_concave_named)
  "rr_jensen_three_log_concave" " using " "zero_or_splits" ":=" term :
  tactic

/-- Closes `gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧ gamma 1 * gamma 3 ≤ gamma 2 ^ 2` from
`pf : IsPFPolynomial (jensenPolynomial 3 gamma)`. -/
syntax (name := rr_jensen_pf_three_log_concave_named)
  "rr_jensen_pf_three_log_concave" " using " "pf" ":=" term :
  tactic

/-- Closes `IsFiniteMultiplierSequence m gamma` from `degree_le : m ≤ n` and
`multiplier : IsFiniteMultiplierSequence n gamma`. -/
syntax (name := rr_finite_multiplier_mono_named)
  "rr_finite_multiplier_mono" " using "
    "degree_le" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence m gamma` from `degree_le : m ≤ n` and
`pf_multiplier : IsFinitePFMultiplierSequence n gamma`. -/
syntax (name := rr_finite_pf_multiplier_mono_named)
  "rr_finite_pf_multiplier_mono" " using "
    "degree_le" ":=" term ","
    "pf_multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_finite_multiplier_mono`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_finite_multiplier_sequence_mono_named)
  "rr_finite_multiplier_sequence_mono" " using "
    "degree_le" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_finite_pf_multiplier_mono`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_finite_pf_multiplier_sequence_mono_named)
  "rr_finite_pf_multiplier_sequence_mono" " using "
    "degree_le" ":=" term ","
    "pf_multiplier" ":=" term :
  tactic

/-- Closes `IsFiniteMultiplierSequence n (fun k => gamma k * delta k)` from `left_multiplier` for
`gamma` and `right_multiplier` for `delta`. -/
syntax (name := rr_finite_multiplier_mul_named)
  "rr_finite_multiplier_mul" " using "
    "left_multiplier" ":=" term ","
    "right_multiplier" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n (fun k => gamma k * delta k)` from `left_pf_multiplier`
for `gamma` and `right_pf_multiplier` for `delta`. -/
syntax (name := rr_finite_pf_multiplier_mul_named)
  "rr_finite_pf_multiplier_mul" " using "
    "left_pf_multiplier" ":=" term ","
    "right_pf_multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_finite_multiplier_mul`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_finite_multiplier_sequence_mul_named)
  "rr_finite_multiplier_sequence_mul" " using "
    "left_multiplier" ":=" term ","
    "right_multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_finite_pf_multiplier_mul`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_finite_pf_multiplier_sequence_mul_named)
  "rr_finite_pf_multiplier_sequence_mul" " using "
    "left_pf_multiplier" ":=" term ","
    "right_pf_multiplier" ":=" term :
  tactic

/-- Closes `IsFiniteMultiplierSequence n (fun _ => a)` for a constant sequence. -/
syntax (name := rr_finite_multiplier_const_named)
  "rr_finite_multiplier_const" :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n (fun _ => a)` from `scalar_nonneg : 0 ≤ a`. -/
syntax (name := rr_finite_pf_multiplier_const_named)
  "rr_finite_pf_multiplier_const" " using " "scalar_nonneg" ":=" term :
  tactic

/-- Closes `IsFiniteMultiplierSequence n (fun _ => 1)`. -/
syntax (name := rr_finite_multiplier_one_named)
  "rr_finite_multiplier_one" :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n (fun _ => 1)`. -/
syntax (name := rr_finite_pf_multiplier_one_named)
  "rr_finite_pf_multiplier_one" :
  tactic

/-- Closes `IsFiniteMultiplierSequence n (fun _ => 0)`. -/
syntax (name := rr_finite_multiplier_zero_named)
  "rr_finite_multiplier_zero" :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n (fun _ => 0)`. -/
syntax (name := rr_finite_pf_multiplier_zero_named)
  "rr_finite_pf_multiplier_zero" :
  tactic

/-- Closes `IsFiniteMultiplierSequence n gamma` for every `gamma`, from `degree_le_one : n ≤ 1`. -/
syntax (name := rr_finite_multiplier_le_one_named)
  "rr_finite_multiplier_le_one" " using " "degree_le_one" ":=" term :
  tactic

/-- Closes `IsFiniteMultiplierSequence 0 gamma`. -/
syntax (name := rr_finite_multiplier_degree_zero_named)
  "rr_finite_multiplier_degree_zero" :
  tactic

/-- Closes `IsFiniteMultiplierSequence 1 gamma`. -/
syntax (name := rr_finite_multiplier_degree_one_named)
  "rr_finite_multiplier_degree_one" :
  tactic

/-- Closes `IsFiniteMultiplierSequence n gamma` from `degree_le_two : n ≤ 2`,
`sequence_nonneg : ∀ k, 0 ≤ gamma k` and `jensen_pf : IsPFPolynomial (jensenPolynomial n gamma)`. -/
syntax (name := rr_finite_multiplier_le_two_of_jensen_pf_named)
  "rr_finite_multiplier_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

/-- Closes `IsFiniteMultiplierSequence 2 gamma` from `sequence_nonneg : ∀ k, 0 ≤ gamma k` and
`jensen_pf : IsPFPolynomial (jensenPolynomial 2 gamma)`. -/
syntax (name := rr_finite_multiplier_degree_two_of_jensen_pf_named)
  "rr_finite_multiplier_degree_two_of_jensen_pf" " using "
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (jensenPolynomial n gamma)` from `sequence_nonneg : ∀ k, 0 ≤ gamma k` and
`multiplier : IsFiniteMultiplierSequence n gamma`. -/
syntax (name := rr_jensen_pf_of_finite_multiplier_named)
  "rr_jensen_pf_of_finite_multiplier" " using "
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_jensen_pf_of_finite_multiplier`: for the `level` sequence `N`, closes
`∀ i, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))`. -/
syntax (name := rr_jensen_sequence_pf_of_finite_multiplier_named)
  "rr_jensen_sequence_pf_of_finite_multiplier" " using "
    "level" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Closes `IsPFPolynomial (jensenPolynomial n gamma)` from
`pf_multiplier : IsFinitePFMultiplierSequence n gamma`. -/
syntax (name := rr_jensen_pf_of_finite_pf_multiplier_named)
  "rr_jensen_pf_of_finite_pf_multiplier" " using " "pf_multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_jensen_pf_of_finite_pf_multiplier`: for the `level` sequence `N`, closes
`∀ i, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))`. -/
syntax (name := rr_jensen_sequence_pf_of_finite_pf_multiplier_named)
  "rr_jensen_sequence_pf_of_finite_pf_multiplier" " using "
    "level" ":=" term ","
    "pf_multiplier" ":=" term :
  tactic

/-- Closes `gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧ gamma 1 * gamma 3 ≤ gamma 2 ^ 2` from
`sequence_nonneg : ∀ k, 0 ≤ gamma k` and `multiplier : IsFiniteMultiplierSequence 3 gamma`. -/
syntax (name := rr_finite_multiplier_three_log_concave_named)
  "rr_finite_multiplier_three_log_concave" " using "
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Closes `gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧ gamma 1 * gamma 3 ≤ gamma 2 ^ 2` from
`pf_multiplier : IsFinitePFMultiplierSequence 3 gamma`. -/
syntax (name := rr_finite_pf_multiplier_three_log_concave_named)
  "rr_finite_pf_multiplier_three_log_concave" " using "
    "pf_multiplier" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n gamma` from `sequence_nonneg : ∀ k, 0 ≤ gamma k` and
`multiplier : IsFiniteMultiplierSequence n gamma`. -/
syntax (name := rr_finite_pf_multiplier_of_finite_multiplier_named)
  "rr_finite_pf_multiplier_of_finite_multiplier" " using "
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Sequence form of `rr_finite_pf_multiplier_of_finite_multiplier`: for the `level` sequence `N`,
closes `∀ i, IsFinitePFMultiplierSequence (N i) (Gamma i)`. -/
syntax (name := rr_finite_pf_multiplier_sequence_of_finite_multiplier_named)
  "rr_finite_pf_multiplier_sequence_of_finite_multiplier" " using "
    "level" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "multiplier" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n gamma` from `degree_le_one : n ≤ 1` and
`sequence_nonneg : ∀ k, 0 ≤ gamma k`. -/
syntax (name := rr_finite_pf_multiplier_le_one_named)
  "rr_finite_pf_multiplier_le_one" " using "
    "degree_le_one" ":=" term ","
    "sequence_nonneg" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence 0 gamma` from `sequence_nonneg : ∀ k, 0 ≤ gamma k`. -/
syntax (name := rr_finite_pf_multiplier_degree_zero_named)
  "rr_finite_pf_multiplier_degree_zero" " using " "sequence_nonneg" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence 1 gamma` from `sequence_nonneg : ∀ k, 0 ≤ gamma k`. -/
syntax (name := rr_finite_pf_multiplier_degree_one_named)
  "rr_finite_pf_multiplier_degree_one" " using " "sequence_nonneg" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence n gamma` from `degree_le_two : n ≤ 2`,
`sequence_nonneg : ∀ k, 0 ≤ gamma k` and `jensen_pf : IsPFPolynomial (jensenPolynomial n gamma)`. -/
syntax (name := rr_finite_pf_multiplier_le_two_of_jensen_pf_named)
  "rr_finite_pf_multiplier_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

/-- Closes `IsFinitePFMultiplierSequence 2 gamma` from `sequence_nonneg : ∀ k, 0 ≤ gamma k` and
`jensen_pf : IsPFPolynomial (jensenPolynomial 2 gamma)`. -/
syntax (name := rr_finite_pf_multiplier_degree_two_of_jensen_pf_named)
  "rr_finite_pf_multiplier_degree_two_of_jensen_pf" " using "
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

/-- Sequence form of `rr_finite_multiplier_le_two_of_jensen_pf`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_finite_multiplier_sequence_le_two_of_jensen_pf_named)
  "rr_finite_multiplier_sequence_le_two_of_jensen_pf" " using "
    "degree_le_two" ":=" term ","
    "sequence_nonneg" ":=" term ","
    "jensen_pf" ":=" term :
  tactic

/-- Sequence form of `rr_finite_pf_multiplier_le_two_of_jensen_pf`: the same certificate for every
index `i : Nat`. -/
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
