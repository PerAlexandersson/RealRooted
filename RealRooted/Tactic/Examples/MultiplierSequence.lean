import RealRooted.Tactic.MultiplierSequence

open Polynomial

namespace RealRooted
namespace Tactic

example {gamma : ℕ → ℝ} {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hgamma : ∀ n, 0 ≤ gamma n) :
    HasNonnegCoeffs (diagonalOperator gamma p) := by
  rr_diagonal_nonneg using nonneg := hp, sequence_nonneg := hgamma

example {gamma : ℕ → ℝ} {p : ℝ[X]} :
    (diagonalOperator gamma p).natDegree ≤ p.natDegree := by
  rr_diagonal_natDegree_le

example (gamma : ℕ → ℝ) (p q : ℝ[X]) :
    diagonalOperator gamma (p + q) =
      diagonalOperator gamma p + diagonalOperator gamma q := by
  rr_diagonal_add

example (gamma : ℕ → ℝ) (p q : ℝ[X]) :
    diagonalOperator gamma (p - q) =
      diagonalOperator gamma p - diagonalOperator gamma q := by
  rr_diagonal_sub

example (gamma : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (-p) = -diagonalOperator gamma p := by
  rr_diagonal_neg

example (gamma : ℕ → ℝ) (a : ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (C a * p) =
      C a * diagonalOperator gamma p := by
  rr_diagonal_C_mul

example (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (diagonalOperator delta p) =
      diagonalOperator (fun n => gamma n * delta n) p := by
  rr_diagonal_comp

example (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (diagonalOperator delta p) =
      diagonalOperator delta (diagonalOperator gamma p) := by
  rr_diagonal_comm

example {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hdeg : (diagonalOperator gamma p).natDegree = 3)
    (hdisc : 0 ≤ cubicDiscr (diagonalOperator gamma p)) :
    (diagonalOperator gamma p).Splits := by
  rr_diagonal_splits_cubic using degree := hdeg, discriminant := hdisc

example {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hdeg : (diagonalOperator gamma p).natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (diagonalOperator gamma p)) :
    (diagonalOperator gamma p).Splits := by
  rr_diagonal_splits_le_three using degree_le := hdeg, discriminant := hdisc

example {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    HasNonnegCoeffs (jensenPolynomial n gamma) := by
  rr_jensen_nonneg using sequence_nonneg := hgamma

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ i k, 0 ≤ Gamma i k) :
    ∀ i : Nat, HasNonnegCoeffs (jensenPolynomial (N i) (Gamma i)) := by
  rr_jensen_sequence_nonneg using level := N, sequence_nonneg := hGamma

example {n : ℕ} {gamma : ℕ → ℝ} :
    (jensenPolynomial n gamma).natDegree ≤ n := by
  rr_jensen_natDegree_le

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ} :
    ∀ i : Nat, (jensenPolynomial (N i) (Gamma i)).natDegree ≤ N i := by
  rr_jensen_sequence_natDegree_le using level := N, sequence := Gamma

example {n : ℕ} {gamma : ℕ → ℝ} :
    jensenPolynomial n gamma = 0 ↔ ∀ k, k ≤ n → gamma k = 0 := by
  rr_jensen_zero_iff

example (n : ℕ) (gamma : ℕ → ℝ) :
    jensenPolynomial n gamma = diagonalOperator gamma ((X + 1) ^ n) := by
  rr_jensen_as_diagonal_X_add_one_pow

example (n : ℕ) (gamma delta : ℕ → ℝ) :
    jensenPolynomial n (fun k => gamma k * delta k) =
      diagonalOperator gamma (jensenPolynomial n delta) := by
  rr_jensen_mul_sequence_as_diagonal

example (a b c : ℝ) (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d (fun k => a * (k : ℝ) ^ 2 + b * (k : ℝ) + c) =
      ((X + 1 : ℝ[X]) ^ (d - 2)) *
        (C c * (X + 1) ^ 2 +
          C ((a + b) * (d : ℝ)) * X * (X + 1) +
            C (a * (d : ℝ) * ((d : ℝ) - 1)) * X ^ 2) := by
  rr_jensen_quadratic_sequence_factor using degree_ge_two := hd

example (gamma : ℕ → ℝ) :
    cubicDiscr (jensenPolynomial 3 gamma) =
      27 * (6 * gamma 3 * gamma 2 * gamma 1 * gamma 0
        - 4 * gamma 2 ^ 3 * gamma 0
        + 3 * gamma 2 ^ 2 * gamma 1 ^ 2
        - 4 * gamma 3 * gamma 1 ^ 3
        - gamma 3 ^ 2 * gamma 0 ^ 2) := by
  rr_jensen_cubic_discr

example {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) := by
  rr_jensen_three_discr_nonneg using zero_or_splits := hs

example {gamma : ℕ → ℝ} (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) := by
  rr_jensen_pf_three_discr_nonneg using pf := hj

example {gamma : ℕ → ℝ} :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) ↔
      jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits := by
  rr_jensen_three_discr_iff_zero_or_splits

example {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 := by
  rr_jensen_three_log_concave using zero_or_splits := hs

example {gamma : ℕ → ℝ} (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 := by
  rr_jensen_pf_three_log_concave using pf := hj

example {m n : ℕ} {gamma : ℕ → ℝ} (hmn : m ≤ n)
    (h : IsFiniteMultiplierSequence n gamma) :
    IsFiniteMultiplierSequence m gamma := by
  rr_finite_multiplier_mono using degree_le := hmn, multiplier := h

example {M N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hMN : ∀ i : Nat, M i ≤ N i)
    (h : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFiniteMultiplierSequence (M i) (Gamma i) := by
  rr_finite_multiplier_sequence_mono using degree_le := hMN, multiplier := h

example {m n : ℕ} {gamma : ℕ → ℝ} (hmn : m ≤ n)
    (h : IsFinitePFMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence m gamma := by
  rr_finite_pf_multiplier_mono using degree_le := hmn, pf_multiplier := h

example {M N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hMN : ∀ i : Nat, M i ≤ N i)
    (h : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (M i) (Gamma i) := by
  rr_finite_pf_multiplier_sequence_mono using
    degree_le := hMN,
    pf_multiplier := h

example {n : ℕ} {gamma delta : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence n gamma)
    (hdelta : IsFiniteMultiplierSequence n delta) :
    IsFiniteMultiplierSequence n (fun k => gamma k * delta k) := by
  rr_finite_multiplier_mul using left_multiplier := hgamma, right_multiplier := hdelta

example {N : Nat → ℕ} {Gamma Delta : Nat → ℕ → ℝ}
    (hGamma : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i))
    (hDelta : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Delta i)) :
    ∀ i : Nat, IsFiniteMultiplierSequence (N i)
      (fun k => Gamma i k * Delta i k) := by
  rr_finite_multiplier_sequence_mul using
    left_multiplier := hGamma,
    right_multiplier := hDelta

example {n : ℕ} {gamma delta : ℕ → ℝ}
    (hgamma : IsFinitePFMultiplierSequence n gamma)
    (hdelta : IsFinitePFMultiplierSequence n delta) :
    IsFinitePFMultiplierSequence n (fun k => gamma k * delta k) := by
  rr_finite_pf_multiplier_mul using
    left_pf_multiplier := hgamma,
    right_pf_multiplier := hdelta

example {N : Nat → ℕ} {Gamma Delta : Nat → ℕ → ℝ}
    (hGamma : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i))
    (hDelta : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Delta i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i)
      (fun k => Gamma i k * Delta i k) := by
  rr_finite_pf_multiplier_sequence_mul using
    left_pf_multiplier := hGamma,
    right_pf_multiplier := hDelta

example {n : ℕ} {a : ℝ} :
    IsFiniteMultiplierSequence n (fun _ => a) := by
  rr_finite_multiplier_const

example {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    IsFinitePFMultiplierSequence n (fun _ => a) := by
  rr_finite_pf_multiplier_const using scalar_nonneg := ha

example {n : ℕ} :
    IsFiniteMultiplierSequence n (fun _ => (1 : ℝ)) := by
  rr_finite_multiplier_one

example {n : ℕ} :
    IsFinitePFMultiplierSequence n (fun _ => (1 : ℝ)) := by
  rr_finite_pf_multiplier_one

example {n : ℕ} :
    IsFiniteMultiplierSequence n (fun _ => (0 : ℝ)) := by
  rr_finite_multiplier_zero

example {n : ℕ} :
    IsFinitePFMultiplierSequence n (fun _ => (0 : ℝ)) := by
  rr_finite_pf_multiplier_zero

example {n : ℕ} {gamma : ℕ → ℝ} (hn : n ≤ 1) :
    IsFiniteMultiplierSequence n gamma := by
  rr_finite_multiplier_le_one using degree_le_one := hn

example {gamma : ℕ → ℝ} :
    IsFiniteMultiplierSequence 0 gamma := by
  rr_finite_multiplier_degree_zero

example {gamma : ℕ → ℝ} :
    IsFiniteMultiplierSequence 1 gamma := by
  rr_finite_multiplier_degree_one

example {n : ℕ} {gamma : ℕ → ℝ} (hn : n ≤ 2)
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma := by
  rr_finite_multiplier_le_two_of_jensen_pf using
    degree_le_two := hn,
    sequence_nonneg := hgamma,
    jensen_pf := hjensen

example {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial 2 gamma)) :
    IsFiniteMultiplierSequence 2 gamma := by
  rr_finite_multiplier_degree_two_of_jensen_pf using
    sequence_nonneg := hgamma,
    jensen_pf := hjensen

example {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) := by
  rr_jensen_pf_of_finite_multiplier using sequence_nonneg := hgamma, multiplier := hmult

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i)) := by
  rr_jensen_sequence_pf_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

example {n : ℕ} {gamma : ℕ → ℝ} (hmult : IsFinitePFMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) := by
  rr_jensen_pf_of_finite_pf_multiplier using pf_multiplier := hmult

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hmult : ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i)) := by
  rr_jensen_sequence_pf_of_finite_pf_multiplier using
    level := N,
    pf_multiplier := hmult

example {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 := by
  rr_finite_multiplier_three_log_concave using
    sequence_nonneg := hgamma,
    multiplier := hmult

example {gamma : ℕ → ℝ} (hmult : IsFinitePFMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 := by
  rr_finite_pf_multiplier_three_log_concave using pf_multiplier := hmult

example {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence n gamma := by
  rr_finite_pf_multiplier_of_finite_multiplier using
    sequence_nonneg := hgamma,
    multiplier := hmult

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hmult : ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i)) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i) := by
  rr_finite_pf_multiplier_sequence_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

example {n : ℕ} {gamma : ℕ → ℝ} (hn : n ≤ 1)
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma := by
  rr_finite_pf_multiplier_le_one using
    degree_le_one := hn,
    sequence_nonneg := hgamma

example {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence 0 gamma := by
  rr_finite_pf_multiplier_degree_zero using sequence_nonneg := hgamma

example {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence 1 gamma := by
  rr_finite_pf_multiplier_degree_one using sequence_nonneg := hgamma

example {n : ℕ} {gamma : ℕ → ℝ} (hn : n ≤ 2)
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma := by
  rr_finite_pf_multiplier_le_two_of_jensen_pf using
    degree_le_two := hn,
    sequence_nonneg := hgamma,
    jensen_pf := hjensen

example {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial 2 gamma)) :
    IsFinitePFMultiplierSequence 2 gamma := by
  rr_finite_pf_multiplier_degree_two_of_jensen_pf using
    sequence_nonneg := hgamma,
    jensen_pf := hjensen

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hN : ∀ i : Nat, N i ≤ 2)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hjensen : ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))) :
    ∀ i : Nat, IsFiniteMultiplierSequence (N i) (Gamma i) := by
  rr_finite_multiplier_sequence_le_two_of_jensen_pf using
    degree_le_two := hN,
    sequence_nonneg := hGamma,
    jensen_pf := hjensen

example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hN : ∀ i : Nat, N i ≤ 2)
    (hGamma : ∀ i k, 0 ≤ Gamma i k)
    (hjensen : ∀ i : Nat, IsPFPolynomial (jensenPolynomial (N i) (Gamma i))) :
    ∀ i : Nat, IsFinitePFMultiplierSequence (N i) (Gamma i) := by
  rr_finite_pf_multiplier_sequence_le_two_of_jensen_pf using
    degree_le_two := hN,
    sequence_nonneg := hGamma,
    jensen_pf := hjensen

end Tactic
end RealRooted
