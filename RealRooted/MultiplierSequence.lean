import RealRooted.CoefficientShape
import RealRooted.CubicDiscriminant
import RealRooted.CubicNewton
import RealRooted.PFPolynomial

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Finite multiplier sequences

This file records the finite-degree multiplier-sequence interface needed for
the PF side of the Hadamard/Schur--Szego machinery.  It deliberately stays
independent of `RealRooted.Hadamard`, so work here can proceed while the
Garloff--Wagner theorem file is being edited elsewhere.

The main classical input is the finite Polya--Schur theorem: for nonnegative
diagonal coefficients, preservation of real-rootedness up to degree `n` is
equivalent to the corresponding Jensen polynomial being PF.
-/

/-- Diagonal operator attached to a sequence `gamma`: it sends
`sum a_n X^n` to `sum gamma_n a_n X^n`. -/
def diagonalOperator (gamma : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => monomial n (gamma n * a)

@[simp] theorem coeff_diagonalOperator
    (gamma : ℕ → ℝ) (p : ℝ[X]) (n : ℕ) :
    (diagonalOperator gamma p).coeff n = gamma n * p.coeff n := by
  classical
  rw [diagonalOperator, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  simp_all

@[simp] theorem diagonalOperator_zero (gamma : ℕ → ℝ) :
    diagonalOperator gamma 0 = 0 := by
  ext n
  simp

@[simp] theorem diagonalOperator_zero_sequence (p : ℝ[X]) :
    diagonalOperator (fun _ => (0 : ℝ)) p = 0 := by
  ext n
  simp

@[simp] theorem diagonalOperator_one_sequence (p : ℝ[X]) :
    diagonalOperator (fun _ => (1 : ℝ)) p = p := by
  ext n
  simp

theorem diagonalOperator_const_sequence (a : ℝ) (p : ℝ[X]) :
    diagonalOperator (fun _ ↦ a) p = C a * p := by
  ext n
  simp

theorem diagonalOperator_add (gamma : ℕ → ℝ) (p q : ℝ[X]) :
    diagonalOperator gamma (p + q) =
      diagonalOperator gamma p + diagonalOperator gamma q := by
  ext n
  simp [mul_add]

theorem diagonalOperator_sub (gamma : ℕ → ℝ) (p q : ℝ[X]) :
    diagonalOperator gamma (p - q) =
      diagonalOperator gamma p - diagonalOperator gamma q := by
  ext n
  simp [mul_sub]

theorem diagonalOperator_neg (gamma : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (-p) = -diagonalOperator gamma p := by
  ext n
  simp

theorem diagonalOperator_C_mul (gamma : ℕ → ℝ) (a : ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (C a * p) =
      C a * diagonalOperator gamma p := by
  ext n
  simp [mul_comm, mul_left_comm]

@[simp] theorem diagonalOperator_C (gamma : ℕ → ℝ) (a : ℝ) :
    diagonalOperator gamma (C a) = C (gamma 0 * a) := by
  ext n
  cases n <;> simp

theorem diagonalOperator_monomial (gamma : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    diagonalOperator gamma (monomial n a) = monomial n (gamma n * a) := by
  ext k
  by_cases hk : k = n
  · simp_all
  · simp [Polynomial.coeff_monomial, Ne.symm hk]

theorem support_diagonalOperator_eq_filter (gamma : ℕ → ℝ) (p : ℝ[X]) :
    (diagonalOperator gamma p).support = p.support.filter fun n => gamma n ≠ 0 := by
  ext n
  by_cases hgamma : gamma n = 0
  · simp [Polynomial.mem_support_iff, coeff_diagonalOperator, hgamma]
  · simp [Polynomial.mem_support_iff, coeff_diagonalOperator, hgamma]

theorem support_diagonalOperator_subset (gamma : ℕ → ℝ) (p : ℝ[X]) :
    (diagonalOperator gamma p).support ⊆ p.support :=
  (support_diagonalOperator_eq_filter gamma p).symm ▸ Finset.filter_subset _ _

theorem natDegree_diagonalOperator_le (gamma : ℕ → ℝ) (p : ℝ[X]) :
    (diagonalOperator gamma p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_diagonalOperator, coeff_eq_zero_of_natDegree_lt hn, mul_zero]

theorem diagonalOperator_comp (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (diagonalOperator delta p) =
      diagonalOperator (fun n => gamma n * delta n) p := by
  ext n
  simp [mul_assoc]

theorem diagonalOperator_comm (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (diagonalOperator delta p) =
      diagonalOperator delta (diagonalOperator gamma p) := by
  ext n
  simp [mul_left_comm]

/-- The diagonal operator is additive in the diagonal sequence. -/
theorem diagonalOperator_add_sequence (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator (fun n => gamma n + delta n) p =
      diagonalOperator gamma p + diagonalOperator delta p := by
  ext n
  simp [add_mul]

/-- The diagonal operator is negation-preserving in the diagonal sequence. -/
theorem diagonalOperator_neg_sequence (gamma : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator (fun n => -gamma n) p = -diagonalOperator gamma p := by
  ext n
  simp

/-- The diagonal operator is subtractive in the diagonal sequence. -/
theorem diagonalOperator_sub_sequence (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator (fun n => gamma n - delta n) p =
      diagonalOperator gamma p - diagonalOperator delta p := by
  ext n
  simp [sub_mul]

/-- Nonnegative diagonal coefficients preserve nonnegative coefficients. -/
theorem HasNonnegCoeffs.diagonalOperator
    {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hgamma : ∀ n, 0 ≤ gamma n) :
    HasNonnegCoeffs (diagonalOperator gamma p) := by
  intro n
  simpa using mul_nonneg (hgamma n) (hp n)

/-! ## Cubic discriminant route -/

/-- Coefficient expansion of the cubic discriminant after applying a diagonal
operator.  This is the algebraic target needed for the degree-three finite
Pólya--Schur route. -/
theorem cubicDiscr_diagonalOperator (gamma : ℕ → ℝ) (p : ℝ[X]) :
    cubicDiscr (diagonalOperator gamma p) =
      18 * (gamma 3 * p.coeff 3) * (gamma 2 * p.coeff 2) *
          (gamma 1 * p.coeff 1) * (gamma 0 * p.coeff 0)
        - 4 * (gamma 2 * p.coeff 2) ^ 3 * (gamma 0 * p.coeff 0)
        + (gamma 2 * p.coeff 2) ^ 2 * (gamma 1 * p.coeff 1) ^ 2
        - 4 * (gamma 3 * p.coeff 3) * (gamma 1 * p.coeff 1) ^ 3
        - 27 * (gamma 3 * p.coeff 3) ^ 2 * (gamma 0 * p.coeff 0) ^ 2 := by
  unfold cubicDiscr
  simp only [coeff_diagonalOperator]

/-- Degree-three diagonal-operator output splits once its cubic discriminant is
nonnegative. -/
theorem diagonalOperator_splits_of_natDegree_three_cubicDiscr_nonneg
    {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hdeg : (diagonalOperator gamma p).natDegree = 3)
    (hdisc : 0 ≤ cubicDiscr (diagonalOperator gamma p)) :
    (diagonalOperator gamma p).Splits :=
  splits_of_cubicDiscr_nonneg hdeg hdisc

/-- Degree-at-most-three diagonal-operator output splits once its cubic
discriminant is nonnegative. -/
theorem diagonalOperator_splits_of_natDegree_le_three_cubicDiscr_nonneg
    {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hdeg : (diagonalOperator gamma p).natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (diagonalOperator gamma p)) :
    (diagonalOperator gamma p).Splits :=
  splits_of_natDegree_le_three_cubicDiscr_nonneg hdeg hdisc

/-- The degree-`n` Jensen polynomial attached to a diagonal sequence. -/
def jensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k ((Nat.choose n k : ℝ) * gamma k)

@[simp] theorem jensenPolynomial_zero (gamma : ℕ → ℝ) :
    jensenPolynomial 0 gamma = C (gamma 0) := by
  ext k
  cases k <;> simp [jensenPolynomial]

@[simp] theorem coeff_jensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) (k : ℕ) :
    (jensenPolynomial n gamma).coeff k =
      if k ≤ n then (Nat.choose n k : ℝ) * gamma k else 0 := by
  classical
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := by simp_all
    rw [jensenPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b hb hbk
      simp [Polynomial.coeff_monomial, hbk]
    · simp_all
  · rw [jensenPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hb_le : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hne : k ≠ b := by grind
      have hbk : b ≠ k := Ne.symm hne
      simp [Polynomial.coeff_monomial, hbk]

/-- A polynomial of degree at most `n` is recovered as the Jensen polynomial of
its binomially normalized coefficient sequence. -/
theorem jensenPolynomial_normalized_coeff_eq_of_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    jensenPolynomial n (fun k => p.coeff k / (Nat.choose n k : ℝ)) = p := by
  ext k
  rw [coeff_jensenPolynomial]
  by_cases hk : k ≤ n
  · have hchoose : (Nat.choose n k : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero (R := ℝ) hk
    grind
  · have hklt : n < k := Nat.lt_of_not_le hk
    have hpcoeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hklt)
    simp [hk, hpcoeff]

/-- A PF polynomial of degree at most `n`, rebuilt as the Jensen polynomial of
its binomially normalized coefficient sequence, is PF. -/
theorem IsPFPolynomial.jensenPolynomial_normalized_coeff_of_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial
      (jensenPolynomial n (fun k => p.coeff k / (Nat.choose n k : ℝ))) :=
  (jensenPolynomial_normalized_coeff_eq_of_natDegree_le hpdeg).symm ▸ hp

/-- The Jensen polynomial of `gamma` is the image of `(X + 1) ^ n` under the
diagonal operator attached to `gamma`. -/
theorem jensenPolynomial_eq_diagonalOperator_X_add_one_pow
    (n : ℕ) (gamma : ℕ → ℝ) :
    jensenPolynomial n gamma = diagonalOperator gamma ((X + 1) ^ n) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_diagonalOperator, coeff_X_add_one_pow]
  by_cases hk : k ≤ n
  · grind
  · have hlt : n < k := Nat.lt_of_not_le hk
    simp [hk, Nat.choose_eq_zero_of_lt hlt]

/-- Multiplying two diagonal sequences inside a Jensen polynomial is the same
as applying one sequence as a diagonal operator to the Jensen polynomial of the
other sequence. -/
theorem jensenPolynomial_mul_sequence_eq_diagonalOperator
    (n : ℕ) (gamma delta : ℕ → ℝ) :
    jensenPolynomial n (fun k => gamma k * delta k) =
      diagonalOperator gamma (jensenPolynomial n delta) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_diagonalOperator, coeff_jensenPolynomial]
  grind

/-- The Jensen polynomial of a constant diagonal sequence. -/
theorem jensenPolynomial_const_sequence (n : ℕ) (a : ℝ) :
    jensenPolynomial n (fun _ => a) = C a * ((X + 1 : ℝ[X]) ^ n) :=
  (jensenPolynomial_eq_diagonalOperator_X_add_one_pow n (fun _ => a)).trans
    (diagonalOperator_const_sequence a ((X + 1 : ℝ[X]) ^ n))

/-- The Jensen polynomial is additive in the diagonal sequence. -/
theorem jensenPolynomial_add_sequence (n : ℕ) (gamma delta : ℕ → ℝ) :
    jensenPolynomial n (fun k => gamma k + delta k) =
      jensenPolynomial n gamma + jensenPolynomial n delta := by
  simpa [jensenPolynomial_eq_diagonalOperator_X_add_one_pow] using
    diagonalOperator_add_sequence gamma delta ((X + 1 : ℝ[X]) ^ n)

/-- The Jensen polynomial is negation-preserving in the diagonal sequence. -/
theorem jensenPolynomial_neg_sequence (n : ℕ) (gamma : ℕ → ℝ) :
    jensenPolynomial n (fun k => -gamma k) = -jensenPolynomial n gamma := by
  simpa [jensenPolynomial_eq_diagonalOperator_X_add_one_pow] using
    diagonalOperator_neg_sequence gamma ((X + 1 : ℝ[X]) ^ n)

/-- The Jensen polynomial is subtractive in the diagonal sequence. -/
theorem jensenPolynomial_sub_sequence (n : ℕ) (gamma delta : ℕ → ℝ) :
    jensenPolynomial n (fun k => gamma k - delta k) =
      jensenPolynomial n gamma - jensenPolynomial n delta := by
  simpa [jensenPolynomial_eq_diagonalOperator_X_add_one_pow] using
    diagonalOperator_sub_sequence gamma delta ((X + 1 : ℝ[X]) ^ n)

theorem hasNonnegCoeffs_jensenPolynomial
    {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    HasNonnegCoeffs (jensenPolynomial n gamma) :=
  (jensenPolynomial_eq_diagonalOperator_X_add_one_pow n gamma).symm ▸
    (hasNonnegCoeffs_X_add_one.pow n).diagonalOperator hgamma

theorem natDegree_jensenPolynomial_le (n : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial n gamma).natDegree ≤ n :=
  (jensenPolynomial_eq_diagonalOperator_X_add_one_pow n gamma).symm ▸
    (natDegree_diagonalOperator_le _ _).trans (natDegree_X_add_one_pow_le n)

theorem support_jensenPolynomial_eq_filter (n : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial n gamma).support =
      (Finset.range (n + 1)).filter fun k => gamma k ≠ 0 := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
    support_diagonalOperator_eq_filter, support_X_add_one_pow_eq_range]

theorem support_jensenPolynomial_subset (n : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial n gamma).support ⊆ Finset.range (n + 1) :=
  (support_jensenPolynomial_eq_filter n gamma).symm ▸ Finset.filter_subset _ _

theorem jensenPolynomial_eq_zero_iff {n : ℕ} {gamma : ℕ → ℝ} :
    jensenPolynomial n gamma = 0 ↔ ∀ k, k ≤ n → gamma k = 0 := by
  rw [← support_eq_empty, support_jensenPolynomial_eq_filter, Finset.filter_eq_empty_iff]
  simp [Finset.mem_range]

@[simp] theorem jensenPolynomial_zero_sequence (n : ℕ) :
    jensenPolynomial n (fun _ => (0 : ℝ)) = 0 := by
  simpa using jensenPolynomial_const_sequence n (0 : ℝ)

@[simp] theorem jensenPolynomial_one_sequence (n : ℕ) :
    jensenPolynomial n (fun _ => (1 : ℝ)) = (X + 1 : ℝ[X]) ^ n := by
  simpa using jensenPolynomial_const_sequence n (1 : ℝ)

/-- The Euler operator `X d/dX` acts diagonally with multiplier `k`. -/
theorem eulerOperator_eq_diagonalOperator_natCast (p : ℝ[X]) :
    X * derivative p = diagonalOperator (fun k => (k : ℝ)) p := by
  ext k
  cases k with
  | zero => simp [coeff_diagonalOperator]
  | succ k =>
      simp [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, coeff_diagonalOperator]
      ring

/-- The diagonal operator with multiplier `k^2` is the square of the Euler
operator. -/
theorem diagonalOperator_natCast_sq_eq_euler_sq (p : ℝ[X]) :
    diagonalOperator (fun k => (k : ℝ) ^ 2) p =
      X * derivative (X * derivative p) := by
  rw [eulerOperator_eq_diagonalOperator_natCast p]
  rw [eulerOperator_eq_diagonalOperator_natCast
    (diagonalOperator (fun k => (k : ℝ)) p)]
  ext k
  simp [coeff_diagonalOperator]
  ring

/-- The diagonal operator is linear in a quadratic multiplier. -/
theorem diagonalOperator_quadratic_sequence
    (a b c : ℝ) (p : ℝ[X]) :
    diagonalOperator (fun k => a * (k : ℝ) ^ 2 + b * (k : ℝ) + c) p =
      C a * diagonalOperator (fun k => (k : ℝ) ^ 2) p +
        C b * diagonalOperator (fun k => (k : ℝ)) p + C c * p := by
  ext k
  simp [coeff_diagonalOperator]
  ring

/-- Jensen factorization for a quadratic multiplier.

For `d >= 2`, the Jensen polynomial of the sequence `a k^2 + b k + c` has
the common factor `(1 + X)^(d - 2)` and a residual quadratic. -/
theorem jensenPolynomial_quadratic_sequence_factor
    (a b c : ℝ) (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d (fun k => a * (k : ℝ) ^ 2 + b * (k : ℝ) + c) =
      ((X + 1 : ℝ[X]) ^ (d - 2)) *
        (C c * (X + 1) ^ 2 +
          C ((a + b) * (d : ℝ)) * X * (X + 1) +
            C (a * (d : ℝ) * ((d : ℝ) - 1)) * X ^ 2) := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  rw [diagonalOperator_quadratic_sequence]
  rw [diagonalOperator_natCast_sq_eq_euler_sq]
  rw [← eulerOperator_eq_diagonalOperator_natCast]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_natCast, Polynomial.C_add, Polynomial.C_mul,
    Polynomial.C_eq_natCast, one_mul, mul_one, add_zero]
  have hd1 : d - 1 = d - 2 + 1 := by lia
  have hd11 : d - 1 - 1 = d - 2 := by lia
  rw [hd11, hd1]
  have hcast :
      ((d - 2 + 1 : ℕ) : ℝ[X]) = (d : ℝ[X]) - 1 := by
    have hnat : d - 2 + 1 = d - 1 := by lia
    rw [hnat]
    norm_num [Nat.cast_sub (by lia : 1 ≤ d)]
  have hpow :
      (X + 1 : ℝ[X]) ^ d =
        (X + 1 : ℝ[X]) ^ (d - 2) * (X + 1) ^ 2 := by
    simpa [Nat.sub_add_cancel hd] using
      (pow_add (X + 1 : ℝ[X]) (d - 2) 2)
  rw [hpow]
  rw [pow_add]
  rw [hcast]
  norm_num [Polynomial.C_eq_natCast]
  ring_nf

/-- Explicit cubic discriminant of the degree-three Jensen polynomial.

This is the coefficient-normalized algebraic target for the degree-three
finite Pólya--Schur route. -/
theorem cubicDiscr_jensenPolynomial_three (gamma : ℕ → ℝ) :
    cubicDiscr (jensenPolynomial 3 gamma) =
      27 * (6 * gamma 3 * gamma 2 * gamma 1 * gamma 0
        - 4 * gamma 2 ^ 3 * gamma 0
        + 3 * gamma 2 ^ 2 * gamma 1 ^ 2
        - 4 * gamma 3 * gamma 1 ^ 3
        - gamma 3 ^ 2 * gamma 0 ^ 2) := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
    cubicDiscr_diagonalOperator]
  norm_num [coeff_X_add_one_pow]
  ring

/-- A degree-three Jensen polynomial that is zero or splits has nonnegative
cubic discriminant. -/
theorem cubicDiscr_jensenPolynomial_three_nonneg_of_eq_zero_or_splits
    {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) := by
  rcases hs with hzero | hsplit
  · simp [hzero, cubicDiscr]
  · exact
      cubicDiscr_nonneg_of_splits_natDegree_le_three
        (natDegree_jensenPolynomial_le 3 gamma) hsplit

/-- A PF degree-three Jensen polynomial has nonnegative cubic discriminant. -/
theorem IsPFPolynomial.cubicDiscr_jensenPolynomial_three_nonneg
    {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) :=
  cubicDiscr_jensenPolynomial_three_nonneg_of_eq_zero_or_splits
    hj.eq_zero_or_splits

/-- For degree-three Jensen polynomials, nonnegative cubic discriminant is
equivalent to being zero or splitting. -/
theorem cubicDiscr_jensenPolynomial_three_nonneg_iff_eq_zero_or_splits
    {gamma : ℕ → ℝ} :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) ↔
      jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits :=
  ⟨fun hdisc =>
      Or.inr <|
        splits_of_natDegree_le_three_cubicDiscr_nonneg
          (natDegree_jensenPolynomial_le 3 gamma) hdisc,
    cubicDiscr_jensenPolynomial_three_nonneg_of_eq_zero_or_splits⟩

/-- Finite multiplier sequence up to degree `n`: the diagonal operator
preserves real-rootedness, allowing the zero polynomial. -/
def IsFiniteMultiplierSequence (n : ℕ) (gamma : ℕ → ℝ) : Prop :=
  ∀ {p : ℝ[X]},
    p.natDegree ≤ n →
    p.Splits →
    diagonalOperator gamma p = 0 ∨ (diagonalOperator gamma p).Splits

/-- Finite PF multiplier sequence up to degree `n`: the diagonal operator
preserves the polynomial PF cone on polynomials of degree at most `n`. -/
def IsFinitePFMultiplierSequence (n : ℕ) (gamma : ℕ → ℝ) : Prop :=
  ∀ {p : ℝ[X]},
    IsPFPolynomial p →
    p.natDegree ≤ n →
    IsPFPolynomial (diagonalOperator gamma p)

theorem IsFiniteMultiplierSequence.mono {m n : ℕ} {gamma : ℕ → ℝ}
    (hmn : m ≤ n) (h : IsFiniteMultiplierSequence n gamma) :
    IsFiniteMultiplierSequence m gamma :=
  fun {_} hp hsplit => h (hp.trans hmn) hsplit

theorem IsFinitePFMultiplierSequence.mono {m n : ℕ} {gamma : ℕ → ℝ}
    (hmn : m ≤ n) (h : IsFinitePFMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence m gamma :=
  fun {_} hp hdeg => h hp (hdeg.trans hmn)

theorem IsFiniteMultiplierSequence.mul {n : ℕ} {gamma delta : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence n gamma)
    (hdelta : IsFiniteMultiplierSequence n delta) :
    IsFiniteMultiplierSequence n (fun k => gamma k * delta k) := by
  intro p hp hsplit
  rw [← diagonalOperator_comp]
  rcases hdelta hp hsplit with hzero | hsplit_delta
  · simp_all
  · exact hgamma ((natDegree_diagonalOperator_le delta p).trans hp) hsplit_delta

theorem IsFinitePFMultiplierSequence.mul {n : ℕ} {gamma delta : ℕ → ℝ}
    (hgamma : IsFinitePFMultiplierSequence n gamma)
    (hdelta : IsFinitePFMultiplierSequence n delta) :
    IsFinitePFMultiplierSequence n (fun k => gamma k * delta k) := by
  intro p hp hdeg
  rw [← diagonalOperator_comp]
  exact hgamma (hdelta hp hdeg) ((natDegree_diagonalOperator_le delta p).trans hdeg)

theorem isFiniteMultiplierSequence_const_sequence (n : ℕ) (a : ℝ) :
    IsFiniteMultiplierSequence n (fun _ => a) := by
  intro p _ hsplit
  by_cases ha : a = 0
  · simp_all
  by_cases hp0 : p = 0
  · simp_all
  · rw [diagonalOperator_const_sequence]
    simp_all

theorem isFinitePFMultiplierSequence_const_sequence
    {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    IsFinitePFMultiplierSequence n (fun _ => a) := by
  intro p hp _
  by_cases ha0 : a = 0
  · simpa [diagonalOperator_const_sequence, ha0] using IsPFPolynomial.zero
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simpa [diagonalOperator_const_sequence] using hp.const_mul ha_pos

theorem isFiniteMultiplierSequence_one_sequence (n : ℕ) :
    IsFiniteMultiplierSequence n (fun _ => (1 : ℝ)) :=
  isFiniteMultiplierSequence_const_sequence n (1 : ℝ)

theorem isFinitePFMultiplierSequence_one_sequence (n : ℕ) :
    IsFinitePFMultiplierSequence n (fun _ => (1 : ℝ)) :=
  isFinitePFMultiplierSequence_const_sequence (n := n) (a := 1) zero_le_one

theorem isFiniteMultiplierSequence_zero_sequence (n : ℕ) :
    IsFiniteMultiplierSequence n (fun _ => (0 : ℝ)) :=
  isFiniteMultiplierSequence_const_sequence n (0 : ℝ)

theorem isFinitePFMultiplierSequence_zero_sequence (n : ℕ) :
    IsFinitePFMultiplierSequence n (fun _ => (0 : ℝ)) :=
  isFinitePFMultiplierSequence_const_sequence (n := n) (a := 0) le_rfl

/-- In degrees at most one, every diagonal sequence is a finite multiplier
sequence: after applying the diagonal operator, the output is either zero or a
nonzero polynomial of degree at most one, hence split over `ℝ`. -/
theorem isFiniteMultiplierSequence_of_natDegree_le_one
    {n : ℕ} (hn : n ≤ 1) (gamma : ℕ → ℝ) :
    IsFiniteMultiplierSequence n gamma := by
  intro p hp _
  by_cases hzero : diagonalOperator gamma p = 0
  · simp_all
  · exact Or.inr <|
      (isRealRooted_of_natDegree_le_one hzero
        ((natDegree_diagonalOperator_le gamma p).trans (hp.trans hn))).2

/-- Degree-zero finite multiplier sequences are automatic. -/
theorem isFiniteMultiplierSequence_natDegree_zero (gamma : ℕ → ℝ) :
    IsFiniteMultiplierSequence 0 gamma :=
  isFiniteMultiplierSequence_of_natDegree_le_one (by norm_num) gamma

/-- Degree-one finite multiplier sequences are automatic. -/
theorem isFiniteMultiplierSequence_natDegree_one (gamma : ℕ → ℝ) :
    IsFiniteMultiplierSequence 1 gamma :=
  isFiniteMultiplierSequence_of_natDegree_le_one le_rfl gamma

/-- The degree-two Jensen PF hypothesis gives the expected log-concavity
inequality on the first three diagonal entries. -/
theorem IsPFPolynomial.jensenPolynomial_two_logConcave {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 2 gamma)) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 := by
  have hdisc := disc_nonneg_of_isPolyaFreqSeq_natDegree_le_two
    (p := jensenPolynomial 2 gamma) hj.to_sequence
    (natDegree_jensenPolynomial_le 2 gamma)
  simp [coeff_jensenPolynomial] at hdisc
  nlinarith

private lemma gamma_eq_zero_of_natDegree_jensen_lt {n : ℕ} {gamma : ℕ → ℝ}
    {k : ℕ} (hk : k ≤ n) (hdeg : (jensenPolynomial n gamma).natDegree < k) :
    gamma k = 0 := by
  have hcoeff : (jensenPolynomial n gamma).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt hdeg
  rw [coeff_jensenPolynomial] at hcoeff
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero (R := ℝ) hk
  simp_all

/-- Left adjacent log-concavity inequality extracted from a degree-three PF
Jensen polynomial. -/
theorem IsPFPolynomial.jensenPolynomial_three_logConcave_left {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 := by
  by_cases hdeg : (jensenPolynomial 3 gamma).natDegree < 2
  · have hgamma2 : gamma 2 = 0 :=
      gamma_eq_zero_of_natDegree_jensen_lt (n := 3) (gamma := gamma)
        (k := 2) (by norm_num) hdeg
    rw [hgamma2]
    nlinarith [sq_nonneg (gamma 1)]
  · have hdeg' : 1 < (jensenPolynomial 3 gamma).natDegree := by lia
    have hdeg_le : (jensenPolynomial 3 gamma).natDegree ≤ 3 :=
      natDegree_jensenPolynomial_le 3 gamma
    have hdeg_ge : 2 ≤ (jensenPolynomial 3 gamma).natDegree := by lia
    have hulc :=
      hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
        hj.hasNonnegCoeffs hj.eq_zero_or_splits
    rcases Nat.eq_or_lt_of_le hdeg_ge with hdeg_two' | hdeg_gt
    · have hdeg_two : (jensenPolynomial 3 gamma).natDegree = 2 := hdeg_two'.symm
      have h := hulc 1 (by norm_num) (by grind)
      rw [hdeg_two] at h
      norm_num [coeff_jensenPolynomial] at h
      nlinarith
    · have hdeg_three : (jensenPolynomial 3 gamma).natDegree = 3 := by lia
      have h := hulc 1 (by norm_num) hdeg'
      rw [hdeg_three] at h
      norm_num [coeff_jensenPolynomial] at h
      nlinarith

/-- Right adjacent log-concavity inequality extracted from a degree-three PF
Jensen polynomial. -/
theorem IsPFPolynomial.jensenPolynomial_three_logConcave_right {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    gamma 1 * gamma 3 ≤ gamma 2 ^ 2 := by
  by_cases hdeg : (jensenPolynomial 3 gamma).natDegree < 3
  · have hgamma3 : gamma 3 = 0 :=
      gamma_eq_zero_of_natDegree_jensen_lt (n := 3) (gamma := gamma)
        (k := 3) (by norm_num) hdeg
    rw [hgamma3]
    nlinarith [sq_nonneg (gamma 2)]
  · have hdeg' : 2 < (jensenPolynomial 3 gamma).natDegree := by lia
    have hdeg_le : (jensenPolynomial 3 gamma).natDegree ≤ 3 :=
      natDegree_jensenPolynomial_le 3 gamma
    have hdeg_three : (jensenPolynomial 3 gamma).natDegree = 3 := by lia
    have hulc :=
      hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits
        hj.hasNonnegCoeffs hj.eq_zero_or_splits
    have h := hulc 2 (by norm_num) hdeg'
    rw [hdeg_three] at h
    norm_num [coeff_jensenPolynomial] at h
    nlinarith

/-- Adjacent log-concavity inequalities extracted from a degree-three PF
Jensen polynomial. -/
theorem IsPFPolynomial.jensenPolynomial_three_logConcave {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  ⟨hj.jensenPolynomial_three_logConcave_left,
    hj.jensenPolynomial_three_logConcave_right⟩

/-- Adjacent log-concavity inequalities for a Jensen cubic that is zero or
splits.  This degree-`≤ 3` form packages the degenerate cases with the exact
cubic Newton inequalities. -/
theorem jensenPolynomial_three_logConcave_of_eq_zero_or_splits
    {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  jensen_three_logConcave_of_natDegree_le_three
    (natDegree_jensenPolynomial_le 3 gamma) hs
    (by simp)
    (by simp)
    (by simp)
    (by simp)

/-- Adjacent log-concavity inequalities for a splitting Jensen cubic of exact
degree three.  This is the coefficient form of the two cubic Newton
inequalities after the binomial factors in `jensenPolynomial 3 gamma` cancel. -/
theorem jensenPolynomial_three_logConcave_of_splits_natDegree_three
    {gamma : ℕ → ℝ}
    (_hdeg : (jensenPolynomial 3 gamma).natDegree = 3)
    (hs : (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  jensenPolynomial_three_logConcave_of_eq_zero_or_splits (Or.inr hs)

/-- A splitting real quadratic has nonnegative discriminant, expressed in
coefficient form. -/
theorem four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_natDegree_two
    {p : ℝ[X]} (hdeg : p.natDegree = 2) (hs : p.Splits) :
    4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 :=
  quadratic_disc_coeff_le_of_splits_natDegree_two hdeg hs

private theorem diagonalOperator_discrim_nonneg_of_natDegree_two
    {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hgamma0 : 0 ≤ gamma 0) (hgamma2 : 0 ≤ gamma 2)
    (hlog : gamma 0 * gamma 2 ≤ gamma 1 ^ 2)
    (hpdisc : 4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2) :
    0 ≤ discrim ((diagonalOperator gamma p).coeff 2)
      ((diagonalOperator gamma p).coeff 1) ((diagonalOperator gamma p).coeff 0) := by
  rw [coeff_diagonalOperator, coeff_diagonalOperator, coeff_diagonalOperator]
  unfold discrim
  ring_nf
  by_cases hprod : 0 ≤ p.coeff 0 * p.coeff 2
  · nlinarith [hlog, hpdisc, hprod, sq_nonneg (gamma 1), sq_nonneg (p.coeff 1)]
  · have hp_nonpos : p.coeff 0 * p.coeff 2 ≤ 0 := le_of_lt (not_le.mp hprod)
    have hgamma_nonneg : 0 ≤ gamma 0 * gamma 2 := mul_nonneg hgamma0 hgamma2
    have hmul_nonpos : (gamma 0 * gamma 2) * (p.coeff 0 * p.coeff 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hgamma_nonneg hp_nonpos
    nlinarith [hmul_nonpos, sq_nonneg (gamma 1 * p.coeff 1)]

/-- Degree at most two case of the backward finite Pólya--Schur direction.

The proof is the classical discriminant argument: the PF Jensen polynomial
gives `gamma 0 * gamma 2 ≤ gamma 1 ^ 2`, while a split quadratic input gives
the corresponding discriminant inequality for its coefficients. -/
theorem isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma := by
  intro p hp hsplit
  by_cases hn1 : n ≤ 1
  · exact isFiniteMultiplierSequence_of_natDegree_le_one hn1 gamma hp hsplit
  have hn_eq : n = 2 := by
    lia
  subst n
  by_cases hzero : diagonalOperator gamma p = 0
  · simp_all
  by_cases hq_le_one : (diagonalOperator gamma p).natDegree ≤ 1
  · exact Or.inr ((isRealRooted_of_natDegree_le_one hzero hq_le_one).2)
  have hpdeg : p.natDegree = 2 := by
    have hq_le_p := natDegree_diagonalOperator_le gamma p
    lia
  have hqdeg : (diagonalOperator gamma p).natDegree = 2 := by
    have hq_le_two := (natDegree_diagonalOperator_le gamma p).trans hp
    lia
  have hlog := hjensen.jensenPolynomial_two_logConcave
  have hpdisc :=
    four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_natDegree_two
      hpdeg hsplit
  have hqdisc := diagonalOperator_discrim_nonneg_of_natDegree_two
    (hgamma 0) (hgamma 2) hlog hpdisc
  have hqcoeff2 : (diagonalOperator gamma p).coeff 2 ≠ 0 := by
    have hlc : (diagonalOperator gamma p).leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr hzero
    rwa [Polynomial.leadingCoeff, hqdeg] at hlc
  have hqdisc' : 0 ≤ (diagonalOperator gamma p).coeff 1 ^ 2 -
      4 * (diagonalOperator gamma p).coeff 2 * (diagonalOperator gamma p).coeff 0 := by
    simpa [discrim] using hqdisc
  obtain ⟨x, hx⟩ := exists_root_of_disc_nonneg
    (a := (diagonalOperator gamma p).coeff 2)
    (b := (diagonalOperator gamma p).coeff 1)
    (c := (diagonalOperator gamma p).coeff 0) hqcoeff2 hqdisc'
  have hroot : (diagonalOperator gamma p).IsRoot x := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range, hqdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    grind
  exact Or.inr (Polynomial.Splits.of_natDegree_eq_two hqdeg hroot)

/-- Degree-two finite multiplier sequences are classified by the PF Jensen
polynomial condition. -/
theorem isFiniteMultiplierSequence_natDegree_two_of_isPF_jensenPolynomial
    {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial 2 gamma)) :
    IsFiniteMultiplierSequence 2 gamma :=
  isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    le_rfl hgamma hjensen

theorem splits_X_add_one_pow (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).Splits :=
  (show (X + 1 : ℝ[X]).Splits by
    simpa [sub_eq_add_neg] using (isRealRooted_X_sub_C (-1)).2).pow n

/-- The easy direction of finite Polya--Schur: a nonnegative finite multiplier
sequence has a PF Jensen polynomial. -/
theorem isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) := by
  have hd := hmult (natDegree_X_add_one_pow_le n) (splits_X_add_one_pow n)
  rw [← jensenPolynomial_eq_diagonalOperator_X_add_one_pow] at hd
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hasNonnegCoeffs_jensenPolynomial hgamma) hd

/-- The easy PF direction: a finite PF multiplier sequence has a PF Jensen
polynomial. -/
theorem isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
    {n : ℕ} {gamma : ℕ → ℝ}
    (hmult : IsFinitePFMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) :=
  (jensenPolynomial_eq_diagonalOperator_X_add_one_pow n gamma).symm ▸
    hmult (isPFPolynomial_X_add_one.pow n) (natDegree_X_add_one_pow_le n)

/-- A nonnegative finite multiplier sequence through degree three satisfies
the two adjacent cubic log-concavity inequalities. -/
theorem finiteMultiplierSequence_three_logConcave
    {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  (isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
    hgamma hmult).jensenPolynomial_three_logConcave

/-- A finite PF multiplier sequence through degree three satisfies the two
adjacent cubic log-concavity inequalities. -/
theorem finitePFMultiplierSequence_three_logConcave
    {gamma : ℕ → ℝ}
    (hmult : IsFinitePFMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  (isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
    hmult).jensenPolynomial_three_logConcave

/-- The finite Polya--Schur theorem in the nonnegative-coefficient convention:
a nonnegative diagonal sequence preserves real-rootedness up to degree `n` if
and only if its degree-`n` Jensen polynomial is PF. -/
def finitePolyaSchurNonnegStatement : Prop :=
  ∀ {n : ℕ} {gamma : ℕ → ℝ},
    (∀ k, 0 ≤ gamma k) →
      (IsFiniteMultiplierSequence n gamma ↔
        IsPFPolynomial (jensenPolynomial n gamma))

/-- The remaining hard direction of the finite Polya--Schur theorem. -/
def finitePolyaSchurNonnegBackwardStatement : Prop :=
  ∀ {n : ℕ} {gamma : ℕ → ℝ},
    (∀ k, 0 ≤ gamma k) →
      IsPFPolynomial (jensenPolynomial n gamma) →
        IsFiniteMultiplierSequence n gamma

/-- Low-degree base case of the backward finite Pólya--Schur direction.

For `n ≤ 1`, the Jensen-polynomial hypothesis is unnecessary: diagonal
operators preserve real-rootedness up to degree one for purely degree reasons. -/
theorem finitePolyaSchurNonnegBackward_of_natDegree_le_one
    {n : ℕ} (hn : n ≤ 1) {gamma : ℕ → ℝ}
    (_hgamma : ∀ k, 0 ≤ gamma k)
    (_hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_natDegree_le_one hn gamma

/-- Degree-zero case of the backward finite Pólya--Schur direction. -/
theorem finitePolyaSchurNonnegBackward_natDegree_zero
    {gamma : ℕ → ℝ}
    (_hgamma : ∀ k, 0 ≤ gamma k)
    (_hjensen : IsPFPolynomial (jensenPolynomial 0 gamma)) :
    IsFiniteMultiplierSequence 0 gamma :=
  isFiniteMultiplierSequence_natDegree_zero gamma

/-- Degree-one case of the backward finite Pólya--Schur direction. -/
theorem finitePolyaSchurNonnegBackward_natDegree_one
    {gamma : ℕ → ℝ}
    (_hgamma : ∀ k, 0 ≤ gamma k)
    (_hjensen : IsPFPolynomial (jensenPolynomial 1 gamma)) :
    IsFiniteMultiplierSequence 1 gamma :=
  isFiniteMultiplierSequence_natDegree_one gamma

/-- Degree at most two case of the backward finite Pólya--Schur direction. -/
theorem finitePolyaSchurNonnegBackward_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    hn hgamma hjensen

/-- Degree-two case of the backward finite Pólya--Schur direction. -/
theorem finitePolyaSchurNonnegBackward_natDegree_two
    {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial 2 gamma)) :
    IsFiniteMultiplierSequence 2 gamma :=
  finitePolyaSchurNonnegBackward_of_natDegree_le_two le_rfl hgamma hjensen

/-- Degree at most two case of the full finite Pólya--Schur classification.

The forward implication is elementary; the reverse implication is the checked
low-degree backward theorem. -/
theorem finitePolyaSchur_nonneg_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    finitePolyaSchurNonnegBackward_of_natDegree_le_two hn hgamma⟩

/-- Degree-two case of the full finite Pólya--Schur classification. -/
theorem finitePolyaSchur_nonneg_natDegree_two
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFiniteMultiplierSequence 2 gamma ↔
      IsPFPolynomial (jensenPolynomial 2 gamma) :=
  finitePolyaSchur_nonneg_of_natDegree_le_two le_rfl hgamma

theorem finitePolyaSchur_nonneg_of_backward
    (hBack : finitePolyaSchurNonnegBackwardStatement) :
    finitePolyaSchurNonnegStatement :=
  fun hgamma => ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    hBack hgamma⟩

/-- The full finite Pólya--Schur statement contains, in particular, the hard
backward direction from PF Jensen polynomial to finite multiplier sequence. -/
theorem finitePolyaSchur_backward_of_nonneg
    (hFPS : finitePolyaSchurNonnegStatement) :
    finitePolyaSchurNonnegBackwardStatement :=
  fun hgamma hjensen => (hFPS hgamma).2 hjensen

/-- In the nonnegative-coefficient convention, the full finite Pólya--Schur
statement is equivalent to its backward direction.  The forward direction is
the elementary Jensen-polynomial test on `(X + 1)^n`. -/
theorem finitePolyaSchurNonnegStatement_iff_backward :
    finitePolyaSchurNonnegStatement ↔ finitePolyaSchurNonnegBackwardStatement :=
  ⟨finitePolyaSchur_backward_of_nonneg, finitePolyaSchur_nonneg_of_backward⟩

/- The classical finite Pólya--Schur theorem `finitePolyaSchur_nonneg` is
established in `RealRooted.Hadamard`, where the Schur--Szegő composition
machinery (`finiteSchurSzegoComposition`) needed for the backward direction
`finitePolyaSchurNonnegBackwardStatement` is available. -/

/-- A nonnegative finite multiplier sequence preserves the PF cone on the same
degree range. -/
theorem isFinitePFMultiplierSequence_of_finiteMultiplierSequence
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence n gamma := by
  intro p hp hdeg
  by_cases hp0 : p = 0
  · simp_all
  have hsplit := hmult hdeg (hp.ne_zero_and_splits hp0).2
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hp.hasNonnegCoeffs.diagonalOperator hgamma) hsplit

/-- In degrees at most one, every nonnegative diagonal sequence preserves the
PF cone: finite multiplier preservation is automatic in this range. -/
theorem isFinitePFMultiplierSequence_of_natDegree_le_one
    {n : ℕ} (hn : n ≤ 1) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_natDegree_le_one hn gamma)

/-- Degree-zero finite PF multiplier sequences are automatic for nonnegative
diagonal sequences. -/
theorem isFinitePFMultiplierSequence_natDegree_zero
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence 0 gamma :=
  isFinitePFMultiplierSequence_of_natDegree_le_one (by norm_num) hgamma

/-- Degree-one finite PF multiplier sequences are automatic for nonnegative
diagonal sequences. -/
theorem isFinitePFMultiplierSequence_natDegree_one
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence 1 gamma :=
  isFinitePFMultiplierSequence_of_natDegree_le_one le_rfl hgamma

/-- Degree at most two PF-preservation case of the backward finite
Pólya--Schur direction. -/
theorem isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
      hn hgamma hjensen)

/-- Degree-two finite PF multiplier sequences are classified by the PF Jensen
polynomial condition. -/
theorem isFinitePFMultiplierSequence_natDegree_two_of_isPF_jensenPolynomial
    {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial 2 gamma)) :
    IsFinitePFMultiplierSequence 2 gamma :=
  isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
    le_rfl hgamma hjensen

/-- Degree at most two PF-preservation form of finite Pólya--Schur. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence,
    isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two
      hn hgamma⟩

/-- Degree-two PF-preservation form of finite Pólya--Schur. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial_natDegree_two
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence 2 gamma ↔
      IsPFPolynomial (jensenPolynomial 2 gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_natDegree_le_two
    le_rfl hgamma

/-- The finite Polya--Schur classification, used in the forward direction. -/
theorem jensenPolynomial_isPF_of_finiteMultiplierSequence
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) :=
  (hFPS hgamma).1 hmult

/-- The finite Polya--Schur classification, used in the reverse direction. -/
theorem isFiniteMultiplierSequence_of_jensenPolynomial
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  (hFPS hgamma).2 hjensen

/-- The backward finite Pólya--Schur direction, used directly as a multiplier
sequence criterion. -/
theorem isFiniteMultiplierSequence_of_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurNonnegBackwardStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  hBack hgamma hjensen

/-- PF preservation obtained from the finite Polya--Schur classification and a
PF Jensen polynomial. -/
theorem isFinitePFMultiplierSequence_of_jensenPolynomial
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_jensenPolynomial hFPS hgamma hjensen)

/-- PF preservation obtained from the backward finite Pólya--Schur direction
and a PF Jensen polynomial. -/
theorem isFinitePFMultiplierSequence_of_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurNonnegBackwardStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_jensenPolynomial_of_backward hBack hgamma hjensen)

/-- PF-preservation form of finite Pólya--Schur: for a nonnegative diagonal
sequence, preserving the PF cone up to degree `n` is equivalent to the degree
`n` Jensen polynomial being PF. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence,
    isFinitePFMultiplierSequence_of_jensenPolynomial hFPS hgamma⟩

/-- PF finite multiplier sequences are classified by the Jensen polynomial
once the backward finite Pólya--Schur direction is available. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurNonnegBackwardStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence,
    isFinitePFMultiplierSequence_of_jensenPolynomial_of_backward hBack hgamma⟩

end RealRooted
