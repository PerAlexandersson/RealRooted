import RealRooted.PFPolynomial
import Mathlib.Tactic

/-!
# The Narayana Transformation

This module starts a formalization of Mao--Wang, *The Narayana transformation*,
arXiv:2607.01572v1.

The main paper theorem says that the basis transformation
`X ^ k ↦ N_{k,m}` preserves real-rooted polynomials with nonnegative
coefficients.  The proof uses Gribinski--Marcus rectangular additive
convolution.  We first expose the reusable basis-transformation interfaces from
the paper and the checked coefficient infrastructure for the generalized
Narayana polynomials.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Zero-aware predicate for real-rooted polynomials whose real roots are all
nonpositive. -/
def HasOnlyNonposRoots (p : ℝ[X]) : Prop :=
  p = 0 ∨ p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Zero-aware predicate for real-rooted polynomials whose real roots are all
nonnegative. -/
def HasOnlyNonnegRoots (p : ℝ[X]) : Prop :=
  p = 0 ∨ p.Splits ∧ ∀ r ∈ p.roots, 0 ≤ r

theorem IsPFPolynomial.hasOnlyNonposRoots {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    HasOnlyNonposRoots p :=
  hp.eq_zero_or_splits.elim Or.inl fun hsplits =>
    Or.inr ⟨hsplits, hp.roots_nonpos⟩

theorem HasOnlyNonposRoots.of_nonnegCoeffs_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hsplits : p.Splits) :
    HasOnlyNonposRoots p :=
  Or.inr ⟨hsplits, roots_nonpos_of_nonneg_coeffs hsplits hpnn⟩

/-- The linear basis transform sending `X ^ k` to `P k`. -/
def basisTransform (P : ℕ → ℝ[X]) (p : ℝ[X]) : ℝ[X] :=
  p.sum fun k a => C a * P k

theorem coeff_basisTransform (P : ℕ → ℝ[X]) (p : ℝ[X]) (j : ℕ) :
    (basisTransform P p).coeff j = p.sum fun k a => a * (P k).coeff j := by
  simp [basisTransform, Polynomial.coeff_sum, Polynomial.coeff_C_mul]

@[simp] theorem basisTransform_zero (P : ℕ → ℝ[X]) :
    basisTransform P 0 = 0 := by
  simp [basisTransform]

@[simp] theorem basisTransform_monomial (P : ℕ → ℝ[X]) (n : ℕ) (a : ℝ) :
    basisTransform P (Polynomial.monomial n a) = C a * P n := by
  rw [basisTransform, Polynomial.sum_monomial_index]
  simp

@[simp] theorem basisTransform_C (P : ℕ → ℝ[X]) (a : ℝ) :
    basisTransform P (C a) = C a * P 0 := by
  simpa using basisTransform_monomial P 0 a

@[simp] theorem basisTransform_X_pow (P : ℕ → ℝ[X]) (n : ℕ) :
    basisTransform P (X ^ n) = P n := by
  rw [show (X ^ n : ℝ[X]) = Polynomial.monomial n 1 by
    simp [Polynomial.X_pow_eq_monomial]]
  simp

theorem basisTransform_add (P : ℕ → ℝ[X]) (p q : ℝ[X]) :
    basisTransform P (p + q) = basisTransform P p + basisTransform P q := by
  rw [basisTransform, basisTransform, basisTransform]
  exact Polynomial.sum_add_index p q (fun k a => C a * P k) (by simp) (by simp [add_mul])

theorem basisTransform_smul (P : ℕ → ℝ[X]) (a : ℝ) (p : ℝ[X]) :
    basisTransform P (a • p) = C a * basisTransform P p := by
  rw [basisTransform, basisTransform]
  rw [Polynomial.sum_smul_index]
  · simp [Polynomial.sum_def, Finset.mul_sum, mul_assoc]
  · simp

theorem HasNonnegCoeffs.basisTransform {P : ℕ → ℝ[X]} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hP : ∀ k, HasNonnegCoeffs (P k)) :
    HasNonnegCoeffs (basisTransform P p) := by
  intro j
  rw [coeff_basisTransform]
  simpa only [Polynomial.sum] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hP k j)

/-- Falling factorial `⟨x⟩_k = x (x - 1) ... (x - k + 1)`. -/
def fallingFactorialPolynomial (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X - C (i : ℝ))

/-- Generalized rising factorial `(x|μ)_k = x (x + μ) ... (x + (k-1) μ)`. -/
def risingFactorialPolynomial (μ : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X + C ((i : ℝ) * μ))

/-- Brenti's falling-factorial inverse transform, paper Lemma 3.9 / Brenti
Theorem 2.4.2. -/
theorem brentiFallingFactorial {p : ℝ[X]}
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  sorry

/-- Su--Yang--Zhang generalized rising-factorial transform preserves PF
polynomials, paper Lemma 3.11. -/
theorem generalizedRisingFactorialPreservesPF {μ : ℝ} (hμ : 0 < μ) {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  sorry

/-- Coefficient `N_m(n,k)` of the generalized Narayana polynomial. -/
def narayanaTransformCoeff (m n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (Nat.choose (n + m) k : ℝ) /
    (Nat.choose (m + k) k : ℝ)

theorem narayanaTransformCoeff_nonneg (m n k : ℕ) :
    0 ≤ narayanaTransformCoeff m n k := by
  unfold narayanaTransformCoeff
  positivity

@[simp] theorem narayanaTransformCoeff_zero_right (m n : ℕ) :
    narayanaTransformCoeff m n 0 = 1 := by
  simp [narayanaTransformCoeff]

@[simp] theorem narayanaTransformCoeff_zero_left (m k : ℕ) :
    narayanaTransformCoeff m 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, narayanaTransformCoeff]
  · have hchoose : Nat.choose 0 k = 0 := by
      cases k with
      | zero => contradiction
      | succ k => simp
    simp [hk, narayanaTransformCoeff, hchoose]

/-- Generalized Narayana polynomial `N_{n,m}` from Mao--Wang, Eq. (1.2). -/
def narayanaPolynomial (m n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (narayanaTransformCoeff m n k) * X ^ k

@[simp] theorem coeff_narayanaPolynomial_of_le {m n k : ℕ} (hk : k ≤ n) :
    (narayanaPolynomial m n).coeff k = narayanaTransformCoeff m n k := by
  simp [narayanaPolynomial, hk]

@[simp] theorem coeff_narayanaPolynomial_of_lt {m n k : ℕ} (hk : n < k) :
    (narayanaPolynomial m n).coeff k = 0 := by
  simp [narayanaPolynomial, hk.not_ge]

theorem hasNonnegCoeffs_narayanaPolynomial (m n : ℕ) :
    HasNonnegCoeffs (narayanaPolynomial m n) := by
  intro k
  by_cases hk : k ≤ n
  · simp [coeff_narayanaPolynomial_of_le hk, narayanaTransformCoeff_nonneg]
  · have hk' : n < k := Nat.lt_of_not_ge hk
    simp [coeff_narayanaPolynomial_of_lt hk']

theorem natDegree_narayanaPolynomial_le (m n : ℕ) :
    (narayanaPolynomial m n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_narayanaPolynomial_of_lt hk

/-- The Narayana basis transform `X ^ k ↦ N_{k,m}`. -/
def narayanaTransform (m : ℕ) : ℝ[X] → ℝ[X] :=
  basisTransform (narayanaPolynomial m)

@[simp] theorem narayanaTransform_X_pow (m n : ℕ) :
    narayanaTransform m (X ^ n) = narayanaPolynomial m n :=
  basisTransform_X_pow (narayanaPolynomial m) n

@[simp] theorem narayanaTransform_monomial (m n : ℕ) (a : ℝ) :
    narayanaTransform m (Polynomial.monomial n a) = C a * narayanaPolynomial m n := by
  rw [narayanaTransform, basisTransform_monomial]

theorem coeff_narayanaTransform (m : ℕ) (p : ℝ[X]) (j : ℕ) :
    (narayanaTransform m p).coeff j =
      p.sum fun k a => a * (narayanaPolynomial m k).coeff j :=
  coeff_basisTransform (narayanaPolynomial m) p j

@[simp] theorem coeff_narayanaTransform_monomial (m n j : ℕ) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j =
      a * (narayanaPolynomial m n).coeff j := by
  simp [narayanaTransform_monomial]

@[simp] theorem coeff_narayanaTransform_monomial_of_le
    {m n j : ℕ} (hj : j ≤ n) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j =
      a * narayanaTransformCoeff m n j := by
  simp [hj]

@[simp] theorem coeff_narayanaTransform_monomial_of_lt
    {m n j : ℕ} (hj : n < j) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j = 0 := by
  simp [hj]

theorem HasNonnegCoeffs.narayanaTransform {m : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (narayanaTransform m p) :=
  hp.basisTransform (hasNonnegCoeffs_narayanaPolynomial m)

/-- The generalized Narayana polynomials are PF polynomials
(Dominici--Johnston--Jordaan root-location input, paper Lemma 2.5). -/
theorem narayanaPolynomialRootLocation (m n : ℕ) :
    IsPFPolynomial (narayanaPolynomial m n) := by
  sorry

/-- The Narayana transform preserves PF polynomials
(Mao--Wang Theorem 1.1 in zero-aware PF-polynomial form). -/
theorem narayanaTransformPreservesPF (m : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (narayanaTransform m p) := by
  sorry

/-- Gribinski--Marcus rectangular additive convolution coefficient. -/
def rectangularConvolutionGamma (m n i j : ℕ) : ℝ :=
  ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n - j) : ℝ) /
      ((Nat.factorial n : ℝ) * (Nat.factorial (n - i - j) : ℝ))) *
    ((Nat.factorial (n + m - i) : ℝ) * (Nat.factorial (n + m - j) : ℝ) /
      ((Nat.factorial (n + m) : ℝ) * (Nat.factorial (n + m - i - j) : ℝ)))

/-- The rectangular convolution coefficient is symmetric in its two indices. -/
theorem rectangularConvolutionGamma_symm (m n i j : ℕ) :
    rectangularConvolutionGamma m n i j = rectangularConvolutionGamma m n j i := by
  unfold rectangularConvolutionGamma
  rw [Nat.sub_right_comm n i j, Nat.sub_right_comm (n + m) i j]
  ring

def rectangularConvolutionCoeff (m n : ℕ) (f g : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    rectangularConvolutionGamma m n i (k - i) *
      f.coeff (n - i) * g.coeff (n - (k - i))

/-- Rectangular additive convolution in the coefficient convention of
Mao--Wang, Eq. (2.3). -/
def rectangularAdditiveConvolution (m n : ℕ) (f g : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (rectangularConvolutionCoeff m n f g k) * X ^ (n - k)

/-- Coefficient extraction for the rectangular additive convolution. -/
theorem coeff_rectangularAdditiveConvolution_of_le (m n : ℕ) (f g : ℝ[X])
    {j : ℕ} (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n f g).coeff j =
      rectangularConvolutionCoeff m n f g (n - j) := by
  unfold rectangularAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem (n - j)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le n j)))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Nat.sub_sub_self hj,
      if_pos rfl, mul_one]
  · intro k hk hkne
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun hjk => hkne (by lia)), mul_zero]

/-- The rectangular additive convolution has no coefficients above degree `n`. -/
theorem coeff_rectangularAdditiveConvolution_of_gt (m n : ℕ) (f g : ℝ[X])
    {j : ℕ} (hj : n < j) :
    (rectangularAdditiveConvolution m n f g).coeff j = 0 := by
  unfold rectangularAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun hjk => by lia),
    mul_zero]

/-- The rectangular additive convolution has degree at most `n`. -/
theorem natDegree_rectangularAdditiveConvolution_le (m n : ℕ) (f g : ℝ[X]) :
    (rectangularAdditiveConvolution m n f g).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_rectangularAdditiveConvolution_of_gt m n f g hk

/-- Factorial form of the generalized Narayana coefficient `N_m(n,k)`.

From `N_m(n,k) = C(n,k) * C(n+m,k) / C(m+k,k)` one gets, for `k ≤ n`,
the paper's Eq. (1.2) form. -/
theorem narayanaTransformCoeff_eq_factorial (m n k : ℕ) (hk : k ≤ n) :
    narayanaTransformCoeff m n k =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
          (Nat.factorial m : ℝ)) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ) *
          (Nat.factorial (m + k) : ℝ) *
          (Nat.factorial (n + m - k) : ℝ)) := by
  have hk2 : k ≤ n + m := hk.trans (Nat.le_add_right n m)
  have h3 : k ≤ m + k := Nat.le_add_left k m
  have e1 : (m + k) - k = m := by lia
  unfold narayanaTransformCoeff
  rw [Nat.cast_choose ℝ hk, Nat.cast_choose ℝ hk2, Nat.cast_choose ℝ h3, e1]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp

/-- Complementary-index symmetry of the generalized Narayana coefficients. -/
theorem narayanaTransformCoeff_symm (m n k : ℕ) (hk : k ≤ n) :
    narayanaTransformCoeff m n k = narayanaTransformCoeff m n (n - k) := by
  rw [narayanaTransformCoeff_eq_factorial m n k hk,
      narayanaTransformCoeff_eq_factorial m n (n - k) (Nat.sub_le n k)]
  have h1 : n - (n - k) = k := by lia
  have h2 : m + (n - k) = n + m - k := by lia
  have h3 : n + m - (n - k) = m + k := by lia
  rw [h1, h2, h3]
  ring

/-- Reversed-index coefficient of the generalized Narayana polynomial. -/
theorem coeff_narayanaPolynomial_sub (m n i : ℕ) (hi : i ≤ n) :
    (narayanaPolynomial m n).coeff (n - i) = narayanaTransformCoeff m n i := by
  rw [coeff_narayanaPolynomial_of_le (Nat.sub_le n i)]
  exact (narayanaTransformCoeff_symm m n i hi).symm

/-- The key coefficient identity from Section 2 of Mao--Wang.  For `i+j ≤ n`,
the rectangular convolution coefficient `γ_{i,j}^{(n,m)}` transports the
generalized Narayana coefficient `N_m(n,j)` to `N_m(n-i,j)`. -/
theorem rectangularConvolutionGamma_mul_narayanaTransformCoeff
    (m n i j : ℕ) (h : i + j ≤ n) :
    rectangularConvolutionGamma m n i j * narayanaTransformCoeff m n j =
      narayanaTransformCoeff m (n - i) j := by
  have hj : j ≤ n := by lia
  have hji : j ≤ n - i := by lia
  have ea : (n - i) + m = n + m - i := by lia
  rw [narayanaTransformCoeff_eq_factorial m n j hj,
      narayanaTransformCoeff_eq_factorial m (n - i) j hji, ea]
  unfold rectangularConvolutionGamma
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp

/-- Symmetric companion of
`rectangularConvolutionGamma_mul_narayanaTransformCoeff`. -/
theorem rectangularConvolutionGamma_mul_narayanaTransformCoeff_left
    (m n i j : ℕ) (h : i + j ≤ n) :
    rectangularConvolutionGamma m n i j * narayanaTransformCoeff m n i =
      narayanaTransformCoeff m (n - j) i := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_mul_narayanaTransformCoeff m n j i (by lia)

/-- Rectangular convolution of two generalized Narayana polynomials, expanded
as the finite coefficient sum before the final Vandermonde evaluation. -/
theorem rectangularConvolutionCoeff_narayanaPolynomial_of_le
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        rectangularConvolutionGamma m n i (k - i) *
          narayanaTransformCoeff m n i *
          narayanaTransformCoeff m n (k - i) := by
  unfold rectangularConvolutionCoeff
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hi_n : i ≤ n := hik.trans hk
  have hki_n : k - i ≤ n := (Nat.sub_le k i).trans hk
  rw [coeff_narayanaPolynomial_sub m n i hi_n,
    coeff_narayanaPolynomial_sub m n (k - i) hki_n]

/-- The same convolution sum after transporting one Narayana factor with the
rectangular convolution coefficient.  The remaining closed-form step is a
Vandermonde/Chu summation. -/
theorem rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (k - i) := by
  rw [rectangularConvolutionCoeff_narayanaPolynomial_of_le m n k hk]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsum : i + (k - i) ≤ n := by
    rw [Nat.add_sub_of_le hik]
    exact hk
  rw [← rectangularConvolutionGamma_mul_narayanaTransformCoeff m n i (k - i) hsum]
  ring

/-- Vandermonde variant used in the Mao--Wang Section 2 coefficient bridge.
Summing the shifted product of binomials over `Finset.range (k + 1)` collapses
to a single binomial coefficient. -/
theorem sum_choose_mul_choose_shift (m k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        Nat.choose k i * Nat.choose (2 * m + k) (m + i) =
      Nat.choose (2 * m + 2 * k) (m + k) := by
  have h1 : Nat.choose (2 * m + 2 * k) (m + k) =
      ∑ i ∈ Finset.range (m + k + 1),
        Nat.choose k i * Nat.choose (2 * m + k) (m + k - i) := by
    rw [show 2 * m + 2 * k = k + (2 * m + k) by ring, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      fun i j => Nat.choose k i * Nat.choose (2 * m + k) j]
  rw [h1, ← Finset.sum_subset (Finset.range_mono (by lia : k + 1 ≤ m + k + 1))]
  · rw [← Finset.sum_flip]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hx),
        Nat.add_sub_assoc (Finset.mem_range_succ_iff.mp hx)]
  · intro x _ hx
    have hx' : k < x :=
      Nat.lt_of_succ_le (Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx))
    rw [Nat.choose_eq_zero_of_lt hx']
    ring

/-- Reciprocal-factorial form of the Chu--Vandermonde summation appearing in
the Mao--Wang Section 2 coefficient bridge. -/
theorem sum_factorial_recip_eq (m k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ)) =
      (Nat.factorial (2 * m + 2 * k) : ℝ) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (m + k) : ℝ) ^ 2 *
          (Nat.factorial (2 * m + k) : ℝ)) := by
  have h_binom : (∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ))) =
      ∑ i ∈ Finset.range (k + 1),
        ((Nat.choose k i : ℝ) * (Nat.choose (2 * m + k) (m + i) : ℝ)) /
          ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hmi : m + i ≤ 2 * m + k := by lia
    rw [Nat.cast_choose ℝ hik, Nat.cast_choose ℝ hmi]
    field_simp
    rw [show 2 * m + k - (m + i) = m + k - i by lia]
  convert h_binom using 1
  convert congr_arg
      (fun x : ℕ =>
        (x : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)))
      (sum_choose_mul_choose_shift m k) using 1
  · rw [sum_choose_mul_choose_shift, Nat.cast_choose]
    · rw [show 2 * m + 2 * k - (m + k) = m + k by
        rw [Nat.sub_eq_of_eq_add]
        ring]
      ring
    · lia
  · convert congr_arg
        (fun x : ℕ =>
          (x : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)))
        (sum_choose_mul_choose_shift m k) using 1
    norm_num [Finset.sum_div]

/-- Short name for the transported Narayana rectangular-convolution coefficient
sum used in the Mao--Wang Section 2 bridge. -/
theorem rectangularConvolutionCoeff_narayana_eq_sum
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (k - i) :=
  rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport m n k hk

/-- Each summand of the Chu--Vandermonde sum factors as a constant independent
of `i` times a reciprocal-factorial term. -/
theorem narayana_product_term_eq (m n k i : ℕ) (hk : k ≤ n) (hi : i ≤ k) :
    narayanaTransformCoeff m n i * narayanaTransformCoeff m (n - i) (k - i) =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
          (Nat.factorial m : ℝ) ^ 2 /
            ((Nat.factorial (n - k) : ℝ) *
              (Nat.factorial (n + m - k) : ℝ))) *
        ((1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ))) := by
  have h_geometric :
      narayanaTransformCoeff m n i * narayanaTransformCoeff m (n - i) (k - i) =
        ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
            (Nat.factorial m : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (n - i) : ℝ) *
            (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (n + m - i) : ℝ))) *
        ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n + m - i) : ℝ) *
            (Nat.factorial m : ℝ) /
          ((Nat.factorial (k - i) : ℝ) * (Nat.factorial (n - k) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ) *
            (Nat.factorial (n + m - k) : ℝ))) := by
    convert congr_arg₂ (· * ·)
      (narayanaTransformCoeff_eq_factorial m n i (hi.trans hk))
      (narayanaTransformCoeff_eq_factorial m (n - i) (k - i) (by lia)) using 2
    rw [show n + m - i = n - i + m by lia,
      show n - i - (k - i) = n - k by lia,
      show m + (k - i) = m + k - i by lia,
      show n - i + m - (k - i) = n + m - k by lia]
  rw [h_geometric]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp [f0]

/-- Mao--Wang Section 2 coefficient bridge: closed form for the rectangular
convolution coefficient of a generalized Narayana polynomial with itself. -/
theorem coeff_rectangularConvolution_narayana (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      narayanaTransformCoeff m n k *
        ((Nat.factorial m : ℝ) * (Nat.factorial (2 * m + 2 * k) : ℝ) /
          ((Nat.factorial (2 * m + k) : ℝ) *
            (Nat.factorial (m + k) : ℝ))) := by
  convert rectangularConvolutionCoeff_narayana_eq_sum m n k hk using 1
  rw [Finset.sum_congr rfl
    fun i hi => narayana_product_term_eq m n k i hk
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [← Finset.mul_sum _ _ _, sum_factorial_recip_eq]
  rw [narayanaTransformCoeff_eq_factorial m n k hk]
  ring

/-- Coefficients of the rectangular additive convolution of two generalized
Narayana polynomials, reduced to the transported convolution sum. -/
theorem coeff_rectangularAdditiveConvolution_narayanaPolynomial_of_le
    (m n j : ℕ) (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n (narayanaPolynomial m n)
        (narayanaPolynomial m n)).coeff j =
      ∑ i ∈ Finset.range (n - j + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (n - j - i) := by
  rw [coeff_rectangularAdditiveConvolution_of_le m n (narayanaPolynomial m n)
      (narayanaPolynomial m n) hj,
    rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport m n (n - j)
      (Nat.sub_le n j)]

/-- Gribinski--Marcus preservation theorem for rectangular additive convolution,
in the form used by Mao--Wang, paper Lemma 2.6. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g) := by
  sorry

end RealRooted
