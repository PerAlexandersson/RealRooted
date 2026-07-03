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

@[simp] theorem basisTransform_X_pow (P : ℕ → ℝ[X]) (n : ℕ) :
    basisTransform P (X ^ n) = P n := by
  rw [show (X ^ n : ℝ[X]) = Polynomial.monomial n 1 by
    simp [Polynomial.X_pow_eq_monomial]]
  rw [basisTransform, Polynomial.sum_monomial_index]
  · simp
  · simp

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
def brentiFallingFactorialStatement : Prop :=
  ∀ {p : ℝ[X]},
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Su--Yang--Zhang generalized rising-factorial transform, paper Lemma 3.11.
-/
def generalizedRisingFactorialPreservesPFStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

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

theorem HasNonnegCoeffs.narayanaTransform {m : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (narayanaTransform m p) :=
  hp.basisTransform (hasNonnegCoeffs_narayanaPolynomial m)

/-- Dominici--Johnston--Jordaan root-location input for the generalized
Narayana polynomials, paper Lemma 2.5. -/
def narayanaPolynomialRootLocationStatement : Prop :=
  ∀ m n : ℕ, IsPFPolynomial (narayanaPolynomial m n)

/-- Mao--Wang Theorem 1.1 in zero-aware PF-polynomial form. -/
def narayanaTransformPreservesPFStatement : Prop :=
  ∀ (m : ℕ) {p : ℝ[X]},
    IsPFPolynomial p → IsPFPolynomial (narayanaTransform m p)

/-- Gribinski--Marcus rectangular additive convolution coefficient. -/
def rectangularConvolutionGamma (m n i j : ℕ) : ℝ :=
  ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n - j) : ℝ) /
      ((Nat.factorial n : ℝ) * (Nat.factorial (n - i - j) : ℝ))) *
    ((Nat.factorial (n + m - i) : ℝ) * (Nat.factorial (n + m - j) : ℝ) /
      ((Nat.factorial (n + m) : ℝ) * (Nat.factorial (n + m - i - j) : ℝ)))

def rectangularConvolutionCoeff (m n : ℕ) (f g : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    rectangularConvolutionGamma m n i (k - i) *
      f.coeff (n - i) * g.coeff (n - (k - i))

/-- Rectangular additive convolution in the coefficient convention of
Mao--Wang, Eq. (2.3). -/
def rectangularAdditiveConvolution (m n : ℕ) (f g : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (rectangularConvolutionCoeff m n f g k) * X ^ (n - k)

/-- Gribinski--Marcus preservation theorem in the form used by Mao--Wang,
paper Lemma 2.6. -/
def rectangularAdditiveConvolutionPreservesNonnegRootsStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n →
    g.natDegree = n →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g)

end RealRooted
