import RealRooted.BrandenVecchi.ChowContinuity
import RealRooted.BrandenVecchi.ChowSupersymmetric
import RealRooted.BrandenVecchi.SupersymmetricLimits
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real

/-!
# Chow polynomials of infinite Pólya-frequency symbols

This file proves the constant-term-one case of Brändén--Vecchi, Theorem 8.4.
The infinite Aissen--Schoenberg--Whitney--Edrei symbol is approached by the
finite supersymmetric products from `SupersymmetricLimits`.  At every fixed
rank, `ChowContinuity` turns coefficient convergence of the symbols into
coefficient convergence of their Chow polynomials.  Bounded-degree root
closedness and zero-aware proper-position closedness then transfer the finite
certificates from `ChowSupersymmetric` to the limit.
-/

open Filter Matrix Polynomial Topology

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The finite numerator alphabet used to approximate an ASW--Edrei symbol. -/
def aswEdreiTruncationNumerator
    (gamma : ℝ) (alpha : ℕ → ℝ) (N : ℕ) : List ℝ :=
  List.replicate N (gamma * (N : ℝ)⁻¹) ++ parameterPrefix alpha N

/-- The finite denominator alphabet used to approximate an ASW--Edrei symbol. -/
def aswEdreiTruncationDenominator
    (beta : ℕ → ℝ) (N : ℕ) : List ℝ :=
  parameterPrefix beta N

/-- The rank-`n` Chow polynomial of the `N`th finite ASW--Edrei
approximation. -/
def aswEdreiTruncationChow
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N n : ℕ) : ℝ[X] :=
  finiteSupersymmetricChow
    (aswEdreiTruncationNumerator gamma alpha N)
    (aswEdreiTruncationDenominator beta N) n

/-- The rank-`n` Chow-derangement polynomial of the `N`th finite ASW--Edrei
approximation. -/
def aswEdreiTruncationChowDerangement
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N n : ℕ) : ℝ[X] :=
  finiteSupersymmetricChowDerangement
    (aswEdreiTruncationNumerator gamma alpha N)
    (aswEdreiTruncationDenominator beta N) n

/-- The lower Toeplitz matrix of an infinite ASW--Edrei coefficient
sequence. -/
def aswEdreiToeplitz
    (gamma : ℝ) (alpha beta : ℕ → ℝ) : LowerTriangularMatrix ℝ :=
  toeplitz (aswEdreiCoeff gamma alpha beta)

/-- The fixed-rank Chow polynomial of an infinite ASW--Edrei symbol. -/
def aswEdreiChow
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  chowPolynomial (aswEdreiToeplitz gamma alpha beta) n

/-- The fixed-rank Chow-derangement polynomial of an infinite ASW--Edrei
symbol. -/
def aswEdreiChowDerangement
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  chowDerangement (aswEdreiToeplitz gamma alpha beta) n

private theorem truncationNumerator_nonneg
    {gamma : ℝ} {alpha : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (N : ℕ) :
    ∀ x ∈ aswEdreiTruncationNumerator gamma alpha N, 0 ≤ x := by
  intro x hx
  simp only [aswEdreiTruncationNumerator, List.mem_append,
    List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩ | hx
  · exact mul_nonneg hgamma (inv_nonneg.mpr (Nat.cast_nonneg N))
  · simpa [parameterPrefix] using
      (List.forall_mem_ofFn_iff.mpr fun i : Fin N => halpha i) x hx

private theorem truncationDenominator_nonneg
    {beta : ℕ → ℝ} (hbeta : ∀ i, 0 ≤ beta i) (N : ℕ) :
    ∀ y ∈ aswEdreiTruncationDenominator beta N, 0 ≤ y := by
  simpa [aswEdreiTruncationDenominator, parameterPrefix] using
    (List.forall_mem_ofFn_iff.mpr fun i : Fin N => hbeta i)

private theorem truncationCoeff_eq_finiteSupersymmetricCoeff
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N : ℕ) :
    aswEdreiTruncationCoeff gamma alpha beta N =
      finiteSupersymmetricCoeff
        (aswEdreiTruncationNumerator gamma alpha N)
        (aswEdreiTruncationDenominator beta N) := by
  rfl

/-- Each coefficient of a fixed-rank finite Chow approximation converges to
the corresponding coefficient of the infinite-symbol Chow polynomial. -/
theorem tendsto_coeff_aswEdreiTruncationChow
    {gamma : ℝ} {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n d : ℕ) :
    Tendsto
      (fun N => (aswEdreiTruncationChow gamma alpha beta N n).coeff d)
      atTop (𝓝 ((aswEdreiChow gamma alpha beta n).coeff d)) := by
  simpa [aswEdreiTruncationChow, finiteSupersymmetricChow,
    finiteSupersymmetricToeplitz, aswEdreiChow, aswEdreiToeplitz,
    truncationCoeff_eq_finiteSupersymmetricCoeff] using
    tendsto_coeff_chowPolynomial_toeplitz
      (fun N => aswEdreiTruncationCoeff gamma alpha beta N)
      (aswEdreiCoeff gamma alpha beta) n
      (fun k _ => tendsto_aswEdreiTruncationCoeff halpha hbeta hsum k) d

/-- Each coefficient of a fixed-rank finite Chow-derangement approximation
converges to its infinite-symbol counterpart. -/
theorem tendsto_coeff_aswEdreiTruncationChowDerangement
    {gamma : ℝ} {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n d : ℕ) :
    Tendsto
      (fun N =>
        (aswEdreiTruncationChowDerangement gamma alpha beta N n).coeff d)
      atTop (𝓝 ((aswEdreiChowDerangement gamma alpha beta n).coeff d)) := by
  simpa [aswEdreiTruncationChowDerangement,
    finiteSupersymmetricChowDerangement, finiteSupersymmetricToeplitz,
    aswEdreiChowDerangement, aswEdreiToeplitz,
    truncationCoeff_eq_finiteSupersymmetricCoeff] using
    tendsto_coeff_chowDerangement_toeplitz
      (fun N => aswEdreiTruncationCoeff gamma alpha beta N)
      (aswEdreiCoeff gamma alpha beta) n
      (fun k _ => tendsto_aswEdreiTruncationCoeff halpha hbeta hsum k) d

theorem natDegree_aswEdreiTruncationChow_le
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N n : ℕ) :
    (aswEdreiTruncationChow gamma alpha beta N n).natDegree ≤ n :=
  natDegree_chowPolynomial_le _ n

theorem natDegree_aswEdreiTruncationChowDerangement_le
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N n : ℕ) :
    (aswEdreiTruncationChowDerangement gamma alpha beta N n).natDegree ≤ n :=
  natDegree_chowDerangement_le _ n

theorem natDegree_aswEdreiChow_le
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (n : ℕ) :
    (aswEdreiChow gamma alpha beta n).natDegree ≤ n :=
  natDegree_chowPolynomial_le _ n

theorem natDegree_aswEdreiChowDerangement_le
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (n : ℕ) :
    (aswEdreiChowDerangement gamma alpha beta n).natDegree ≤ n :=
  natDegree_chowDerangement_le _ n

private theorem eq_zero_or_splits_of_coeff_tendsto_of_natDegree_le
    {p : ℕ → ℝ[X]} {p₀ : ℝ[X]} {N : ℕ}
    (hdeg : ∀ k, (p k).natDegree ≤ N) (hdeg₀ : p₀.natDegree ≤ N)
    (hsplit : ∀ k, p k = 0 ∨ (p k).Splits)
    (hcoeff : ∀ i, Tendsto (fun k => (p k).coeff i) atTop
      (𝓝 (p₀.coeff i))) :
    p₀ = 0 ∨ p₀.Splits := by
  apply Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
      hdeg hsplit
  intro z
  apply Polynomial.tendsto_eval_of_coeff_tendsto_of_natDegree_le
      (p := fun k => (p k).map Complex.ofRealHom)
      (p₀ := p₀.map Complex.ofRealHom)
  · intro k
    simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective]
      using hdeg k
  · simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective]
      using hdeg₀
  · intro i
    simpa [coeff_map, Complex.ofRealHom_eq_coe, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp (hcoeff i)

private theorem truncationChow_isPFPolynomial
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (N n : ℕ) :
    IsPFPolynomial (aswEdreiTruncationChow gamma alpha beta N n) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact finiteSupersymmetricChow_nonnegCoeffs
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · exact finiteSupersymmetricChow_eq_zero_or_splits
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n

private theorem truncationChowDerangement_isPFPolynomial
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (N n : ℕ) :
    IsPFPolynomial
      (aswEdreiTruncationChowDerangement gamma alpha beta N n) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact finiteSupersymmetricChowDerangement_nonnegCoeffs
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · exact finiteSupersymmetricChowDerangement_eq_zero_or_splits
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n

/-- The fixed-rank infinite-symbol Chow polynomial is Pólya-frequency.  This
is the coefficientwise limit of the checked finite certificates. -/
theorem aswEdreiChow_isPFPolynomial
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    IsPFPolynomial (aswEdreiChow gamma alpha beta n) := by
  apply IsPFPolynomial.of_coeff_tendsto
      (p := fun N => aswEdreiTruncationChow gamma alpha beta N n)
  · exact fun N =>
      truncationChow_isPFPolynomial hgamma halpha hbeta N n
  · exact tendsto_coeff_aswEdreiTruncationChow halpha hbeta hsum n

/-- The fixed-rank infinite-symbol Chow-derangement polynomial is
Pólya-frequency, with the zero case retained. -/
theorem aswEdreiChowDerangement_isPFPolynomial
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    IsPFPolynomial (aswEdreiChowDerangement gamma alpha beta n) := by
  apply IsPFPolynomial.of_coeff_tendsto
      (p := fun N => aswEdreiTruncationChowDerangement gamma alpha beta N n)
  · exact fun N =>
      truncationChowDerangement_isPFPolynomial hgamma halpha hbeta N n
  · exact tendsto_coeff_aswEdreiTruncationChowDerangement
      halpha hbeta hsum n

/-- Infinite-symbol Chow polynomials have nonnegative coefficients. -/
theorem aswEdreiChow_nonnegCoeffs
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    HasNonnegCoeffs (aswEdreiChow gamma alpha beta n) :=
  (aswEdreiChow_isPFPolynomial hgamma halpha hbeta hsum n).hasNonnegCoeffs

/-- Infinite-symbol Chow polynomials are zero or split over the reals. -/
theorem aswEdreiChow_eq_zero_or_splits
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    aswEdreiChow gamma alpha beta n = 0 ∨
      (aswEdreiChow gamma alpha beta n).Splits := by
  apply eq_zero_or_splits_of_coeff_tendsto_of_natDegree_le
      (p := fun N => aswEdreiTruncationChow gamma alpha beta N n)
      (N := n)
  · exact fun N => natDegree_aswEdreiTruncationChow_le
      gamma alpha beta N n
  · exact natDegree_aswEdreiChow_le gamma alpha beta n
  · intro N
    exact finiteSupersymmetricChow_eq_zero_or_splits
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · exact tendsto_coeff_aswEdreiTruncationChow halpha hbeta hsum n

/-- Infinite-symbol Chow-derangement polynomials have nonnegative
coefficients. -/
theorem aswEdreiChowDerangement_nonnegCoeffs
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    HasNonnegCoeffs (aswEdreiChowDerangement gamma alpha beta n) :=
  (aswEdreiChowDerangement_isPFPolynomial hgamma halpha hbeta hsum n).hasNonnegCoeffs

/-- Infinite-symbol Chow-derangement polynomials are zero or split over the
reals. -/
theorem aswEdreiChowDerangement_eq_zero_or_splits
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    aswEdreiChowDerangement gamma alpha beta n = 0 ∨
      (aswEdreiChowDerangement gamma alpha beta n).Splits := by
  apply eq_zero_or_splits_of_coeff_tendsto_of_natDegree_le
      (p := fun N =>
        aswEdreiTruncationChowDerangement gamma alpha beta N n)
      (N := n)
  · exact fun N => natDegree_aswEdreiTruncationChowDerangement_le
      gamma alpha beta N n
  · exact natDegree_aswEdreiChowDerangement_le gamma alpha beta n
  · intro N
    exact finiteSupersymmetricChowDerangement_eq_zero_or_splits
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · exact tendsto_coeff_aswEdreiTruncationChowDerangement
      halpha hbeta hsum n

/-- In a fixed infinite-symbol row, the Chow polynomial precedes the
Chow-derangement endpoint, including all zero cases. -/
theorem aswEdreiChow_prec0_derangement
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    Prec0 (aswEdreiChow gamma alpha beta n)
      (aswEdreiChowDerangement gamma alpha beta n) := by
  apply prec0_of_pf_coeff_tendsto_of_natDegree_le
      (p := fun N => aswEdreiTruncationChow gamma alpha beta N n)
      (q := fun N =>
        aswEdreiTruncationChowDerangement gamma alpha beta N n)
      (N := n)
  · exact fun N =>
      truncationChow_isPFPolynomial hgamma halpha hbeta N n
  · exact fun N =>
      truncationChowDerangement_isPFPolynomial hgamma halpha hbeta N n
  · intro N
    exact finiteSupersymmetricChow_prec0_derangement
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · exact fun N => natDegree_aswEdreiTruncationChow_le
      gamma alpha beta N n
  · exact fun N => natDegree_aswEdreiTruncationChowDerangement_le
      gamma alpha beta N n
  · exact tendsto_coeff_aswEdreiTruncationChow halpha hbeta hsum n
  · exact tendsto_coeff_aswEdreiTruncationChowDerangement
      halpha hbeta hsum n

/-- Consecutive infinite-symbol Chow polynomials remain in zero-aware proper
position. -/
theorem aswEdreiChow_prec0_succ
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    Prec0 (aswEdreiChow gamma alpha beta n)
      (aswEdreiChow gamma alpha beta (n + 1)) := by
  apply prec0_of_pf_coeff_tendsto_of_natDegree_le
      (p := fun N => aswEdreiTruncationChow gamma alpha beta N n)
      (q := fun N => aswEdreiTruncationChow gamma alpha beta N (n + 1))
      (N := n + 1)
  · exact fun N =>
      truncationChow_isPFPolynomial hgamma halpha hbeta N n
  · exact fun N =>
      truncationChow_isPFPolynomial hgamma halpha hbeta N (n + 1)
  · intro N
    exact finiteSupersymmetricChow_prec0_succ
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · intro N
    exact (natDegree_aswEdreiTruncationChow_le gamma alpha beta N n).trans
      (Nat.le_succ n)
  · exact fun N => natDegree_aswEdreiTruncationChow_le
      gamma alpha beta N (n + 1)
  · exact tendsto_coeff_aswEdreiTruncationChow halpha hbeta hsum n
  · exact tendsto_coeff_aswEdreiTruncationChow halpha hbeta hsum (n + 1)

/-- Consecutive infinite-symbol Chow-derangement polynomials remain in
zero-aware proper position. -/
theorem aswEdreiChowDerangement_prec0_succ
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    Prec0 (aswEdreiChowDerangement gamma alpha beta n)
      (aswEdreiChowDerangement gamma alpha beta (n + 1)) := by
  apply prec0_of_pf_coeff_tendsto_of_natDegree_le
      (p := fun N =>
        aswEdreiTruncationChowDerangement gamma alpha beta N n)
      (q := fun N =>
        aswEdreiTruncationChowDerangement gamma alpha beta N (n + 1))
      (N := n + 1)
  · exact fun N =>
      truncationChowDerangement_isPFPolynomial hgamma halpha hbeta N n
  · exact fun N =>
      truncationChowDerangement_isPFPolynomial hgamma halpha hbeta N (n + 1)
  · intro N
    exact finiteSupersymmetricChowDerangement_prec0_succ
      (truncationNumerator_nonneg hgamma halpha N)
      (truncationDenominator_nonneg hbeta N) n
  · intro N
    exact (natDegree_aswEdreiTruncationChowDerangement_le
      gamma alpha beta N n).trans (Nat.le_succ n)
  · exact fun N => natDegree_aswEdreiTruncationChowDerangement_le
      gamma alpha beta N (n + 1)
  · exact tendsto_coeff_aswEdreiTruncationChowDerangement
      halpha hbeta hsum n
  · exact tendsto_coeff_aswEdreiTruncationChowDerangement
      halpha hbeta hsum (n + 1)

/-- Constant-term-one Brändén--Vecchi Theorem 8.4 for the ASW--Edrei
symbol `exp (gamma * z) * ∏ᵢ (1 + alphaᵢ * z) /
∏ᵢ (1 - betaᵢ * z)`: every fixed-rank Chow polynomial is
Pólya-frequency, and consecutive ranks are in zero-aware proper position. -/
theorem aswEdrei_chow_theorem
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (n : ℕ) :
    IsPFPolynomial (aswEdreiChow gamma alpha beta n) ∧
      Prec0 (aswEdreiChow gamma alpha beta n)
        (aswEdreiChow gamma alpha beta (n + 1)) :=
  ⟨aswEdreiChow_isPFPolynomial hgamma halpha hbeta hsum n,
    aswEdreiChow_prec0_succ hgamma halpha hbeta hsum n⟩

end

end RealRooted.BrandenVecchi
