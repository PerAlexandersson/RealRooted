import RealRooted.HermiteBiehler
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Closure
import RealRooted.PFPolynomial
import RealRooted.SamePhaseInterlacing

/-!
# Closure of Pólya-frequency polynomials and proper position

This file proves coefficientwise sequential closure for Pólya-frequency
sequences and polynomials.  Its final theorem combines bounded-degree root
closedness with the sign-normalized Hermite--Biehler correspondence to retain
the orientation of the zero-aware proper-position relation `Interl`.
-/

open Filter Matrix Polynomial Topology

noncomputable section

namespace RealRooted

/-- Pointwise limits of Pólya-frequency sequences are Pólya-frequency. -/
theorem IsPolyaFreqSeq.of_tendsto
    {a : ℕ → ℕ → ℝ} {a₀ : ℕ → ℝ}
    (ha : ∀ k, IsPolyaFreqSeq (a k))
    (hlim : ∀ i, Tendsto (fun k => a k i) atTop (𝓝 (a₀ i))) :
    IsPolyaFreqSeq a₀ := by
  rw [IsPolyaFreqSeq]
  apply Matrix.IsTotallyNonneg.of_tendsto (fun k => ha k)
  intro i j
  by_cases hji : j ≤ i
  · simpa [toeplitz_apply, hji] using hlim (i - j)
  · simp [toeplitz_apply, hji]

/-- Coefficientwise limits of Pólya-frequency polynomials are
Pólya-frequency.  No degree bound is needed for this coefficient-sequence
statement. -/
theorem IsPFPolynomial.of_coeff_tendsto
    {p : ℕ → ℝ[X]} {p₀ : ℝ[X]}
    (hp : ∀ k, IsPFPolynomial (p k))
    (hlim : ∀ i, Tendsto (fun k => (p k).coeff i) atTop (𝓝 (p₀.coeff i))) :
    IsPFPolynomial p₀ := by
  apply IsPFPolynomial.of_polyaFreqSeq
  exact IsPolyaFreqSeq.of_tendsto (fun k => (hp k).to_sequence) hlim

/-- Uniform degree bounds turn coefficientwise convergence into pointwise
evaluation convergence. -/
theorem Polynomial.tendsto_eval_of_coeff_tendsto_of_natDegree_le
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hdeg : ∀ k, (p k).natDegree ≤ N) (hdeg₀ : p₀.natDegree ≤ N)
    (hcoeff : ∀ i, Tendsto (fun k => (p k).coeff i) atTop (𝓝 (p₀.coeff i)))
    (z : ℂ) :
    Tendsto (fun k => (p k).eval z) atTop (𝓝 (p₀.eval z)) := by
  have hsum : Tendsto
      (fun k => ∑ i ∈ Finset.range (N + 1), (p k).coeff i * z ^ i)
      atTop
      (𝓝 (∑ i ∈ Finset.range (N + 1), p₀.coeff i * z ^ i)) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    exact (hcoeff i).mul_const (z ^ i)
  rw [show (fun k => (p k).eval z) =
      fun k => ∑ i ∈ Finset.range (N + 1), (p k).coeff i * z ^ i by
    funext k
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg k)) z]
  rw [show p₀.eval z =
      ∑ i ∈ Finset.range (N + 1), p₀.coeff i * z ^ i by
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg₀) z]
  exact hsum

/-- A nonzero bounded-degree evaluation limit of upper-half-plane-stable-or-zero
polynomials is upper-half-plane stable. -/
theorem isUpperHalfPlaneStable_of_tendsto_eval_of_natDegree_le
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hp₀ : p₀ ≠ 0) (hdeg : ∀ k, (p k).natDegree ≤ N)
    (hstable : ∀ k, p k = 0 ∨ IsUpperHalfPlaneStable (p k))
    (heval : ∀ z, Tendsto (fun k => (p k).eval z) atTop (𝓝 (p₀.eval z))) :
    IsUpperHalfPlaneStable p₀ := by
  intro z hz hzero
  have hzroot : z ∈ p₀.roots := mem_roots'.mpr ⟨hp₀, hzero⟩
  have hzclosed : z ∈ {w : ℂ | w.im ≤ 0} := by
    apply Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
      (isClosed_le Complex.continuous_im continuous_const) hdeg
      (fun k w hw => ?_) heval z hzroot
    rcases hstable k with hkzero | hkstable
    · simp [hkzero] at hw
    · exact le_of_not_gt fun hwim => hkstable w hwim (mem_roots'.mp hw).2
  exact (not_le_of_gt hz) hzclosed

/-- Uniformly bounded-degree coefficientwise limits preserve zero-aware
proper position for Pólya-frequency polynomial pairs. -/
theorem prec0_of_pf_coeff_tendsto_of_natDegree_le
    {p q : ℕ → ℝ[X]} {p₀ q₀ : ℝ[X]} {N : ℕ}
    (hp : ∀ k, IsPFPolynomial (p k))
    (hq : ∀ k, IsPFPolynomial (q k))
    (hprec : ∀ k, Interl (p k) (q k))
    (hpdeg : ∀ k, (p k).natDegree ≤ N)
    (hqdeg : ∀ k, (q k).natDegree ≤ N)
    (hpcoeff : ∀ i, Tendsto (fun k => (p k).coeff i) atTop
      (𝓝 (p₀.coeff i)))
    (hqcoeff : ∀ i, Tendsto (fun k => (q k).coeff i) atTop
      (𝓝 (q₀.coeff i))) :
    Interl p₀ q₀ := by
  have hp₀pf : IsPFPolynomial p₀ :=
    IsPFPolynomial.of_coeff_tendsto hp hpcoeff
  have hq₀pf : IsPFPolynomial q₀ :=
    IsPFPolynomial.of_coeff_tendsto hq hqcoeff
  by_cases hp₀zero : p₀ = 0
  · exact Or.inl hp₀zero
  by_cases hq₀zero : q₀ = 0
  · exact Or.inr (Or.inl hq₀zero)
  right
  right
  have hp₀pos : HasPosLeadingCoeff p₀ :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hp₀pf.hasNonnegCoeffs hp₀zero
  have hq₀pos : HasPosLeadingCoeff q₀ :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hq₀pf.hasNonnegCoeffs hq₀zero
  let H : ℕ → ℂ[X] := fun k => hermiteBiehlerPolynomial (q k) (p k)
  let H₀ : ℂ[X] := hermiteBiehlerPolynomial q₀ p₀
  have hHdeg : ∀ k, (H k).natDegree ≤ N := by
    intro k
    dsimp only [H, hermiteBiehlerPolynomial, complexify]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective]
        using hqdeg k
    · exact (natDegree_C_mul_le _ _).trans <| by
        simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective]
          using hpdeg k
  have hH₀deg : H₀.natDegree ≤ N := by
    dsimp only [H₀, hermiteBiehlerPolynomial, complexify]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective]
        using natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
          have hzero : ∀ k, (q k).coeff i = 0 := fun k =>
            coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hqdeg k) hi)
          exact tendsto_nhds_unique (hqcoeff i)
            (by simp [hzero])
    · apply (natDegree_C_mul_le _ _).trans
      simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective]
        using natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
          have hzero : ∀ k, (p k).coeff i = 0 := fun k =>
            coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hpdeg k) hi)
          exact tendsto_nhds_unique (hpcoeff i)
            (by simp [hzero])
  have hHcoeff : ∀ i, Tendsto (fun k => (H k).coeff i) atTop
      (𝓝 (H₀.coeff i)) := by
    intro i
    simp only [H, H₀, hermiteBiehler_coeff]
    exact ((Complex.continuous_ofReal.tendsto _).comp (hqcoeff i)).add
      (tendsto_const_nhds.mul
        ((Complex.continuous_ofReal.tendsto _).comp (hpcoeff i)))
  have hHstable : ∀ k, H k = 0 ∨ IsUpperHalfPlaneStable (H k) := by
    intro k
    rcases hprec k with hpzero | hqzero | hpq
    · dsimp only [H]
      rw [hpzero]
      by_cases hqzero' : q k = 0
      · left
        simp [hermiteBiehlerPolynomial, hqzero']
      · right
        simpa [hermiteBiehlerPolynomial] using
          Polynomial.Splits.isUpperHalfPlaneStable_complexify
            ((hq k).ne_zero_and_splits hqzero').2 hqzero'
    · dsimp only [H]
      rw [hqzero]
      by_cases hpzero' : p k = 0
      · left
        simp [hermiteBiehlerPolynomial, hpzero']
      · right
        intro z hz
        simp only [hermiteBiehlerPolynomial, complexify_zero, zero_add,
          eval_mul, eval_C]
        exact mul_ne_zero (by simp)
          (eval_complexify_ne_zero_of_splits_of_im_pos
            ((hp k).ne_zero_and_splits hpzero').2 hpzero' hz)
    · right
      dsimp only [H]
      exact hermiteBiehlerForwardPos
        (hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero
          (hq k).hasNonnegCoeffs hpq.2.1.1)
        (hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero
          (hp k).hasNonnegCoeffs hpq.1.1)
        hpq
  have hH₀zero : H₀ ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun r : ℂ[X] => r.coeff p₀.natDegree) hzero
    rw [hermiteBiehler_coeff] at hcoeff
    have him := congrArg Complex.im hcoeff
    simp only [coeff_zero, Complex.add_im, Complex.ofReal_im, zero_add,
      Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, one_mul,
      Complex.ofReal_re] at him
    exact (leadingCoeff_ne_zero.mpr hp₀zero) (by simpa using him)
  have hH₀stable : IsUpperHalfPlaneStable H₀ :=
    isUpperHalfPlaneStable_of_tendsto_eval_of_natDegree_le hH₀zero hHdeg
      hHstable fun z =>
        Polynomial.tendsto_eval_of_coeff_tendsto_of_natDegree_le
          hHdeg hH₀deg hHcoeff z
  exact prec_of_upperHalfPlaneStable_hermiteBiehler hq₀pos hp₀pos hH₀stable

end RealRooted
