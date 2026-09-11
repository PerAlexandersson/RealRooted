import RealRooted.FiniteFreeAdditiveIdentity
import RealRooted.HermiteBiehler.Basic
import RealRooted.LiebSokal

/-!
# Finite-free additive convolution preservation

This module turns the algebraic differential identity for finite-free
additive convolution into a bounded-degree splitness theorem.  It is
zero-aware: inputs of degree smaller than the ambient degree may yield zero.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The degree-boxed finite-free additive convolution of split real
polynomials is split.  The output may be zero when an input degree is smaller
than the ambient degree. -/
theorem splits_finiteFreeAdditiveConvolution
    (d : ℕ) {p q : ℝ[X]}
    (hp : p.Splits) (hq : q.Splits)
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d) :
    (finiteFreeAdditiveConvolution d p q).Splits := by
  by_cases hp0 : p = 0
  · subst p
    simp [finiteFreeAdditiveConvolution, finiteFreeAdditiveConvolutionCoeff]
  by_cases hq0 : q = 0
  · subst q
    simp [finiteFreeAdditiveConvolution, finiteFreeAdditiveConvolutionCoeff]
  have hpdegC : (complexify p).natDegree ≤ d := by
    rw [complexify, Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
    exact hpdeg
  have hqdegC : (complexify q).natDegree ≤ d := by
    rw [complexify, Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
    exact hqdeg
  have hpstable : IsUpperHalfPlaneStable (complexify p) :=
    Polynomial.Splits.isUpperHalfPlaneStable_complexify hp hp0
  have hqstable : IsUpperHalfPlaneStable (complexify q) :=
    Polynomial.Splits.isUpperHalfPlaneStable_complexify hq hq0
  have hFstable : MvUpperHalfPlaneStable
      (signedMultiaffineReciprocal (polarization d (complexify p))) :=
    MvUpperHalfPlaneStable.signedMultiaffineReciprocal
      (mvUpperHalfPlaneStable_polarization hpdegC hpstable)
      (isMultiaffine_polarization d _)
  have hGstable : MvUpperHalfPlaneStable (polarization d (complexify q)) :=
    mvUpperHalfPlaneStable_polarization hqdegC hqstable
  rcases hFstable.liebSokal_multiaffine hGstable
      (isMultiaffine_signedMultiaffineReciprocal _)
      (isMultiaffine_polarization d _) with hzero | hstable
  · have hdiagzero := congrArg (diagonalProjection d) hzero
    change diagonalProjection d
      (applyNegDifferential
        (signedMultiaffineReciprocal
          (polarization d (p.map Complex.ofRealHom)))
        (polarization d (q.map Complex.ofRealHom))) = 0 at hdiagzero
    rw [diagonal_applyNegDifferential_signedPolarization] at hdiagzero
    have hscalar : Polynomial.C ((-1 : ℂ) ^ d) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hmapzero : (finiteFreeAdditiveConvolution d p q).map Complex.ofRealHom = 0 :=
      (mul_eq_zero.mp hdiagzero).resolve_left hscalar
    have hconvzero : finiteFreeAdditiveConvolution d p q = 0 :=
      (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hmapzero
    simp [hconvzero]
  · have hdiagstable : IsUpperHalfPlaneStable
        (diagonalProjection d
          (applyNegDifferential
            (signedMultiaffineReciprocal (polarization d (complexify p)))
            (polarization d (complexify q)))) := by
      intro z hz
      rw [eval_diagonalProjection]
      exact hstable (fun _ => z) (fun _ => hz)
    change IsUpperHalfPlaneStable
      (diagonalProjection d
        (applyNegDifferential
          (signedMultiaffineReciprocal
            (polarization d (p.map Complex.ofRealHom)))
          (polarization d (q.map Complex.ofRealHom)))) at hdiagstable
    rw [diagonal_applyNegDifferential_signedPolarization] at hdiagstable
    have hconvstable : IsUpperHalfPlaneStable
        ((finiteFreeAdditiveConvolution d p q).map Complex.ofRealHom) := by
      intro z hz hzero
      apply hdiagstable z hz
      simp [hzero]
    exact IsUpperHalfPlaneStable.splits_complexify hconvstable

end

end RealRooted
