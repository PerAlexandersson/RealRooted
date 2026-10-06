import RealRooted.AissenSchoenbergWhitney
import RealRooted.HermiteBiehler.Converse
import RealRooted.HermiteBiehler.OddEven

/-!
# Hermite--Biehler to Hurwitz stability

This file applies the general converse Hermite--Biehler theorem to the
conformal odd/even substitution. It separates the upper-half-plane and
first-quadrant substitution lemmas and the right-half-plane stability theorem
from the converse root-geometry proof.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Upper-half-plane substitution form of the forward Hermite--Biehler/Hurwitz
odd/even theorem: for any upper-half-plane point `w` with a right-half-plane
square root `z`, the Hurwitz combination `q(w) + z·p(w)` is nonzero.

This is the analytic conformal-substitution core: the quadratic map `z ↦ z²`
sends the open first quadrant onto the open upper half-plane. -/
theorem hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution ⦃p q : ℝ[X]⦄
    (h_p : HasNonnegCoeffs p) (h_q : HasNonnegCoeffs q)
    (h_stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p))
    ⦃w z : ℂ⦄ (hwim : 0 < w.im) (hzw : z ^ 2 = w) (hzre : 0 < z.re) :
    (complexify q).eval w + z * (complexify p).eval w ≠ 0 := by
  have h_zim : 0 < z.im := by
    have h_we : w.im = 2 * z.re * z.im := by rw [← hzw, pow_two, Complex.mul_im]; ring
    simp_all
  intro heq
  have hpw : (complexify p).eval w ≠ 0 := by
    intro hp₀
    rw [hp₀, mul_zero, add_zero] at heq
    exact h_stable w hwim (by simp [*])
  have h_z_eq : z = -((complexify q).eval w / (complexify p).eval w) := by
    field_simp; linear_combination heq
  have h_q_ne : q ≠ 0 := by
    rintro rfl
    simp only [complexify, Polynomial.map_zero, eval_zero, zero_add] at heq
    have h_z₀ : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre
    refine hpw ?_
    rcases mul_eq_zero.mp heq with h | h
    · exact absurd h h_z₀
    · exact h
  have h_q_pos : HasPosLeadingCoeff q := HasNonnegCoeffs.pos_leadingCoeff h_q h_q_ne
  by_cases h_q_deg : 1 ≤ q.natDegree
  · have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := HasNonnegCoeffs.pos_leadingCoeff h_p h_p_ne
    have h_strictInterl : StrictInterl p q :=
      strictInterl_of_stable_general h_q_pos h_p_pos h_stable h_q_deg
    have h_ratio : ((complexify p).eval w / (complexify q).eval w).im ≤ 0 :=
      im_ratio_nonpos_general h_q_pos h_p_pos h_strictInterl h_q_deg hwim
    have h_qw : (complexify q).eval w ≠ 0 := by
      obtain ⟨-, ⟨-, hqs⟩, -⟩ := id h_strictInterl
      exact eval_complexify_ne_zero_of_splits_of_im_pos hqs h_q_ne hwim
    have h_qp_im : 0 ≤ ((complexify q).eval w / (complexify p).eval w).im := by
      have h_recip : ((complexify q).eval w / (complexify p).eval w)
          = ((complexify p).eval w / (complexify q).eval w)⁻¹ := by simp
      rw [h_recip, Complex.inv_im]
      have h_normsq : 0 < Complex.normSq ((complexify p).eval w / (complexify q).eval w) :=
        Complex.normSq_pos.mpr (div_ne_zero hpw h_qw)
      have h_num : 0 ≤ -((complexify p).eval w / (complexify q).eval w).im := by simp [*]
      exact div_nonneg h_num h_normsq.le
    have h_zim_le : z.im ≤ 0 := by simp [*]
    linarith [h_zim, h_zim_le]
  · push Not at h_q_deg
    have h_q_deg₀ : q.natDegree = 0 := by lia
    have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := HasNonnegCoeffs.pos_leadingCoeff h_p h_p_ne
    obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable h_q_pos h_p_pos h_stable
    have h_p_deg₀ : p.natDegree = 0 := by lia
    have h_qc : (complexify q).eval w = ((q.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_q_deg₀]; simp
    have h_pc : (complexify p).eval w = ((p.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_p_deg₀]; simp
    simp_all

/-- First-quadrant form of the forward Hermite--Biehler/Hurwitz conformal
substitution: `q(x²) + x p(x²)` has no roots in the open first quadrant
`{Re > 0, Im > 0}`.  For `z` in the open first quadrant, `w = z²` lies in the
open upper half-plane and `z` is a right-half-plane square root of `w`. -/
theorem hermiteBiehlerStableToHurwitzOddEven_firstQuadrant ⦃p q : ℝ[X]⦄
    (h_p : HasNonnegCoeffs p) (h_q : HasNonnegCoeffs q)
    (h_stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p))
    (z : ℂ) (hzre : 0 < z.re) (hzim : 0 < z.im) :
    (complexify (oddEvenPolynomial p q)).eval z ≠ 0 := by
  have h := hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution h_p h_q h_stable
  rw [eval_complexify_oddEvenPolynomial]
  have h_w : 0 < (z ^ 2).im := by
    rw [pow_two, Complex.mul_im]
    positivity
  simp [*]

/-- Forward Hermite--Biehler/Hurwitz odd/even theorem: if `q + i p` is
upper-half-plane stable and `p`, `q` have nonnegative coefficients, then
`q(x²) + x p(x²)` is right-half-plane stable.

The first quadrant is `hermiteBiehlerStableToHurwitzOddEven_firstQuadrant`; the
real-axis case `Im z = 0` is handled by positivity of the nonnegative-coefficient
polynomial, and the lower half-plane case `Im z < 0` is reduced to the first
quadrant by complex conjugation. -/
theorem hermiteBiehlerStableToHurwitzOddEven {p q : ℝ[X]}
    (h_p : HasNonnegCoeffs p) (h_q : HasNonnegCoeffs q)
    (h_stable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) := by
  intro z hzre
  -- The odd/even polynomial is nonzero, otherwise the stability hypothesis fails.
  have h_f_ne : oddEvenPolynomial p q ≠ 0 := by
    intro h₀
    rw [oddEvenPolynomial_eq_zero_iff] at h₀
    obtain ⟨hp₀, hq₀⟩ := h₀
    have h_I := h_stable Complex.I (by simp)
    simp_all
  rcases lt_trichotomy z.im 0 with h_im | h_im | h_im
  · -- Lower half-plane: reduce to the first quadrant by conjugation.
    have h_conj := eval_complexify_conj (oddEvenPolynomial p q) z
    have h_re : 0 < (starRingEnd ℂ z).re := by simp [*]
    have h_ci : 0 < (starRingEnd ℂ z).im := by simp [*]
    have h_ne : (complexify (oddEvenPolynomial p q)).eval (starRingEnd ℂ z) ≠ 0 :=
      hermiteBiehlerStableToHurwitzOddEven_firstQuadrant h_p h_q h_stable
        (starRingEnd ℂ z) h_re h_ci
    intro h₀
    apply h_ne
    rw [h_conj, h₀, map_zero]
  · -- Real axis: positivity of the nonnegative-coefficient polynomial.
    have h_z : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h_im]
    rw [h_z, eval_complexify_ofReal]
    have h_pos : 0 < (oddEvenPolynomial p q).eval z.re :=
      eval_pos_of_hasNonnegCoeffs (hasNonnegCoeffs_oddEvenPolynomial h_p h_q) h_f_ne hzre
    simpa using h_pos.ne'
  · -- First quadrant: the interface applies directly.
    exact hermiteBiehlerStableToHurwitzOddEven_firstQuadrant h_p h_q h_stable z hzre h_im

end RealRooted
