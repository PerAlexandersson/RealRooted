import RealRooted.AissenSchoenbergWhitney
import RealRooted.HermiteBiehler.Converse
import RealRooted.HermiteBiehler.OddEven

/-!
# Hermite--Biehler to Hurwitz stability

This file applies the general converse Hermite--Biehler theorem to the
conformal odd/even substitution. It separates the analytic substitution
interfaces and the right-half-plane stability endpoint from the converse
root-geometry proof.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Analytic bridge from the Hermite--Biehler stable polynomial `q + i p` to
right-half-plane stability of `q(x^2) + x p(x^2)`.

This isolates the classical conformal-substitution part of the
-/
abbrev HermiteBiehlerStableToHurwitzOddEvenStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q))

/-! ## Reduction of the forward Hermite--Biehler/Hurwitz bridge to a
first-quadrant conformal-substitution interface -/

/-- First-quadrant form of the forward Hermite--Biehler/Hurwitz conformal
substitution: it suffices to exclude roots of `q(x²) + x p(x²)` in the open
first quadrant `{Re > 0, Im > 0}`. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ z : ℂ, 0 < z.re → 0 < z.im →
      (complexify (oddEvenPolynomial p q)).eval z ≠ 0

/-- Upper-half-plane substitution form of the forward Hermite--Biehler/Hurwitz
bridge: for any upper-half-plane point `w` with a right-half-plane square root
`z`, the Hurwitz combination `q(w) + z·p(w)` is nonzero.

This is the genuinely analytic conformal-substitution core: the quadratic map
`z ↦ z²` sends the open first quadrant onto the open upper half-plane, so this
interface and the first-quadrant interface above carry exactly the same
content. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ ⦃w z : ℂ⦄, 0 < w.im → z ^ 2 = w → 0 < z.re →
      (complexify q).eval w + z * (complexify p).eval w ≠ 0

/-- The first-quadrant interface follows from the upper-half-plane substitution
interface: for `z` in the open first quadrant, `w = z²` lies in the open upper
half-plane and `z` is a right-half-plane square root of `w`. -/
theorem hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement :=
  fun p q h_p h_q h_stable z hzre hzim => by
  rw [eval_complexify_oddEvenPolynomial]
  have h_w : 0 < (z ^ 2).im := by
    rw [pow_two, Complex.mul_im]
    positivity
  simp [*]

/-- Checked reduction of the forward Hermite--Biehler/Hurwitz odd/even bridge to
its first-quadrant conformal-substitution core.

`HermiteBiehlerStableToHurwitzOddEvenStatement` follows from
`HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement`: the real-axis case
`Im z = 0` is handled by positivity of the nonnegative-coefficient polynomial
`q(x²) + x p(x²)`, and the lower half-plane case `Im z < 0` is reduced to the
first quadrant by complex conjugation. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (h : HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement := by
  intro p q h_p h_q h_stable z hzre
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
      h h_p h_q h_stable (starRingEnd ℂ z) h_re h_ci
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
    exact h h_p h_q h_stable z hzre h_im

/-- Composite reduction: the forward Hermite--Biehler/Hurwitz odd/even bridge
follows from the upper-half-plane substitution interface. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement :=
  hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution h)

/-- Packaging form of the analytic Hermite--Biehler-to-Hurwitz odd/even
bridge, including the coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_oddEvenPolynomial_of_hermiteBiehlerStableToHurwitz
    (h : HermiteBiehlerStableToHurwitzOddEvenStatement) {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq, h hp hq hstable⟩

theorem hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution :
    HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement := by
  intro p q h_p h_q h_stable w z hwim hzw hzre
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
  have h_q_pos : HasPosLeadingCoeff q := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_q h_q_ne
  by_cases h_q_deg : 1 ≤ q.natDegree
  · have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_p h_p_ne
    have h_prec : Prec p q := prec_of_stable_general h_q_pos h_p_pos h_stable h_q_deg
    have h_ratio : ((complexify p).eval w / (complexify q).eval w).im ≤ 0 :=
      im_ratio_nonpos_general h_q_pos h_p_pos h_prec h_q_deg hwim
    have h_qw : (complexify q).eval w ≠ 0 := by
      obtain ⟨-, ⟨-, hqs⟩, -⟩ := id h_prec
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
    have h_p_pos : HasPosLeadingCoeff p := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_p h_p_ne
    obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable h_q_pos h_p_pos h_stable
    have h_p_deg₀ : p.natDegree = 0 := by lia
    have h_qc : (complexify q).eval w = ((q.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_q_deg₀]; simp
    have h_pc : (complexify p).eval w = ((p.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_p_deg₀]; simp
    simp_all

theorem hermiteBiehlerStableToHurwitzOddEven {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) :=
  hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution hp hq h

end RealRooted
