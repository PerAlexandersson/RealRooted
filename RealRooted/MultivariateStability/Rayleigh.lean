import RealRooted.Multiaffine.Rayleigh
import RealRooted.PartialSymmetrization

/-!
# The bivariate Rayleigh criterion

For a real multiaffine polynomial in two variables, upper-half-plane
stability is equivalent to nontriviality and nonnegativity of its Rayleigh
difference.  This is the two-coordinate base case of the general Rayleigh
criterion.
-/

namespace RealRooted

noncomputable section

/-- The imaginary part of a real fractional-linear coefficient quotient is
controlled by its two-by-two determinant. -/
theorem im_bivariateQuotient_ofReal
    (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) + (b : ℂ) * z) / ((c : ℂ) + (d : ℂ) * z)).im =
      (b * c - a * d) * z.im /
        Complex.normSq ((c : ℂ) + (d : ℂ) * z) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero]
  ring

/-- A nonzero real affine denominator cannot vanish at an
upper-half-plane point. -/
theorem ofReal_add_mul_ne_zero_of_im_pos
    (c d : ℝ) (z : ℂ) (hcd : c ≠ 0 ∨ d ≠ 0) (hz : 0 < z.im) :
    (c : ℂ) + (d : ℂ) * z ≠ 0 := by
  intro hzero
  by_cases hd : d = 0
  · have hc : c ≠ 0 := by
      rcases hcd with hc | hdne
      · exact hc
      · exact (hdne hd).elim
    have hre := congrArg Complex.re hzero
    simp only [hd, Complex.ofReal_zero, zero_mul, add_zero,
      Complex.ofReal_re, Complex.zero_re] at hre
    exact hc hre
  · have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_add, Complex.zero_im] at him
    have hmul : d * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hmul with hd0 | hz0
    · exact hd hd0
    · exact (ne_of_gt hz) hz0

/-- For a real bivariate coefficient form, the Rayleigh property is exactly
nonnegativity of the coefficient determinant. -/
theorem isRayleigh_bivariate_iff (a b c d : ℝ) :
    MvPolynomial.IsRayleigh
        ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) +
          MvPolynomial.C b * MvPolynomial.X 0 +
          MvPolynomial.C c * MvPolynomial.X 1 +
          MvPolynomial.C d * MvPolynomial.X 0 * MvPolynomial.X 1) ↔
      0 ≤ b * c - a * d := by
  let P : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.C a +
      MvPolynomial.C b * MvPolynomial.X 0 +
      MvPolynomial.C c * MvPolynomial.X 1 +
      MvPolynomial.C d * MvPolynomial.X 0 * MvPolynomial.X 1
  have hma : MvPolynomial.IsMultiaffine P := by
    simpa [P] using MvPolynomial.isMultiaffine_bivariate
      (0 : Fin 2) 1 (by decide) a b c d
  have hdiff : MvPolynomial.rayleighDifference P 0 1 =
      MvPolynomial.C (b * c - a * d) := by
    simpa [P] using MvPolynomial.rayleighDifference_bivariate
      (0 : Fin 2) 1 (by decide) a b c d
  constructor
  · intro h
    have h01 := h 0 1 (fun _ => 0)
    rw [hdiff] at h01
    simpa using h01
  · intro hdet i j x
    change 0 ≤ MvPolynomial.eval x
      (MvPolynomial.rayleighDifference P i j)
    fin_cases i
    · fin_cases j
      · exact hma.eval_rayleighDifference_self_nonneg 0 x
      · norm_num [P, MvPolynomial.rayleighDifference,
          MvPolynomial.pderiv_mul]
        nlinarith
    · fin_cases j
      · norm_num [P, MvPolynomial.rayleighDifference,
          MvPolynomial.pderiv_mul]
        nlinarith
      · exact hma.eval_rayleighDifference_self_nonneg 1 x

/-- A real bivariate multiaffine polynomial is stable exactly when it is
nonzero and its coefficient determinant is nonnegative. -/
theorem mvRealStable_bivariate_coeff_iff (a b c d : ℝ) :
    MvRealStable
        ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) +
          MvPolynomial.C b * MvPolynomial.X 0 +
          MvPolynomial.C c * MvPolynomial.X 1 +
          MvPolynomial.C d * MvPolynomial.X 0 * MvPolynomial.X 1) ↔
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
        0 ≤ b * c - a * d := by
  let P : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.C a +
      MvPolynomial.C b * MvPolynomial.X 0 +
      MvPolynomial.C c * MvPolynomial.X 1 +
      MvPolynomial.C d * MvPolynomial.X 0 * MvPolynomial.X 1
  have hcomplexify :
      complexifyMv P =
        bivariateMultiaffinePolynomial (a : ℂ) (b : ℂ) (c : ℂ)
          (d : ℂ) := by
    simp [P, complexifyMv, bivariateMultiaffinePolynomial]
  constructor
  · intro hstable
    have hP : MvUpperHalfPlaneStable
        (bivariateMultiaffinePolynomial (a : ℂ) (b : ℂ) (c : ℂ)
          (d : ℂ)) := by
      have hstableP : MvRealStable P := by simpa [P] using hstable
      rw [← hcomplexify]
      exact hstableP
    constructor
    · by_contra hcoeff
      simp only [not_or, ne_eq, not_not] at hcoeff
      rcases hcoeff with ⟨ha, hb, hc, hd⟩
      apply hstable.ne_zero
      simp [ha, hb, hc, hd]
    · by_contra hdet
      have hdetneg : b * c - a * d < 0 := lt_of_not_ge hdet
      have hcd : c ≠ 0 ∨ d ≠ 0 := by
        by_contra h
        simp only [not_or, ne_eq, not_not] at h
        rcases h with ⟨rfl, rfl⟩
        simp at hdetneg
      let z : ℂ := Complex.I
      have hz : 0 < z.im := by simp [z]
      have hden : (c : ℂ) + (d : ℂ) * z ≠ 0 :=
        ofReal_add_mul_ne_zero_of_im_pos c d z hcd hz
      let w : ℂ :=
        -(((a : ℂ) + (b : ℂ) * z) /
          ((c : ℂ) + (d : ℂ) * z))
      have hw : 0 < w.im := by
        dsimp only [w]
        rw [Complex.neg_im, im_bivariateQuotient_ofReal]
        have hnorm : 0 < Complex.normSq ((c : ℂ) + (d : ℂ) * z) :=
          Complex.normSq_pos.mpr hden
        exact neg_pos.mpr (div_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos hdetneg hz) hnorm)
      have hzero :
          (a : ℂ) + (b : ℂ) * z + (c : ℂ) * w +
              (d : ℂ) * z * w = 0 :=
        (bivariate_eq_zero_iff (a : ℂ) (b : ℂ) (c : ℂ)
          (d : ℂ) z w hden).2 rfl
      have hne := hP ![z, w] (by
        intro i
        fin_cases i
        · exact hz
        · exact hw)
      rw [eval_bivariateMultiaffinePolynomial] at hne
      exact hne hzero
  · rintro ⟨hcoeff, hdet⟩
    change MvRealStable P
    unfold MvRealStable
    rw [hcomplexify]
    intro z hz
    have hz0 : 0 < (z 0).im := hz 0
    have hz1 : 0 < (z 1).im := hz 1
    rw [eval_bivariateMultiaffinePolynomial]
    by_cases hcd0 : c = 0 ∧ d = 0
    · rcases hcd0 with ⟨rfl, rfl⟩
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      by_cases hb : b = 0
      · have ha : a ≠ 0 := by simpa [hb] using hcoeff
        simpa [hb, Complex.ofReal_ne_zero]
      · intro hzero
        have him := congrArg Complex.im hzero
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, zero_add, Complex.zero_im] at him
        have hmul : b * (z 0).im = 0 := by linarith
        rcases mul_eq_zero.mp hmul with hb0 | hz0'
        · exact hb hb0
        · exact (ne_of_gt hz0) hz0'
    · have hcd : c ≠ 0 ∨ d ≠ 0 := not_and_or.mp hcd0
      have hden : (c : ℂ) + (d : ℂ) * z 0 ≠ 0 :=
        ofReal_add_mul_ne_zero_of_im_pos c d (z 0) hcd hz0
      intro hzero
      have hroot := (bivariate_eq_zero_iff
        (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (z 0) (z 1) hden).1
          hzero
      have hquot : 0 ≤
          (((a : ℂ) + (b : ℂ) * z 0) /
            ((c : ℂ) + (d : ℂ) * z 0)).im := by
        rw [im_bivariateQuotient_ofReal]
        exact div_nonneg (mul_nonneg hdet (le_of_lt hz0))
          (Complex.normSq_nonneg _)
      have him := congrArg Complex.im hroot
      rw [Complex.neg_im] at him
      nlinarith

/-- Bivariate real stability is equivalent to nontriviality together with
the Rayleigh property. -/
theorem mvRealStable_bivariate_iff (a b c d : ℝ) :
    MvRealStable
        ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) +
          MvPolynomial.C b * MvPolynomial.X 0 +
          MvPolynomial.C c * MvPolynomial.X 1 +
          MvPolynomial.C d * MvPolynomial.X 0 * MvPolynomial.X 1) ↔
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
        MvPolynomial.IsRayleigh
          ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) +
            MvPolynomial.C b * MvPolynomial.X 0 +
            MvPolynomial.C c * MvPolynomial.X 1 +
            MvPolynomial.C d * MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [mvRealStable_bivariate_coeff_iff, isRayleigh_bivariate_iff]

end

end RealRooted
