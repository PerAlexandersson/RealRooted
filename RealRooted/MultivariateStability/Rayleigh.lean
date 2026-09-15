import RealRooted.Multiaffine.TwoCoordinateSlice
import RealRooted.MultivariateStability.Specialization
import RealRooted.PartialSymmetrization

/-!
# Rayleigh consequences of multivariate stability

For a real multiaffine polynomial in two variables, upper-half-plane
stability is equivalent to nontriviality and nonnegativity of its Rayleigh
difference.  Finite boundary slices then show that every real-stable
multiaffine polynomial is Rayleigh, without requiring a finite ambient
variable type.
-/

namespace RealRooted

noncomputable section

/-- Restricting a real-stable polynomial to affine motion in two coordinates
preserves real stability up to the zero polynomial.  Only variables actually
occurring in the polynomial are specialized, so the ambient variable type
need not be finite. -/
theorem MvRealStable.twoCoordinateAffineSlice_zero_or
    {σ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (x : σ → ℝ) (i j : σ) (hij : i ≠ j) :
    MvPolynomial.twoCoordinateAffineSlice x i j P = 0 ∨
      MvRealStable (MvPolynomial.twoCoordinateAffineSlice x i j P) := by
  let l := MvPolynomial.twoCoordinateSpectators P i j
  let Q := MvPolynomial.specializeAtList x l P
  have hQcases : Q = 0 ∨ MvRealStable Q := by
    simpa only [Q, l] using
      hP.specializeAtList_zero_or_general x
        (MvPolynomial.twoCoordinateSpectators P i j)
  rcases hQcases with hQ | hQ
  · left
    apply MvPolynomial.funext
    intro z
    simp only [map_zero]
    rw [MvPolynomial.eval_twoCoordinateAffineSlice x i j hij]
    let w : σ → ℝ := Function.update
      (Function.update x i (x i + z 0)) j (x j + z 1)
    have heval := MvPolynomial.eval_specializeAtList_twoCoordinateSpectators
      x w i j hij P
    change MvPolynomial.eval w Q = _ at heval
    rw [hQ, map_zero] at heval
    simpa [w, hij] using heval.symm
  · right
    change MvUpperHalfPlaneStable
      (complexifyMv (MvPolynomial.twoCoordinateAffineSlice x i j P))
    rw [complexifyMv, MvPolynomial.map_twoCoordinateAffineSlice]
    intro z hz
    rw [MvPolynomial.eval_twoCoordinateAffineSlice
      (fun k => Complex.ofRealHom (x k)) i j hij]
    let w : σ → ℂ := fun k =>
      if k = i then (x i : ℂ) + z 0
      else if k = j then (x j : ℂ) + z 1
      else Complex.I
    have hw : ∀ k, 0 < (w k).im := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa [w] using hz 0
      · by_cases hkj : k = j
        · subst k
          simpa [w, hki] using hz 1
        · simp [w, hki, hkj]
    have hQw : MvPolynomial.eval w (complexifyMv Q) ≠ 0 := hQ w hw
    have hspectators :
        MvPolynomial.twoCoordinateSpectators (complexifyMv P) i j =
          MvPolynomial.twoCoordinateSpectators P i j := by
      simp [MvPolynomial.twoCoordinateSpectators, complexifyMv,
        MvPolynomial.vars_map_of_injective P
          Complex.ofRealHom.injective]
    simp only [Q, l, complexifyMv_specializeAtList] at hQw
    rw [← hspectators] at hQw
    rw [MvPolynomial.eval_specializeAtList_twoCoordinateSpectators
      (fun k => (x k : ℂ)) w i j hij] at hQw
    have hwi : w i = (x i : ℂ) + z 0 := by simp [w]
    have hwj : w j = (x j : ℂ) + z 1 := by simp [w, Ne.symm hij]
    rw [hwi, hwj] at hQw
    change MvPolynomial.eval
      (Function.update
        (Function.update (fun k => (x k : ℂ)) i ((x i : ℂ) + z 0))
        j ((x j : ℂ) + z 1)) (complexifyMv P) ≠ 0
    exact hQw

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

/-- Every real-stable multiaffine polynomial is Rayleigh.  The proof reduces
each inequality to the bivariate criterion through a finite boundary slice. -/
theorem MvRealStable.isRayleigh_of_isMultiaffine
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (hPma : MvPolynomial.IsMultiaffine P) :
    MvPolynomial.IsRayleigh P := by
  classical
  intro i j x
  by_cases hij : i = j
  · subst j
    exact hPma.eval_rayleighDifference_self_nonneg i x
  · rcases hP.twoCoordinateAffineSlice_zero_or x i j hij with
      hzero | hstable
    · have hdiff :=
        hPma.rayleighDifference_twoCoordinateAffineSlice x i j hij
      have heval := congrArg
        (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℝ))) hdiff
      have hvalue :
          MvPolynomial.eval x
            (MvPolynomial.rayleighDifference P i j) = 0 := by
        simpa [hzero, MvPolynomial.rayleighDifference] using heval.symm
      simp [hvalue]
    · rw [hPma.twoCoordinateAffineSlice_eq x i j hij] at hstable
      have hdet := (mvRealStable_bivariate_coeff_iff
        (MvPolynomial.eval x P)
        (MvPolynomial.eval x (MvPolynomial.pderiv i P))
        (MvPolynomial.eval x (MvPolynomial.pderiv j P))
        (MvPolynomial.eval x
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j P)))).mp hstable
      rw [MvPolynomial.eval_rayleighDifference]
      exact hdet.2

end

end RealRooted
