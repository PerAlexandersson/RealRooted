module

public import RealRooted.BorceaBranden.Applications.PoissonStarClose
public import RealRooted.BorceaBranden.Applications.PoissonStarTransport
public import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
public import RealRooted.BoundarySpecializationGeneral
public import RealRooted.HermiteBiehler.StablePencil

/-!
# Final stability and algebraic characterizations for the univariate Poisson product

This file closes the stability equivalences and proves that the step-`c`
falling-factorial transform conjugates `starC` to ordinary multiplication.
-/

public section

open Polynomial

namespace RealRooted.Poisson

noncomputable section

private theorem strictInterl_one_X : StrictInterl (1 : ℝ[X]) X := by
  exact StrictInterl.of_degree_zero_right_of_degree_one one_ne_zero
    Polynomial.Splits.one X_ne_zero Polynomial.Splits.X (by simp) (by simp)

private theorem leadingCoeff_starC_X {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    (starC c f X).leadingCoeff = f.leadingCoeff := by
  rw [leadingCoeff_starC hf0 X_ne_zero, leadingCoeff_X, mul_one]

/-- A nonzero admissible factor has a stable Euler pencil. -/
theorem IsAdmissible.isUpperHalfPlaneStablePencil_starC_X
    {c : ℝ} {f : ℝ[X]} (hf : IsAdmissible c f) :
    IsUpperHalfPlaneStablePencil (starC c f X) f := by
  have hinter : StrictInterl f (starC c f X) := by
    simpa only [starC_one_right] using hf.strictInterl_starC strictInterl_one_X
  have hlc := leadingCoeff_ne_zero.mpr hf.1
  rcases lt_or_gt_of_ne hlc with hlcneg | hlcpos
  · have hleft : HasPosLeadingCoeff (-(starC c f X)) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_neg, leadingCoeff_starC_X hf.1]
      linarith
    have hright : HasPosLeadingCoeff (-f) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_neg]
      linarith
    have hinterNeg : StrictInterl (-f) (-(starC c f X)) := by
      have h := (hinter.C_mul_left (a := -1) (by norm_num)).C_mul_right
        (a := -1) (by norm_num)
      simpa using h
    have hstable := isUpperHalfPlaneStablePencil_of_strictInterl
      hleft hright hinterNeg
    simpa using hstable.neg_neg
  · have hleft : HasPosLeadingCoeff (starC c f X) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_starC_X hf.1]
      exact hlcpos
    have hright : HasPosLeadingCoeff f := hlcpos
    exact isUpperHalfPlaneStablePencil_of_strictInterl hleft hright hinter

/-- Stability of the Euler pencil forces the affine-test condition. -/
theorem preservesAffineRealRooted_of_isUpperHalfPlaneStablePencil_starC_X
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0)
    (hstable : IsUpperHalfPlaneStablePencil (starC c f X) f) :
    PreservesAffineRealRooted c f := by
  have hAdeg : (starC c f X).natDegree = f.natDegree + 1 := by
    rw [natDegree_starC hf0 X_ne_zero, natDegree_X]
  have hlc := leadingCoeff_ne_zero.mpr hf0
  have hinter : StrictInterl f (starC c f X) := by
    rcases lt_or_gt_of_ne hlc with hlcneg | hlcpos
    · have hleft : HasPosLeadingCoeff (-(starC c f X)) := by
        unfold HasPosLeadingCoeff
        rw [leadingCoeff_neg, leadingCoeff_starC_X hf0]
        linarith
      have hright : HasPosLeadingCoeff (-f) := by
        unfold HasPosLeadingCoeff
        rw [leadingCoeff_neg]
        linarith
      have hneg := strictInterl_of_stable_general hleft hright
        hstable.neg_neg.hermiteBiehler (by rw [natDegree_neg, hAdeg]; lia)
      have h := (hneg.C_mul_left (a := -1) (by norm_num)).C_mul_right
        (a := -1) (by norm_num)
      simpa using h
    · have hleft : HasPosLeadingCoeff (starC c f X) := by
        unfold HasPosLeadingCoeff
        rw [leadingCoeff_starC_X hf0]
        exact hlcpos
      have hright : HasPosLeadingCoeff f := hlcpos
      exact strictInterl_of_stable_general hleft hright hstable.hermiteBiehler
        (by rw [hAdeg]; lia)
  have hall : AllComboRealRooted f (starC c f X) :=
    allComboRealRooted_of_strictInterl hinter
  intro a b
  rw [starC_affine_right]
  convert hall a b using 1
  rw [starC_X_right]
  ring

/-- For a nonzero factor, stability of the Euler pencil is equivalent to the
root-sign admissibility condition. -/
theorem isUpperHalfPlaneStablePencil_starC_X_iff_isAdmissible
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    IsUpperHalfPlaneStablePencil (starC c f X) f ↔ IsAdmissible c f := by
  constructor
  · intro hstable
    exact isAdmissible_of_preservesAffineRealRooted hf0
      (preservesAffineRealRooted_of_isUpperHalfPlaneStablePencil_starC_X hf0 hstable)
  · exact IsAdmissible.isUpperHalfPlaneStablePencil_starC_X

/-- Stability of the signed Poisson symbol forces the fixed factor to split. -/
private theorem splits_of_poissonSignedSymbol_stable
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0)
    (hstable : MvUpperHalfPlaneStable (poissonSignedSymbol c f)) :
    f.Splits := by
  have hspecialized := hstable.orZero.specializeAt_real_general (1 : Fin 2) 0
  rcases hspecialized with hzero | hspecialized
  · exfalso
    apply hf0
    have hcomplex : complexify f = 0 := by
      apply Polynomial.funext
      intro z
      have heval := congrArg (MvPolynomial.eval ![z, Complex.I]) hzero
      change MvPolynomial.eval ![z, Complex.I]
        (MvPolynomial.specializeAt 1 (0 : ℂ) (poissonSignedSymbol c f)) = 0 at heval
      rw [MvPolynomial.eval_specializeAt, eval_poissonSignedSymbol] at heval
      simpa using heval
    exact (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hcomplex
  · apply IsUpperHalfPlaneStable.splits_complexify
    intro z hz
    have hne := hspecialized ![z, Complex.I] (by
      intro i
      fin_cases i
      · simpa using hz
      · norm_num)
    rw [MvPolynomial.eval_specializeAt, eval_poissonSignedSymbol] at hne
    simpa using hne

/-- For a nonzero factor, signed-symbol stability is equivalent to the exact
root-sign admissibility condition. -/
theorem mvUpperHalfPlaneStable_poissonSignedSymbol_iff_isAdmissible
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    MvUpperHalfPlaneStable (poissonSignedSymbol c f) ↔ IsAdmissible c f := by
  constructor
  · intro hstable
    refine ⟨hf0, splits_of_poissonSignedSymbol_stable hf0 hstable, ?_⟩
    intro r hr
    have hroot : f.eval r = 0 := by
      exact (Polynomial.IsRoot.def.mp ((mem_roots hf0).mp hr))
    by_contra hcr
    have hcrpos : 0 < c * r := lt_of_not_ge hcr
    let d : ℂ := 1 - (c : ℂ) * Complex.I
    have hd0 : d ≠ 0 := by
      intro hd
      have hre := congrArg Complex.re hd
      norm_num [d] at hre
    let x : ℂ := (r : ℂ) / d
    have hxim : x.im = r * c / Complex.normSq d := by
      dsimp only [x, d]
      rw [Complex.div_im]
      simp only [Complex.ofReal_im, zero_mul, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.mul_im,
        Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_sub,
        mul_one]
      ring
    have hnorm : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd0
    have hximpos : 0 < x.im := by
      rw [hxim]
      exact div_pos (by simpa [mul_comm] using hcrpos) hnorm
    let z : Fin 2 → ℂ := ![x, Complex.I]
    have hz : ∀ i, 0 < (z i).im := by
      intro i
      fin_cases i
      · simpa [z] using hximpos
      · simp [z]
    have hne := hstable z hz
    apply hne
    rw [eval_poissonSignedSymbol]
    have hxd : x * d = (r : ℂ) := div_mul_cancel₀ (r : ℂ) hd0
    rw [show z 0 = x by rfl, show z 1 = Complex.I by rfl]
    change (complexify f).eval (x * d) = 0
    rw [hxd, eval_complexify_ofReal, hroot, Complex.ofReal_zero]
  · exact IsAdmissible.poissonSignedSymbol_stable

/-- For a nonzero factor, stability of the explicit Euler pencil
`X (f + c f') + Y f` is equivalent to admissibility. -/
theorem isUpperHalfPlaneStablePencil_euler_iff_isAdmissible
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    IsUpperHalfPlaneStablePencil (X * (f + C c * f.derivative)) f ↔
      IsAdmissible c f := by
  rw [← starC_X_right]
  exact isUpperHalfPlaneStablePencil_starC_X_iff_isAdmissible hf0

/-- For a nonzero factor, preservation on all split inputs is equivalent to
stability of the explicit Euler pencil. -/
theorem preservesRealRootedOrZero_iff_isUpperHalfPlaneStablePencil_euler
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    PreservesRealRootedOrZero (starCLinearMap c f) ↔
      IsUpperHalfPlaneStablePencil (X * (f + C c * f.derivative)) f := by
  rw [preservesRealRootedOrZero_iff_isAdmissible hf0,
    isUpperHalfPlaneStablePencil_euler_iff_isAdmissible hf0]

/-- For a nonzero factor, preservation on affine inputs is equivalent to
stability of the explicit Euler pencil. -/
theorem preservesAffineRealRooted_iff_isUpperHalfPlaneStablePencil_euler
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    PreservesAffineRealRooted c f ↔
      IsUpperHalfPlaneStablePencil (X * (f + C c * f.derivative)) f := by
  rw [preservesAffineRealRooted_iff_isAdmissible hf0,
    isUpperHalfPlaneStablePencil_euler_iff_isAdmissible hf0]

/-- For a nonzero factor, stability of the Euler pencil is equivalent to
stability of the signed Weyl symbol. -/
theorem isUpperHalfPlaneStablePencil_euler_iff_poissonSignedSymbol_stable
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    IsUpperHalfPlaneStablePencil (X * (f + C c * f.derivative)) f ↔
      MvUpperHalfPlaneStable (poissonSignedSymbol c f) := by
  rw [isUpperHalfPlaneStablePencil_euler_iff_isAdmissible hf0,
    mvUpperHalfPlaneStable_poissonSignedSymbol_iff_isAdmissible hf0]

end

end RealRooted.Poisson
