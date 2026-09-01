import RealRooted.NarayanaTransformation.Rectangular.Narayana

/-!
# Rectangular additive convolution preservation.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Gribinski--Marcus preservation theorem in the form used by Mao--Wang,
paper Lemma 2.6. -/
abbrev rectangularAdditiveConvolutionPreservesNonnegRootsStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n →
    g.natDegree = n →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g)

/-- Positive-degree leaf of the Gribinski--Marcus preservation theorem. The
degree-zero base case is checked separately. -/
abbrev rectangularAdditiveConvolutionPreservesNonnegRootsPositiveDegreeStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n + 1 →
    g.natDegree = n + 1 →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1) f g)

/-- Degree-at-least-three leaf of the Gribinski--Marcus preservation theorem.
The degree-zero, degree-one, and degree-two base cases are checked separately. -/
abbrev rectangularAdditiveConvolutionPreservesNonnegRootsDegreeAtLeastThreeStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n + 1 + 1 + 1 →
    g.natDegree = n + 1 + 1 + 1 →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1 + 1 + 1) f g)

/-- The top rectangular-convolution weight is one. -/
theorem rectangularConvolutionGamma_zero_zero (m n : ℕ) :
    rectangularConvolutionGamma m n 0 0 = 1 := by
  unfold rectangularConvolutionGamma
  simp only [Nat.sub_zero]
  rw [div_self (by positivity), div_self (by positivity), one_mul]

/-- The zero-index convolution coefficient is the product of the top input
coefficients. -/
theorem rectangularConvolutionCoeff_zero_index (m n : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m n f g 0 = f.coeff n * g.coeff n := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma_zero_zero]

/-- The degree-`n` coefficient of the rectangular additive convolution is the
product of the degree-`n` input coefficients. -/
theorem coeff_rectangularAdditiveConvolution_top (m n : ℕ) (f g : ℝ[X]) :
    (rectangularAdditiveConvolution m n f g).coeff n = f.coeff n * g.coeff n := by
  rw [coeff_rectangularAdditiveConvolution_of_le m n f g le_rfl, Nat.sub_self,
    rectangularConvolutionCoeff_zero_index]

/-- Reduce preservation of nonnegative roots to real stability of the
bivariate lift of the convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_of_mvRealStable_xyLift
    {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hstab : MvRealStable (xyLift (rectangularAdditiveConvolution m n f g))) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g) := by
  have hfn : f.coeff n = f.leadingCoeff := by rw [← hfdeg, Polynomial.coeff_natDegree]
  have hgn : g.coeff n = g.leadingCoeff := by rw [← hgdeg, Polynomial.coeff_natDegree]
  have hpos : 0 < (rectangularAdditiveConvolution m n f g).coeff n := by
    rw [coeff_rectangularAdditiveConvolution_top m n f g, hfn, hgn]
    exact mul_pos hflead hglead
  have hne : rectangularAdditiveConvolution m n f g ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hpos
    exact lt_irrefl 0 hpos
  exact (hasOnlyNonnegRoots_iff_mvRealStable_xyLift hne).mpr hstab

/-- Rectangular additive convolution of two exact-degree polynomials with only
nonnegative roots has a real-stable bivariate lift. -/
theorem mvRealStable_xyLift_rectangularAdditiveConvolution
    {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    MvRealStable (xyLift (rectangularAdditiveConvolution m n f g)) := by
  have hfne : f ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hflead.ne'
  have hgne : g ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hglead.ne'
  have hfdegC : (f.map Complex.ofRealHom).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective, hfdeg]
  have hgdegC : (g.map Complex.ofRealHom).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective, hgdeg]
  have hfleadC : (f.map Complex.ofRealHom).leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_map_of_injective Complex.ofReal_injective]
    intro hzero
    exact hflead.ne' (Complex.ofReal_injective (by simpa using hzero))
  have hgleadC : (g.map Complex.ofRealHom).leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_map_of_injective Complex.ofReal_injective]
    intro hzero
    exact hglead.ne' (Complex.ofReal_injective (by simpa using hzero))
  have hfstable : MvUpperHalfPlaneStable (xyLift (f.map Complex.ofRealHom)) := by
    simpa [MvRealStable] using hfroots.mvRealStable_xyLift hfne
  have hgstable : MvUpperHalfPlaneStable (xyLift (g.map Complex.ofRealHom)) := by
    simpa [MvRealStable] using hgroots.mvRealStable_xyLift hgne
  have hFstable := mvUpperHalfPlaneStable_reciprocalRectangularPolarization
    (m := m) hgdegC hgleadC hgstable
  have hGstable := mvUpperHalfPlaneStable_rectangularPolarization
    (m := m) hfdegC hfleadC hfstable
  have hFma := isMultiaffine_reciprocalRectangularPolarization
    m n (g.map Complex.ofRealHom)
  have hGma := isMultiaffine_rectangularPolarization m n (f.map Complex.ofRealHom)
  rcases liebSokal_multiaffine hFstable hGstable hFma hGma with hzero | hstable
  · have hconvne : rectangularAdditiveConvolution m n f g ≠ 0 := by
      intro hzeroConv
      have htop := congrArg (fun p : ℝ[X] => p.coeff n) hzeroConv
      have hfn : f.coeff n = f.leadingCoeff := by
        rw [← hfdeg]
        exact Polynomial.coeff_natDegree
      have hgn : g.coeff n = g.leadingCoeff := by
        rw [← hgdeg]
        exact Polynomial.coeff_natDegree
      rw [coeff_rectangularAdditiveConvolution_top m n f g, hfn, hgn,
        Polynomial.coeff_zero] at htop
      exact mul_ne_zero hflead.ne' hglead.ne' htop
    have hmapne :
        (rectangularAdditiveConvolution m n f g).map Complex.ofRealHom ≠ 0 :=
      Polynomial.map_ne_zero hconvne
    have hxyne := xyLift_ne_zero hmapne
    have hrename := congrArg (MvPolynomial.rename rectangularDiagonal) hzero
    rw [map_zero, rectangularDifferential_diagonal_identity] at hrename
    exact ((mul_ne_zero (pow_ne_zero m (by simp)) hxyne) hrename).elim
  · have hdiag := hstable.rename (f := rectangularDiagonal)
    rw [rectangularDifferential_diagonal_identity] at hdiag
    change MvUpperHalfPlaneStable
      (complexifyMv (xyLift (rectangularAdditiveConvolution m n f g)))
    rw [complexifyMv_xyLift]
    exact hdiag.right_of_mul

/-- Degree-at-least-three case of the Gribinski--Marcus preservation theorem for
rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastThree :
    rectangularAdditiveConvolutionPreservesNonnegRootsDegreeAtLeastThreeStatement := by
  intro m n f g hfdeg hgdeg hflead hglead hfroots hgroots
  apply rectangularAdditiveConvolutionPreservesNonnegRoots_of_mvRealStable_xyLift
    hfdeg hgdeg hflead hglead
  exact mvRealStable_xyLift_rectangularAdditiveConvolution
    hfdeg hgdeg hflead hglead hfroots hgroots

/-- Degree-at-least-two case of the Gribinski--Marcus preservation theorem for
rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastTwo
    {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n + 1 + 1) (hgdeg : g.natDegree = n + 1 + 1)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1 + 1) f g) := by
  rcases n with _ | n
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_two
      hfdeg hgdeg hflead hglead hfroots hgroots
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastThree
      hfdeg hgdeg hflead hglead hfroots hgroots

/-- Positive-degree case of the Gribinski--Marcus preservation theorem for
rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_positiveDegree :
    rectangularAdditiveConvolutionPreservesNonnegRootsPositiveDegreeStatement := by
  intro m n f g hfdeg hgdeg hflead hglead hfroots hgroots
  rcases n with _ | n
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_one
      hfdeg hgdeg hflead hglead hfroots hgroots
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastTwo
      hfdeg hgdeg hflead hglead hfroots hgroots

/-- Gribinski--Marcus preservation theorem for rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots :
    rectangularAdditiveConvolutionPreservesNonnegRootsStatement := by
  intro m n f g hfdeg hgdeg hflead hglead hfroots hgroots
  rcases n with _ | n
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_zero
      hfdeg hgdeg hflead hglead hfroots hgroots
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_positiveDegree
      hfdeg hgdeg hflead hglead hfroots hgroots

@[simp] theorem narayanaPolynomial_zero_right (m : ℕ) :
    narayanaPolynomial m 0 = 1 := by
  simp [narayanaPolynomial]

@[simp] theorem narayanaTransformCoeff_self (m n : ℕ) :
    narayanaTransformCoeff m n n = 1 := by
  dsimp [narayanaTransformCoeff]
  have : ((m + n).choose n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left n m)).ne'
  simp [this, add_comm n m]


end RealRooted
