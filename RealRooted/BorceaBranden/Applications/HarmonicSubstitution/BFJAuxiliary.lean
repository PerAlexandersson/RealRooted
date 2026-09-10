import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.CoefficientExtraction
import RealRooted.BorceaBranden.Applications.HarmonicSubstitution

/-!
# Brändén--Ferroni--Jochemko auxiliary product

This file packages the translated factor, denominator-cleared harmonic factor,
and distinguished coefficient used in the stability proof for
polynomial-value products.
-/

namespace MvPolynomial

noncomputable section

/-- Add one auxiliary variable to every variable of a polynomial. -/
def addAuxiliary {R σ : Type*} [CommSemiring R] (P : MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  aeval (fun i => X (some i) + X none) P

/-- The auxiliary product in the Brändén--Ferroni--Jochemko proof. -/
def bfjAuxiliary {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) : MvPolynomial (Option (Fin 2)) R :=
  addAuxiliary P * harmonicClear Q

/-- The distinguished coefficient extracted from the BFJ auxiliary product. -/
def bfjCoefficient {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) (b : ℕ) : MvPolynomial (Fin 2) R :=
  (optionEquivLeft R (Fin 2) (bfjAuxiliary P Q)).coeff (2 * b)

namespace HasNonnegCoeffs

/-- Adding a common auxiliary variable preserves coefficientwise
nonnegativity. -/
theorem addAuxiliary {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : HasNonnegCoeffs P) : HasNonnegCoeffs (MvPolynomial.addAuxiliary P) := by
  apply hP.aeval
  intro i
  exact (X (some i)).add (X none)

/-- The denominator-cleared harmonic substitution preserves coefficientwise
nonnegativity. -/
theorem harmonicClear {Q : MvPolynomial (Fin 2) ℝ}
    (hQ : HasNonnegCoeffs Q) :
    HasNonnegCoeffs (MvPolynomial.harmonicClear Q) := by
  apply hQ.aeval
  intro i
  fin_cases i
  · exact ((X (some 0)).mul (X none)).mul ((X (some 1)).add (X none))
  · exact ((X (some 1)).mul (X none)).mul ((X (some 0)).add (X none))

/-- The BFJ auxiliary product has nonnegative coefficients when both inputs
do. -/
theorem bfjAuxiliary {P Q : MvPolynomial (Fin 2) ℝ}
    (hP : HasNonnegCoeffs P) (hQ : HasNonnegCoeffs Q) :
    HasNonnegCoeffs (MvPolynomial.bfjAuxiliary P Q) := by
  exact hP.addAuxiliary.mul hQ.harmonicClear

/-- The distinguished BFJ coefficient has nonnegative coefficients when both
inputs do. -/
theorem bfjCoefficient {P Q : MvPolynomial (Fin 2) ℝ}
    (hP : HasNonnegCoeffs P) (hQ : HasNonnegCoeffs Q) (b : ℕ) :
    HasNonnegCoeffs (MvPolynomial.bfjCoefficient P Q b) := by
  exact (hP.bfjAuxiliary hQ).optionEquivLeft_coeff (2 * b)

end HasNonnegCoeffs

end

end MvPolynomial

namespace RealRooted

noncomputable section

/-- Adding a common auxiliary variable preserves upper-half-plane
stability. -/
theorem MvUpperHalfPlaneStable.addAuxiliary
    {σ : Type*} {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStable (MvPolynomial.addAuxiliary P) := by
  intro w hw
  change MvPolynomial.aeval w
      (MvPolynomial.aeval (fun i => MvPolynomial.X (some i) +
        MvPolynomial.X none) P) ≠ 0
  rw [MvPolynomial.comp_aeval_apply]
  apply hP
  intro i
  simp only [map_add, MvPolynomial.aeval_X]
  change 0 < (w (some i) + w none).im
  simpa using add_pos (hw (some i)) (hw none)

/-- The BFJ auxiliary product is stable when both factors are stable and the
harmonic factor is homogeneous. -/
theorem MvUpperHalfPlaneStable.bfjAuxiliary
    {P Q : MvPolynomial (Fin 2) ℂ} {b : ℕ}
    (hP : MvUpperHalfPlaneStable P) (hQ : MvUpperHalfPlaneStable Q)
    (hhom : Q.IsHomogeneous b) :
    MvUpperHalfPlaneStable (MvPolynomial.bfjAuxiliary P Q) := by
  exact hP.addAuxiliary.mul (hQ.harmonicClear hhom)

/-- The distinguished coefficient of the stable BFJ auxiliary product is
zero or stable. -/
theorem MvUpperHalfPlaneStable.bfjCoefficient_zero_or
    {P Q : MvPolynomial (Fin 2) ℂ} {b : ℕ}
    (hP : MvUpperHalfPlaneStable P) (hQ : MvUpperHalfPlaneStable Q)
    (hhom : Q.IsHomogeneous b) :
    MvUpperHalfPlaneStableOrZero (MvPolynomial.bfjCoefficient P Q b) := by
  exact (hP.bfjAuxiliary hQ hhom).optionEquivLeft_coeff_zero_or_of_finite
    (2 * b)

end

end RealRooted
