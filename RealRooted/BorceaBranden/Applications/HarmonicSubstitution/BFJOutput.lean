import RealRooted.Basic.Coefficients.Multivariate
import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJAuxiliary.Homogeneous
import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic

/-!
# Dehomogenized BFJ output

This file packages the univariate polynomial obtained by setting the second
variable of the distinguished BFJ coefficient to one. It records the generic
scalar, degree, and coefficient-sign interfaces used by the numerator-product
argument.
-/

open Polynomial

namespace MvPolynomial

noncomputable section

/-- Dehomogenize the distinguished BFJ coefficient by evaluating it at
`(X, 1)`. -/
def bfjOutput {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) (b : ℕ) : R[X] :=
  MvPolynomial.aeval ![Polynomial.X, 1] (bfjCoefficient P Q b)

/-- The BFJ output is the affine-line restriction that sets the second
variable to one. -/
theorem bfjOutput_eq_affineLineRestriction
    {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput P Q b =
      affineLineRestriction ![0, 1] ![1, 0] (bfjCoefficient P Q b) := by
  unfold bfjOutput affineLineRestriction
  simp only [aeval_def]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Mapping coefficients commutes with the dehomogenized BFJ output. -/
theorem map_bfjOutput {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    Polynomial.map f (bfjOutput P Q b) =
      bfjOutput (map f P) (map f Q) b := by
  unfold bfjOutput
  rw [← map_bfjCoefficient]
  simp only [aeval_def]
  change (Polynomial.mapRingHom f)
      (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]
        (bfjCoefficient P Q b)) =
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]
      (MvPolynomial.map f (bfjCoefficient P Q b))
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
  congr 1
  apply MvPolynomial.ringHom_ext'
  · ext r
    simp
  · intro i
    fin_cases i <;> simp

/-- Homogeneous input degrees bound the degree of the dehomogenized BFJ
output. -/
theorem natDegree_bfjOutput_le {R : Type*} [CommSemiring R]
    {P Q : MvPolynomial (Fin 2) R} {a b : ℕ}
    (hP : P.IsHomogeneous a) (hQ : Q.IsHomogeneous b) :
    (bfjOutput P Q b).natDegree ≤ a + b := by
  have hhom := hP.bfjCoefficient hQ
  have hdegree := hhom.natDegree_affineLineRestriction_le ![0, 1] ![1, 0]
  rw [bfjOutput_eq_affineLineRestriction]
  exact hdegree

namespace HasNonnegCoeffs

/-- Dehomogenizing the distinguished BFJ coefficient preserves
coefficientwise nonnegativity. -/
theorem bfjOutput {P Q : MvPolynomial (Fin 2) ℝ}
    (hP : HasNonnegCoeffs P) (hQ : HasNonnegCoeffs Q) (b : ℕ) :
    RealRooted.HasNonnegCoeffs (MvPolynomial.bfjOutput P Q b) := by
  exact (hP.bfjCoefficient hQ b).aeval_X_one

end HasNonnegCoeffs

end

end MvPolynomial
