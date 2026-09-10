import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJOutput
import RealRooted.BoundarySpecializationGeneral
import RealRooted.HermiteBiehler.Basic

/-!
# Stability of the BFJ output

This file derives weak univariate upper-half-plane stability of the
dehomogenized BFJ coefficient by specializing its second variable to one.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The dehomogenized BFJ coefficient is zero or upper-half-plane stable. -/
theorem MvUpperHalfPlaneStable.bfjOutput_zero_or
    {P Q : MvPolynomial (Fin 2) ℂ} {b : ℕ}
    (hP : MvUpperHalfPlaneStable P) (hQ : MvUpperHalfPlaneStable Q)
    (hhom : Q.IsHomogeneous b) :
    MvPolynomial.bfjOutput P Q b = 0 ∨
      IsUpperHalfPlaneStable (MvPolynomial.bfjOutput P Q b) := by
  have hcoeff := hP.bfjCoefficient_zero_or hQ hhom
  have hspec := hcoeff.specializeAt_real_general (1 : Fin 2) 1
  have hupdate (z : ℂ) :
      Function.update ![z, Complex.I] (1 : Fin 2) ((1 : ℝ) : ℂ) =
        ![z, (1 : ℂ)] := by
    funext i
    fin_cases i <;> simp
  rcases hspec with hzero | hstable
  · left
    apply Polynomial.funext
    intro z
    rw [MvPolynomial.eval_bfjOutput]
    have hz := congrArg (MvPolynomial.eval ![z, Complex.I]) hzero
    simp only [MvPolynomial.eval_specializeAt] at hz
    rw [hupdate] at hz
    simpa using hz
  · right
    intro z hz
    rw [MvPolynomial.eval_bfjOutput]
    have heval := hstable ![z, Complex.I] (by
      intro i
      fin_cases i
      · exact hz
      · norm_num)
    simp only [MvPolynomial.eval_specializeAt] at heval
    rw [hupdate] at heval
    exact heval

end

end RealRooted
