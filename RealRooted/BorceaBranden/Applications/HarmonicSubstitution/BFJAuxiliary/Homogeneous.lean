import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJAuxiliary

/-!
# Scalar and homogeneous structure of the BFJ auxiliary product

This file records scalar-change compatibility and the homogeneous degrees of
the translated factor, denominator-cleared harmonic factor, auxiliary
product, and distinguished coefficient.
-/

namespace MvPolynomial

noncomputable section

/-- Mapping coefficients commutes with adding the common auxiliary
variable. -/
theorem map_addAuxiliary {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial σ R) :
    map f (addAuxiliary P) = addAuxiliary (map f P) := by
  simp only [addAuxiliary, aeval_def, algebraMap_eq]
  rw [map_eval₂]
  congr 1
  funext i
  simp

/-- Mapping coefficients commutes with the denominator-cleared harmonic
substitution. -/
theorem map_harmonicClear {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (Q : MvPolynomial (Fin 2) R) :
    map f (harmonicClear Q) = harmonicClear (map f Q) := by
  simp only [harmonicClear, aeval_def, algebraMap_eq]
  rw [map_eval₂]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Mapping coefficients commutes with the BFJ auxiliary product. -/
theorem map_bfjAuxiliary {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P Q : MvPolynomial (Fin 2) R) :
    map f (bfjAuxiliary P Q) = bfjAuxiliary (map f P) (map f Q) := by
  simp [bfjAuxiliary, map_addAuxiliary, map_harmonicClear]

/-- Mapping coefficients commutes with extracting the distinguished BFJ
coefficient. -/
theorem map_bfjCoefficient {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    map f (bfjCoefficient P Q b) =
      bfjCoefficient (map f P) (map f Q) b := by
  simp only [bfjCoefficient, map_optionEquivLeft_coeff, map_bfjAuxiliary]

namespace IsHomogeneous

/-- Adding the common auxiliary variable preserves homogeneous degree. -/
theorem addAuxiliary {R σ : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} {a : ℕ} (hP : P.IsHomogeneous a) :
    (MvPolynomial.addAuxiliary P).IsHomogeneous a := by
  simpa only [MvPolynomial.addAuxiliary, one_mul] using hP.aeval
    (fun i => X (some i) + X none)
    (fun i => (isHomogeneous_X R (some i)).add
      (isHomogeneous_X R none))

/-- The denominator-cleared harmonic substitution triples homogeneous
degree. -/
theorem harmonicClear {R : Type*} [CommSemiring R]
    {Q : MvPolynomial (Fin 2) R} {b : ℕ} (hQ : Q.IsHomogeneous b) :
    (MvPolynomial.harmonicClear Q).IsHomogeneous (3 * b) := by
  apply hQ.aeval
  intro i
  fin_cases i
  · simpa using
      ((isHomogeneous_X R (some 0)).mul (isHomogeneous_X R none)).mul
        ((isHomogeneous_X R (some 1)).add (isHomogeneous_X R none))
  · simpa using
      ((isHomogeneous_X R (some 1)).mul (isHomogeneous_X R none)).mul
        ((isHomogeneous_X R (some 0)).add (isHomogeneous_X R none))

/-- The BFJ auxiliary product has degree `a + 3 * b` when its inputs have
degrees `a` and `b`. -/
theorem bfjAuxiliary {R : Type*} [CommSemiring R]
    {P Q : MvPolynomial (Fin 2) R} {a b : ℕ}
    (hP : P.IsHomogeneous a) (hQ : Q.IsHomogeneous b) :
    (MvPolynomial.bfjAuxiliary P Q).IsHomogeneous (a + 3 * b) := by
  exact hP.addAuxiliary.mul hQ.harmonicClear

/-- The distinguished BFJ coefficient has homogeneous degree `a + b`. -/
theorem bfjCoefficient {R : Type*} [CommSemiring R]
    {P Q : MvPolynomial (Fin 2) R} {a b : ℕ}
    (hP : P.IsHomogeneous a) (hQ : Q.IsHomogeneous b) :
    (MvPolynomial.bfjCoefficient P Q b).IsHomogeneous (a + b) := by
  have haux : (MvPolynomial.bfjAuxiliary P Q).IsHomogeneous (a + 3 * b) :=
    hP.bfjAuxiliary hQ
  have hback :
      ((optionEquivLeft R (Fin 2)).symm
        (optionEquivLeft R (Fin 2) (MvPolynomial.bfjAuxiliary P Q))).IsHomogeneous
          (a + 3 * b) := by
    simpa using haux
  exact hback.coeff_isHomogeneous_of_optionEquivLeft_symm
    (2 * b) (a + b) (by lia)

end IsHomogeneous

end

end MvPolynomial
