import RealRooted.BorceaBranden.Applications.ComplexUnivariateSymbol
import RealRooted.BorceaBranden.Applications.DegreeBoxPolarization
import RealRooted.HermiteBiehler

/-!
# Real univariate finite-symbol sufficiency

This module derives the real univariate positive-symbol implication from the
general complex degree-box theorem. It constructs the coefficientwise
complex-linear extension of a real polynomial operator, identifies its
algebraic symbol, and transports stable-or-zero output back to real splitting.
-/

open Polynomial BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

private def complexScalarMultiple (q : ℂ[X]) : ℂ →ₗ[ℂ] ℂ[X] where
  toFun a := C a * q
  map_add' a b := by simp [add_mul]
  map_smul' a b := by simp [smul_eq_C_mul, mul_assoc]

/-- The coefficientwise complex-linear extension of a real polynomial linear
map. It is characterized below by commuting with `complexify`. -/
noncomputable def complexificationLinearMap
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  Polynomial.lsum fun n => complexScalarMultiple (complexify (T (X ^ n)))

@[simp] theorem complexificationLinearMap_monomial
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) (a : ℂ) :
    complexificationLinearMap T (Polynomial.monomial n a) =
      C a * complexify (T (X ^ n)) := by
  simp [complexificationLinearMap, complexScalarMultiple]

private theorem complexify_smul (a : ℝ) (p : ℝ[X]) :
    complexify (a • p) = (a : ℂ) • complexify p := by
  ext n
  simp [complexify]

/-- Complex-linear extension agrees with the original real map on
complexified inputs. -/
@[simp] theorem complexificationLinearMap_complexify
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (p : ℝ[X]) :
    complexificationLinearMap T (complexify p) = complexify (T p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show complexify (p + q) = complexify p + complexify q by
        simp [complexify]]
      rw [(complexificationLinearMap T).map_add, hp, hq, T.map_add]
      simp [complexify]
  | monomial n a =>
      have hmono : (Polynomial.monomial n a : ℝ[X]) = a • X ^ n := by
        rw [smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hmono, complexify_smul, (complexificationLinearMap T).map_smul,
        T.map_smul, complexify_smul]
      congr 1
      rw [complexify, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.X_pow_eq_monomial, complexificationLinearMap_monomial]
      simp

/-- Embedding a complexified real polynomial in the first variable commutes
with multivariate complexification. -/
theorem complexPolynomialInFirstMv_complexify (p : ℝ[X]) :
    complexPolynomialInFirstMv (complexify p) =
      complexifyMv (Challenges.BorceaBranden.polynomialInFirstMv p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        complexPolynomialInFirstMv (complexify (p + q)) =
            complexPolynomialInFirstMv (complexify p) +
              complexPolynomialInFirstMv (complexify q) := by
          simp [complexPolynomialInFirstMv, complexify]
        _ = complexifyMv (Challenges.BorceaBranden.polynomialInFirstMv p) +
              complexifyMv (Challenges.BorceaBranden.polynomialInFirstMv q) := by
          rw [hp, hq]
        _ = complexifyMv
              (Challenges.BorceaBranden.polynomialInFirstMv (p + q)) := by
          simp [Challenges.BorceaBranden.polynomialInFirstMv, complexifyMv]
  | monomial n a =>
      calc
        complexPolynomialInFirstMv (complexify (Polynomial.monomial n a)) =
            MvPolynomial.C (a : ℂ) * MvPolynomial.X 0 ^ n := by
          simp [complexPolynomialInFirstMv, complexify]
        _ = complexifyMv
              (MvPolynomial.C a * MvPolynomial.X 0 ^ n) := by
          simp [complexifyMv]
        _ = complexifyMv
              (Challenges.BorceaBranden.polynomialInFirstMv
                (Polynomial.monomial n a)) := by
          simp [Challenges.BorceaBranden.polynomialInFirstMv]

/-- The usual finite symbol of a complexified real operator is the
coefficientwise complexification of its real finite symbol. -/
theorem complexFiniteAlgebraicSymbol_complexificationLinearMap
    (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    complexFiniteAlgebraicSymbol d (complexificationLinearMap T) =
      complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T) := by
  classical
  simp only [complexFiniteAlgebraicSymbol,
    Challenges.BorceaBranden.finiteAlgebraicSymbol, complexifyMv, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ((X : ℂ[X]) ^ k) = complexify ((X : ℝ[X]) ^ k) by
    simp [complexify]]
  rw [complexificationLinearMap_complexify]
  rw [complexPolynomialInFirstMv_complexify]
  simp [complexifyMv]

/-- The general degree-box algebraic symbol of a complexified real operator
is the renamed complexification of the real univariate symbol. -/
theorem algebraicSymbol_complexificationDegreeBoxOperator
    (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    MvPolynomial.algebraicSymbol (fun _ : Fin 1 => d)
        (complexUnivariateDegreeBoxOperator d (complexificationLinearMap T)) =
      MvPolynomial.rename finOneSumEquivFinTwo.symm
        (complexifyMv
          (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)) := by
  have h := congrArg (MvPolynomial.rename finOneSumEquivFinTwo.symm)
    (rename_algebraicSymbol_complexUnivariateDegreeBoxOperator d
      (complexificationLinearMap T))
  rw [complexFiniteAlgebraicSymbol_complexificationLinearMap] at h
  have hcomp : finOneSumEquivFinTwo.symm ∘ finOneSumToFinTwo = id := by
    funext i
    exact finOneSumEquivFinTwo.symm_apply_apply i
  rw [MvPolynomial.rename_rename, hcomp, MvPolynomial.rename_id] at h
  exact h

/-- Borcea--Branden positive-symbol sufficiency for real univariate operators.

This is a checked witness of the application-facing statement introduced by
issue #69. It is derived from `finiteSymbol_finOne_preserves_stability`, not
assumed as a backend and not routed through the false homogeneous symbol. -/
theorem finiteSymbolTheorem :
    Challenges.BorceaBranden.finiteSymbolTheoremStatement := by
  intro d T hSymbol p hdeg hp
  by_cases hp0 : p = 0
  · left
    simp [hp0]
  let fmv : MvPolynomial (Fin 1) ℂ :=
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)
  have hfmem : fmv ∈ MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) := by
    rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
    intro i
    rw [Subsingleton.elim i default]
    simpa [fmv] using
      (MvPolynomial.degreeOf_uniqueAlgEquiv_symm (σ := Fin 1)
        (complexify p)).trans_le (Polynomial.natDegree_map_le.trans hdeg)
  let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) := ⟨fmv, hfmem⟩
  have hfstable : MvUpperHalfPlaneStable f.1 := by
    simpa [f, fmv] using
      (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable (complexify p)).mp
        (Polynomial.Splits.isUpperHalfPlaneStable_complexify hp hp0)
  have hAlgSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun _ : Fin 1 => d)
        (complexUnivariateDegreeBoxOperator d (complexificationLinearMap T))) := by
    rw [algebraicSymbol_complexificationDegreeBoxOperator]
    exact hSymbol.rename
  have hout := finiteSymbol_finOne_preserves_stability d
    (complexUnivariateDegreeBoxOperator d (complexificationLinearMap T))
    hAlgSymbol f hfstable
  change MvUpperHalfPlaneStableOrZero
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
      (complexificationLinearMap T
        (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) f.1))) at hout
  have hfpoly :
      MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) f.1 = complexify p := by
    change MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)) =
      complexify p
    exact (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).apply_symm_apply (complexify p)
  rw [hfpoly, complexificationLinearMap_complexify] at hout
  rcases hout with hzero | hstable
  · left
    have hcomplex_zero : complexify (T p) = 0 := by
      apply (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.injective
      simpa using hzero
    exact (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hcomplex_zero
  · right
    apply IsUpperHalfPlaneStable.splits_complexify
    rw [isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable]
    simpa using hstable

/-- Direct application form of `finiteSymbolTheorem`. -/
theorem finiteSymbol_preservesRealRootedUpTo
    {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T))) :
    Challenges.BorceaBranden.PreservesRealRootedUpTo d T :=
  finiteSymbolTheorem hSymbol

end

end RealRooted.BorceaBranden
