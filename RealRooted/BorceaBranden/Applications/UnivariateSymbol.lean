import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
import RealRooted.BorceaBranden.FiniteSymbolBasis
import RealRooted.BorceaBranden.UnivariateFiniteSymbol

/-!
# Univariate compatibility for finite algebraic symbols

This file identifies the general coordinate-box algebraic symbol with the
existing univariate finite-symbol challenge normalization. It remains outside
the Mathlib-shaped core to avoid an application-layer import cycle.
-/

open Polynomial BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

open _root_.MvPolynomial

/-- Identify the left and right singleton blocks with variables `0` and `1`. -/
def finOneSumToFinTwo : Fin 1 ⊕ Fin 1 → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Restrict a univariate operator to the degree-`d` box, expressed in one
multivariate variable. -/
noncomputable def univariateDegreeBoxOperator (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    degreeOfLE (Fin 1) ℝ (fun _ => d) →ₗ[ℝ] MvPolynomial (Fin 1) ℝ where
  toFun p :=
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm
      (T (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p.1))
  map_add' p q := by simp
  map_smul' r p := by simp

lemma rename_uniqueAlgEquiv_symm_eq_polynomialInFirstMv (p : ℝ[X]) :
    rename finOneSumToFinTwo
        (rename (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
          ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm p)) =
      polynomialInFirstMv p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, polynomialInFirstMv, Polynomial.eval₂_add] using
        congrArg₂ (· + ·) hp hq
  | monomial n a =>
      have h := MvPolynomial.uniqueAlgEquiv_symm_monomial
        (R := ℝ) (σ := Fin 1) (d := Finsupp.single 0 n) (r := a)
      rw [show (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm
        (Polynomial.monomial n a) =
          MvPolynomial.monomial (Finsupp.single 0 n) a by simpa using h]
      simp [polynomialInFirstMv, finOneSumToFinTwo, MvPolynomial.monomial_eq]

lemma rename_rightComplementMonomial_finOne (d : ℕ) (m : Fin 1 →₀ ℕ) :
    rename finOneSumToFinTwo
        (rightComplementMonomial (R := ℝ) (τ := Fin 1) (fun _ : Fin 1 => d) m) =
      X (1 : Fin 2) ^ (d - m 0) := by
  simp [rightComplementMonomial, finOneSumToFinTwo]

lemma univariateDegreeBoxOperator_basis (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (m : {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ d}) :
    univariateDegreeBoxOperator d T
      (basisDegreeOfLE (R := ℝ) (fun _ : Fin 1 => d) m) =
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm
        (T (Polynomial.X ^ m.1 0)) := by
  change (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm
      (T (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
        ((basisDegreeOfLE (R := ℝ) (fun _ : Fin 1 => d) m :
          degreeOfLE (Fin 1) ℝ (fun _ => d)) : MvPolynomial (Fin 1) ℝ))) = _
  rw [coe_basisDegreeOfLE, MvPolynomial.uniqueAlgEquiv_monomial]
  simp [Polynomial.X_pow_eq_monomial]

end

end RealRooted.BorceaBranden
