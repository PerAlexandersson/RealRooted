import RealRooted.BorceaBranden.Applications.UnivariateSymbol

/-!
# Complex univariate finite algebraic symbols

This module contains the complex-univariate degree-box infrastructure shared by
general real-operator complexification and specialized operator applications.
-/

noncomputable section

namespace RealRooted.BorceaBranden

open Polynomial
open scoped BigOperators

/-- Regard a complex univariate polynomial as a bivariate polynomial in the
first variable. -/
def complexPolynomialInFirstMv (p : ℂ[X]) : MvPolynomial (Fin 2) ℂ :=
  p.eval₂ (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
    (MvPolynomial.X (0 : Fin 2))

/-- Complex finite algebraic symbol of a complex-linear univariate operator. -/
def complexFiniteAlgebraicSymbol (d : ℕ) (T : ℂ[X] →ₗ[ℂ] ℂ[X]) :
    MvPolynomial (Fin 2) ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    MvPolynomial.C (Nat.choose d k : ℂ) *
      complexPolynomialInFirstMv (T ((X : ℂ[X]) ^ k)) *
        MvPolynomial.X (1 : Fin 2) ^ (d - k)

/-- Restrict a complex univariate operator to the degree-`d` box. -/
def complexUnivariateDegreeBoxOperator (d : ℕ)
    (T : ℂ[X] →ₗ[ℂ] ℂ[X]) :
    MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) →ₗ[ℂ]
      MvPolynomial (Fin 1) ℂ where
  toFun p :=
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
      (T (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) p.1))
  map_add' p q := by simp
  map_smul' c p := by simp

lemma rename_uniqueAlgEquiv_symm_eq_complexPolynomialInFirstMv (p : ℂ[X]) :
    MvPolynomial.rename finOneSumToFinTwo
        (MvPolynomial.rename (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
          ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p)) =
      complexPolynomialInFirstMv p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, complexPolynomialInFirstMv, Polynomial.eval₂_add] using
        congrArg₂ (· + ·) hp hq
  | monomial n a =>
      have h := MvPolynomial.uniqueAlgEquiv_symm_monomial
        (R := ℂ) (σ := Fin 1) (d := Finsupp.single 0 n) (r := a)
      rw [show (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
        (Polynomial.monomial n a) =
          MvPolynomial.monomial (Finsupp.single 0 n) a by simpa using h]
      simp [complexPolynomialInFirstMv, finOneSumToFinTwo,
        MvPolynomial.monomial_eq]

lemma rename_rightComplementMonomial_finOne_complex (d : ℕ)
    (m : Fin 1 →₀ ℕ) :
    MvPolynomial.rename finOneSumToFinTwo
        (MvPolynomial.rightComplementMonomial
          (R := ℂ) (τ := Fin 1) (fun _ : Fin 1 => d) m) =
      MvPolynomial.X (1 : Fin 2) ^ (d - m 0) := by
  simp [MvPolynomial.rightComplementMonomial, finOneSumToFinTwo]

lemma complexUnivariateDegreeBoxOperator_basis (d : ℕ)
    (T : ℂ[X] →ₗ[ℂ] ℂ[X])
    (m : {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ d}) :
    complexUnivariateDegreeBoxOperator d T
      (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => d) m) =
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
        (T (Polynomial.X ^ m.1 0)) := by
  change (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
      (T (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        ((MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => d) m :
          MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d)) :
            MvPolynomial (Fin 1) ℂ))) = _
  rw [MvPolynomial.coe_basisDegreeOfLE,
    MvPolynomial.uniqueAlgEquiv_monomial]
  simp [Polynomial.X_pow_eq_monomial]

/-- The genuine algebraic symbol of a complex univariate degree-box operator
is its usual finite algebraic symbol after identifying the two singleton
variable blocks with `Fin 2`. -/
theorem rename_algebraicSymbol_complexUnivariateDegreeBoxOperator
    (d : ℕ) (T : ℂ[X] →ₗ[ℂ] ℂ[X]) :
    MvPolynomial.rename finOneSumToFinTwo
        (MvPolynomial.algebraicSymbol (fun _ : Fin 1 => d)
          (complexUnivariateDegreeBoxOperator d T)) =
      complexFiniteAlgebraicSymbol d T := by
  classical
  rw [MvPolynomial.algebraicSymbol, map_sum]
  let g : ℕ → MvPolynomial (Fin 2) ℂ := fun k =>
    MvPolynomial.C (Nat.choose d k : ℂ) *
      complexPolynomialInFirstMv (T (Polynomial.X ^ k)) *
        MvPolynomial.X 1 ^ (d - k)
  calc
    ∑ m : {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ d},
        MvPolynomial.rename finOneSumToFinTwo
          (MvPolynomial.C
              (MvPolynomial.boxChoose (fun _ : Fin 1 => d) m.1 : ℂ) *
            MvPolynomial.rename (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
              (complexUnivariateDegreeBoxOperator d T
                (MvPolynomial.basisDegreeOfLE
                  (R := ℂ) (fun _ : Fin 1 => d) m)) *
            MvPolynomial.rightComplementMonomial
              (R := ℂ) (τ := Fin 1) (fun _ : Fin 1 => d) m.1) =
      ∑ m : {m : Fin 1 →₀ ℕ // ∀ i, m i ≤ d}, g (m.1 0) := by
        apply Fintype.sum_congr
        intro m
        simp only [map_mul, MvPolynomial.rename_C]
        rw [complexUnivariateDegreeBoxOperator_basis,
          rename_uniqueAlgEquiv_symm_eq_complexPolynomialInFirstMv,
          rename_rightComplementMonomial_finOne_complex]
        simp [g, MvPolynomial.boxChoose]
    _ = ∑ k : Fin (d + 1), g k := by
      apply Fintype.sum_equiv (degreeOfLEFinOneEquiv d)
      intro m
      simp [g, degreeOfLEFinOneEquiv_val]
    _ = complexFiniteAlgebraicSymbol d T := by
      simpa [g, complexFiniteAlgebraicSymbol] using
        Fin.sum_univ_eq_sum_range g (d + 1)

/-- Identify the left and right singleton blocks with variables `0` and `1`. -/
def finOneSumEquivFinTwo : Fin 1 ⊕ Fin 1 ≃ Fin 2 where
  toFun := finOneSumToFinTwo
  invFun := Fin.cases (Sum.inl 0) (fun _ => Sum.inr 0)
  left_inv i := by
    rcases i with i | i
    · rw [Subsingleton.elim i 0]
      rfl
    · rw [Subsingleton.elim i 0]
      rfl
  right_inv i := by fin_cases i <;> rfl

end RealRooted.BorceaBranden
