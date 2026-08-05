/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.DegreeBox

/-!
# Finite algebraic symbols of multivariate linear operators

This file defines the algebraic symbol of a linear operator whose domain is a
coordinate-wise degree box. The output variables occupy the left block and the
domain variables occupy the right block.

## Main definitions

* `MvPolynomial.boxChoose`: the product of coordinate-wise binomial
  coefficients.
* `MvPolynomial.rightComplementMonomial`: the right-block monomial with
  exponent vector `κ - m`.
* `MvPolynomial.algebraicSymbol`: the finite algebraic symbol expanded in the
  monomial basis of `MvPolynomial.degreeOfLE`.
* `MvPolynomial.negRightVariablesHom`: substitution negating every right-block
  variable.
* `MvPolynomial.algebraicSymbolNegRight`: the sign-reversed symbol used in the
  real Borcea--Branden theorem.
-/

open scoped BigOperators

namespace MvPolynomial

public section AlgebraicSymbol

variable {σ τ R : Type*} [CommSemiring R] [Fintype σ]

/-- The product of the coordinate-wise binomial coefficients. -/
def boxChoose (κ : σ → ℕ) (m : σ →₀ ℕ) : ℕ :=
  ∏ i, Nat.choose (κ i) (m i)

/-- Every binomial coefficient in a multiaffine source box is one. -/
@[simp]
theorem boxChoose_one_of_le_one (m : σ →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
    boxChoose (fun _ : σ => 1) m = 1 := by
  classical
  simp only [boxChoose]
  apply Finset.prod_eq_one
  intro i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hm i) with h | h <;> simp [h]

/-- The right-block monomial with exponent vector `κ - m`. -/
noncomputable def rightComplementMonomial (κ : σ → ℕ) (m : σ →₀ ℕ) :
    MvPolynomial (τ ⊕ σ) R :=
  ∏ i, X (Sum.inr i) ^ (κ i - m i)

/-- Expand the right complementary monomial coordinate by coordinate. -/
theorem rightComplementMonomial_eq_prod (κ : σ → ℕ) (m : σ →₀ ℕ) :
    rightComplementMonomial (R := R) (τ := τ) κ m =
      ∏ i, X (Sum.inr i) ^ (κ i - m i) := by
  rfl

/-- In a multiaffine box, the complementary monomial is the product over the
complement of the exponent support. -/
theorem rightComplementMonomial_one_eq_support_compl [DecidableEq σ]
    (m : σ →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
    rightComplementMonomial (R := R) (τ := τ) (fun _ : σ => 1) m =
      rename (Sum.inr : σ → τ ⊕ σ) (∏ i ∈ m.supportᶜ, X i) := by
  rw [rightComplementMonomial_eq_prod]
  simp only [map_prod, rename_X]
  rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ m.support
  · have hmi : m i = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hm i) with hzero | hone
      · exact (Finsupp.mem_support_iff.mp hi hzero).elim
      · exact hone
    simp [hi, hmi]
  · have hmi : m i = 0 := Finsupp.notMem_support_iff.mp hi
    simp [hi, hmi]

/-- The finite algebraic symbol of a linear map on a coordinate-wise degree
box. Its monomial-basis expansion is
`Σ m, choose(κ, m) * T(X^m) * w^(κ-m)`. -/
noncomputable def algebraicSymbol (κ : σ → ℕ)
    (T : degreeOfLE σ R κ →ₗ[R] MvPolynomial τ R) :
    MvPolynomial (τ ⊕ σ) R :=
  ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
    C (boxChoose κ m.1 : R) *
      rename (Sum.inl : τ → τ ⊕ σ) (T (basisDegreeOfLE κ m)) *
        rightComplementMonomial κ m.1

/-- Expand the finite algebraic symbol in its bounded monomial basis. -/
theorem algebraicSymbol_eq_sum (κ : σ → ℕ)
    (T : degreeOfLE σ R κ →ₗ[R] MvPolynomial τ R) :
    algebraicSymbol κ T =
      ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
        C (boxChoose κ m.1 : R) *
          rename (Sum.inl : τ → τ ⊕ σ)
              (T (basisDegreeOfLE κ m)) *
            rightComplementMonomial κ m.1 := by
  rfl

@[simp]
theorem algebraicSymbol_zero (κ : σ → ℕ) :
    algebraicSymbol κ (0 : degreeOfLE σ R κ →ₗ[R] MvPolynomial τ R) = 0 := by
  classical
  simp [algebraicSymbol]

theorem algebraicSymbol_add (κ : σ → ℕ)
    (T U : degreeOfLE σ R κ →ₗ[R] MvPolynomial τ R) :
    algebraicSymbol κ (T + U) = algebraicSymbol κ T + algebraicSymbol κ U := by
  classical
  simp only [algebraicSymbol, LinearMap.add_apply, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

@[simp]
theorem algebraicSymbol_smul (κ : σ → ℕ) (r : R)
    (T : degreeOfLE σ R κ →ₗ[R] MvPolynomial τ R) :
    algebraicSymbol κ (r • T) = r • algebraicSymbol κ T := by
  classical
  simp only [algebraicSymbol, LinearMap.smul_apply, map_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [smul_eq_C_mul]
  ring

end AlgebraicSymbol

public section NegRight

variable {σ τ R : Type*} [CommRing R]

/-- Negate every variable in the right block and fix every variable in the
left block. -/
noncomputable def negRightVariablesHom :
    MvPolynomial (τ ⊕ σ) R →+* MvPolynomial (τ ⊕ σ) R :=
  eval₂Hom C (Sum.elim (fun i => X (Sum.inl i)) (fun i => -X (Sum.inr i)))

@[simp]
theorem negRightVariablesHom_C (r : R) :
    negRightVariablesHom (R := R) (σ := σ) (τ := τ) (C r) = C r := by
  simp [negRightVariablesHom]

@[simp]
theorem negRightVariablesHom_X_inl (i : τ) :
    negRightVariablesHom (R := R) (σ := σ) (X (Sum.inl i)) = X (Sum.inl i) := by
  simp [negRightVariablesHom]

@[simp]
theorem negRightVariablesHom_X_inr (i : σ) :
    negRightVariablesHom (R := R) (τ := τ) (X (Sum.inr i)) = -X (Sum.inr i) := by
  simp [negRightVariablesHom]

variable [Fintype σ]

/-- The sign-reversed algebraic symbol used in the real finite theorem. -/
noncomputable def algebraicSymbolNegRight (κ : σ → ℕ)
    (T : degreeOfLE σ R κ →ₗ[R] MvPolynomial τ R) :
    MvPolynomial (τ ⊕ σ) R :=
  negRightVariablesHom (algebraicSymbol κ T)

end NegRight

end MvPolynomial
