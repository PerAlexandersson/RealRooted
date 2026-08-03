/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol

/-!
# Source-coordinate degrees of finite algebraic symbols

The source variables of the finite algebraic symbol have the coordinatewise
degrees prescribed by its degree box. In particular, a symbol for the
multiaffine box has degree at most one in every source coordinate, independently
of the degrees in its target variables.
-/

open scoped BigOperators

namespace MvPolynomial

public section

variable {sigma tau R : Type*} [CommSemiring R] [Fintype sigma]

/-- The finite algebraic symbol for the multiaffine degree box has degree at
most one in every source coordinate. No degree bound is imposed on the target
variables. -/
/- Borcea--Branden, arXiv:0809.0401, Section 1.1. In each summand of
`G_T(z,w)`, source variable `w_i` has exponent `κ i - α i`, hence at most
`κ i`; the renamed operator value uses only the output-variable block. -/
theorem degreeOf_algebraicSymbol_inr_le
    (κ : sigma → ℕ)
    (T : degreeOfLE sigma R κ →ₗ[R] MvPolynomial tau R)
    (i : sigma) :
    (algebraicSymbol κ T).degreeOf (Sum.inr i) ≤ κ i := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    rw [Subsingleton.elim (algebraicSymbol κ T) 0]
    simp
  · letI := hR
    rw [algebraicSymbol_eq_sum]
    refine (degreeOf_sum_le (Sum.inr i) Finset.univ fun m =>
      C (boxChoose κ m.1 : R) *
        rename (Sum.inl : tau → tau ⊕ sigma)
          (T (basisDegreeOfLE κ m)) *
            rightComplementMonomial κ m.1).trans ?_
    apply Finset.sup_le
    intro m _
    have hrename :
        (rename (Sum.inl : tau → tau ⊕ sigma)
          (T (basisDegreeOfLE κ m))).degreeOf (Sum.inr i) = 0 := by
      apply Nat.le_zero.mp
      rw [degreeOf_le_iff]
      intro d hd
      apply Nat.le_zero.mpr
      by_contra hdi
      have hmem : Sum.inr i ∈
          (rename (Sum.inl : tau → tau ⊕ sigma)
            (T (basisDegreeOfLE κ m))).vars := by
        rw [mem_vars_iff_mem_support]
        exact ⟨d, hd, Finsupp.mem_support_iff.mpr hdi⟩
      obtain ⟨j, _hj, hji⟩ := mem_vars_rename Sum.inl _ hmem
      exact Sum.inl_ne_inr hji
    have hleft :
        (C (boxChoose κ m.1 : R) *
          rename (Sum.inl : tau → tau ⊕ sigma)
            (T (basisDegreeOfLE κ m))).degreeOf (Sum.inr i) ≤ 0 := by
      exact (degreeOf_C_mul_le _ _ _).trans_eq hrename
    have hright :
        (rightComplementMonomial (R := R) (τ := tau)
          κ m.1).degreeOf (Sum.inr i) ≤ κ i := by
      rw [rightComplementMonomial_eq_prod]
      refine (degreeOf_prod_le (Sum.inr i) Finset.univ fun j =>
        X (Sum.inr j) ^ (κ j - m.1 j)).trans ?_
      calc
        ∑ j : sigma,
            (X (Sum.inr j) ^ (κ j - m.1 j) :
              MvPolynomial (tau ⊕ sigma) R).degreeOf (Sum.inr i) =
            κ i - m.1 i := by
              rw [Finset.sum_eq_single i]
              · simp
              · intro j hj hji
                rw [degreeOf_X_pow_of_ne]
                intro hij
                exact hji (Sum.inr_injective hij).symm
              · simp
        _ ≤ κ i := Nat.sub_le _ _
    exact (degreeOf_mul_le _ _ _).trans
      ((Nat.add_le_add hleft hright).trans_eq
        (Nat.zero_add (κ i)))

theorem degreeOf_algebraicSymbol_one_inr_le
    (T : degreeOfLE sigma R (fun _ => 1) →ₗ[R] MvPolynomial tau R)
    (i : sigma) :
    (algebraicSymbol (fun _ : sigma => 1) T).degreeOf (Sum.inr i) ≤ 1 := by
  exact degreeOf_algebraicSymbol_inr_le (fun _ : sigma => 1) T i

end

end MvPolynomial
