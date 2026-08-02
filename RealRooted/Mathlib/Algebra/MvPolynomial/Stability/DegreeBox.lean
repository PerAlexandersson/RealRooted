/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Coordinate-wise degree boxes for multivariate polynomials

This file defines the submodule of multivariate polynomials whose exponent in
each coordinate `i` is bounded by a possibly coordinate-dependent number
`κ i`. These boxes are the finite-dimensional domains used by algebraic symbols
of multivariate stability preservers.

## Main definitions

* `MvPolynomial.degreeOfLE`: the submodule supported on exponent vectors bounded
  coordinate-wise by `κ`.
* `MvPolynomial.basisDegreeOfLE`: its canonical monomial basis.
* `MvPolynomial.degreeOfLEIndexEquiv`: for finitely many variables, the bounded
  exponent vectors are equivalent to `∀ i, Fin (κ i + 1)`.
-/

namespace MvPolynomial

public section DegreeOfLE

variable {σ R : Type*} [CommSemiring R]

/-- Multivariate polynomials whose degree in coordinate `i` is at most `κ i`.

This is a coordinate-wise box bound, not a total-degree bound. -/
def degreeOfLE (σ : Type*) (R : Type*) [CommSemiring R] (κ : σ → ℕ) :
    Submodule R (MvPolynomial σ R) :=
  restrictSupport R {m | ∀ i, m i ≤ κ i}

theorem mem_degreeOfLE {κ : σ → ℕ} (p : MvPolynomial σ R) :
    p ∈ degreeOfLE σ R κ ↔ ∀ m ∈ p.support, ∀ i, m i ≤ κ i := by
  simp only [degreeOfLE, mem_restrictSupport_iff, Set.subset_def, Set.mem_setOf_eq,
    Finset.mem_coe]

theorem mem_degreeOfLE_iff_degreeOf {κ : σ → ℕ} (p : MvPolynomial σ R) :
    p ∈ degreeOfLE σ R κ ↔ ∀ i, p.degreeOf i ≤ κ i := by
  rw [mem_degreeOfLE]
  constructor
  · intro h i
    exact degreeOf_le_iff.mpr fun m hm => h m hm i
  · intro h m hm i
    exact degreeOf_le_iff.mp (h i) m hm

@[simp]
theorem monomial_mem_degreeOfLE {κ : σ → ℕ} {m : σ →₀ ℕ} {r : R} :
    monomial m r ∈ degreeOfLE σ R κ ↔ (∀ i, m i ≤ κ i) ∨ r = 0 := by
  rw [degreeOfLE, monomial_mem_restrictSupport]
  rfl

theorem degreeOfLE_mono {κ κ' : σ → ℕ} (h : κ ≤ κ') :
    degreeOfLE σ R κ ≤ degreeOfLE σ R κ' :=
  restrictSupport_mono R fun _ hm i => (hm i).trans (h i)

@[simp]
theorem degreeOfLE_const (n : ℕ) :
    degreeOfLE σ R (fun _ => n) = restrictDegree σ R n :=
  by
    ext p
    rw [mem_degreeOfLE, mem_restrictDegree]

/-- The canonical monomial basis of a coordinate-wise degree box. -/
noncomputable def basisDegreeOfLE (κ : σ → ℕ) :
    Module.Basis {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} R (degreeOfLE σ R κ) :=
  basisRestrictSupport R _

@[simp]
theorem coe_basisDegreeOfLE (κ : σ → ℕ) :
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) →
    ((basisDegreeOfLE (R := R) κ :
        {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} → degreeOfLE σ R κ) m :
      MvPolynomial σ R) = monomial m.1 1 :=
  fun m => by
    rw [← Module.Basis.repr_symm_single_one]
    exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

@[simp]
theorem basisDegreeOfLE_repr_apply (κ : σ → ℕ)
    (p : degreeOfLE σ R κ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    (basisDegreeOfLE κ).repr p m = coeff m.1 p.1 :=
  by
    classical
    let coeffLinear : degreeOfLE σ R κ →ₗ[R] R :=
      { toFun := fun q : degreeOfLE σ R κ => coeff m.1 q.1
        map_add' := fun _ _ => coeff_add _ _ _
        map_smul' := fun _ _ => coeff_smul _ _ _ }
    have h :
        coeffLinear =
          (Finsupp.lapply m :
            ({m : σ →₀ ℕ // ∀ i, m i ≤ κ i} →₀ R) →ₗ[R] R).comp
            (basisDegreeOfLE κ).repr.toLinearMap := by
      apply (basisDegreeOfLE κ).ext
      intro n
      by_cases hmn : m = n
      · subst n
        simp [coeffLinear]
      · have hnm' : n.1 ≠ m.1 := fun h => hmn (Subtype.ext h.symm)
        simp [coeffLinear, hmn, hnm']
    exact (LinearMap.congr_fun h p).symm

/-- A bounded exponent vector on finitely many variables is the same data as
choosing an exponent in `Fin (κ i + 1)` for every coordinate. -/
noncomputable def degreeOfLEIndexEquiv [Fintype σ] (κ : σ → ℕ) :
    {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} ≃ ∀ i, Fin (κ i + 1) where
  toFun m i := ⟨m.1 i, Nat.lt_succ_iff.mpr (m.2 i)⟩
  invFun m :=
    ⟨Finsupp.equivFunOnFinite.symm (fun i => (m i).1), fun i => by
      simpa using Nat.lt_succ_iff.mp (m i).2⟩
  left_inv m := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simp
  right_inv m := by
    funext i
    apply Fin.ext
    simp

noncomputable instance degreeOfLEIndexFintype [Fintype σ] (κ : σ → ℕ) :
    Fintype {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} := by
  classical
  exact Fintype.ofEquiv (∀ i, Fin (κ i + 1)) (degreeOfLEIndexEquiv κ).symm

noncomputable instance degreeOfLE_moduleFinite [Finite σ] (κ : σ → ℕ) :
    Module.Finite R (degreeOfLE σ R κ) := by
  letI := Fintype.ofFinite σ
  exact Module.Finite.of_basis (basisDegreeOfLE (R := R) κ)

end DegreeOfLE

end MvPolynomial
