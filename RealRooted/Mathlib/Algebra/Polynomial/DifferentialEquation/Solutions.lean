/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Degree
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic

/-!
# Complete finite polynomial solution spaces

We restrict coefficients to the natural roots of the leading degree polynomial.
This gives an injective map on the polynomial kernel and the dimension bound by
the order of a nonzero differential operator. A separate finite matrix identity
uses all coefficients up to a proven degree bound.
Source: unpublished proof notes in RealRooted issue #2343, Theorem 1 and equation (7).
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [CharZero K]

open Classical in
/-- The finite set of natural-number roots of a degree polynomial. -/
@[expose] noncomputable def odeDegrees (A : ℕ → K[X]) (d : ℕ) (h : ℤ) : Finset ℕ :=
  (odeDegreePolynomial A d h).roots.toFinset.preimage
    (Nat.cast : ℕ → K) Nat.cast_injective.injOn

/-- Membership in the possible-degree set, for a nonzero degree polynomial. -/
theorem mem_odeDegrees_iff (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hI : odeDegreePolynomial A d h ≠ 0) (m : ℕ) :
    m ∈ odeDegrees A d h ↔ (odeDegreePolynomial A d h).eval (m : K) = 0 := by
  classical
  simp [odeDegrees, mem_roots hI, IsRoot.def]

/-- There are at most `d` possible degrees, irrespective of their numerical size. -/
theorem card_odeDegrees_le (A : ℕ → K[X]) (d : ℕ) (h : ℤ) :
    (odeDegrees A d h).card ≤ d := by
  classical
  unfold odeDegrees
  rw [Finset.card_preimage]
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (natDegree_odeDegreePolynomial_le A d h)))

/-- Coefficients at a finite set of indices, restricted to a polynomial kernel. -/
@[expose] noncomputable def solutionCoefficientMap (L : K[X] →ₗ[K] K[X]) (E : Finset ℕ) :
    LinearMap.ker L →ₗ[K] (E → K) :=
  LinearMap.pi fun m => (lcoeff K m).comp (LinearMap.ker L).subtype

omit [CharZero K] in
/-- A polynomial subspace is determined by coefficients at any set containing
the degree of each of its nonzero elements. -/
theorem solutionCoefficientMap_injective
    (L : K[X] →ₗ[K] K[X]) (E : Finset ℕ)
    (hdeg : ∀ p : K[X], p ≠ 0 → L p = 0 → p.natDegree ∈ E) :
    Function.Injective (solutionCoefficientMap L E) := by
  intro p q heq
  apply Subtype.ext
  by_contra hpq
  have hr : (p : K[X]) - q ≠ 0 := sub_ne_zero.mpr hpq
  have hker : L ((p : K[X]) - q) = 0 := by
    rw [map_sub, p.property, q.property, sub_self]
  let m : E := ⟨((p : K[X]) - q).natDegree, hdeg _ hr hker⟩
  have hc := congrFun heq m
  change (p : K[X]).coeff m = (q : K[X]).coeff m at hc
  exact (leadingCoeff_ne_zero.mpr hr) (by
    rw [leadingCoeff, coeff_sub]
    exact sub_eq_zero.mpr hc)

/-- Coefficients at the natural roots of a nonzero leading degree polynomial
injectively determine every polynomial solution. -/
theorem solutionCoefficientMap_differentialOperator_injective
    (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    (hI : odeDegreePolynomial A d h ≠ 0) :
    Function.Injective (solutionCoefficientMap (differentialOperator A d) (odeDegrees A d h)) := by
  apply solutionCoefficientMap_injective
  intro p hp hode
  exact (mem_odeDegrees_iff A d h hI p.natDegree).mpr
    (eval_odeDegreePolynomial_natDegree_eq_zero A d h hA hp hode)

/-- The polynomial kernel of a nonzero finite scalar differential operator is finite dimensional. -/
theorem finiteDimensional_ker_differentialOperator
    (A : ℕ → K[X]) (d : ℕ) (hne : ∃ j ∈ Finset.range (d + 1), A j ≠ 0) :
    FiniteDimensional K (LinearMap.ker (differentialOperator A d)) := by
  exact FiniteDimensional.of_injective
    (solutionCoefficientMap (differentialOperator A d) (odeDegrees A d (odeDegreeShift A d hne)))
    (solutionCoefficientMap_differentialOperator_injective A d _
      (fun j hj hAj => natDegree_sub_le_odeDegreeShift A d hne hj hAj)
      (odeDegreePolynomial_odeDegreeShift_ne_zero A d hne))

/-- The dimension is at most the number of natural roots of the leading degree polynomial. -/
theorem finrank_ker_differentialOperator_le_card
    (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    (hI : odeDegreePolynomial A d h ≠ 0) :
    Module.finrank K (LinearMap.ker (differentialOperator A d)) ≤ (odeDegrees A d h).card := by
  simpa using LinearMap.finrank_le_finrank_of_injective
    (solutionCoefficientMap_differentialOperator_injective A d h hA hI)

/-- A nonzero scalar differential operator has polynomial kernel dimension at most its order. -/
theorem finrank_ker_differentialOperator_le
    (A : ℕ → K[X]) (d : ℕ) (hne : ∃ j ∈ Finset.range (d + 1), A j ≠ 0) :
    Module.finrank K (LinearMap.ker (differentialOperator A d)) ≤ d := by
  exact (finrank_ker_differentialOperator_le_card A d (odeDegreeShift A d hne)
    (fun j hj hAj => natDegree_sub_le_odeDegreeShift A d hne hj hAj)
    (odeDegreePolynomial_odeDegreeShift_ne_zero A d hne)).trans (card_odeDegrees_le A d _)

omit [CharZero K] in
/-- If all nonzero solutions have the same degree, its coefficient determines a solution. -/
theorem eq_of_linearMap_eq_zero_of_coeff_eq
    (L : K[X] →ₗ[K] K[X]) (N : ℕ)
    (hdeg : ∀ p : K[X], p ≠ 0 → L p = 0 → p.natDegree = N)
    {p q : K[X]} (hp : L p = 0)
    (hq : L q = 0) (hc : p.coeff N = q.coeff N) : p = q := by
  have hinj := solutionCoefficientMap_injective L {N}
    (fun p hp hode => by simp [hdeg p hp hode])
  have heq : solutionCoefficientMap L {N} ⟨p, hp⟩ =
      solutionCoefficientMap L {N} ⟨q, hq⟩ := by
    ext m
    have hm : (m : ℕ) = N := Finset.mem_singleton.mp m.property
    simpa [solutionCoefficientMap, hm] using hc
  exact congrArg Subtype.val (hinj heq)

omit [CharZero K] in
/-- Coefficients of a differential operator on a monomial, with negative indices
represented by an explicit zero branch. -/
theorem coeff_differentialOperator_X_pow
    (A : ℕ → K[X]) (d k ℓ : ℕ) :
    (differentialOperator A d (X ^ k)).coeff ℓ =
      ∑ j ∈ Finset.range (d + 1), (k.descFactorial j : K) *
        if k - j ≤ ℓ then (A j).coeff (ℓ - (k - j)) else 0 := by
  rw [differentialOperator, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iterate_derivative_X_pow_eq_C_mul]
  rw [show A j * (C (k.descFactorial j : K) * X ^ (k - j)) =
    C (k.descFactorial j : K) * (A j * X ^ (k - j)) by ring,
    coeff_C_mul, coeff_mul_X_pow']

/-- The exact finite matrix for a degree bound `N` and coefficient-degree bound `a`. -/
@[expose] noncomputable def odeCoefficientMatrix
    (A : ℕ → K[X]) (d N a : ℕ) : Matrix (Fin (N + a + 1)) (Fin (N + 1)) K :=
  fun ℓ k => (differentialOperator A d (X ^ (k : ℕ))).coeff ℓ

omit [CharZero K] in
/-- The matrix-vector product agrees with the ODE coefficients for every polynomial
of degree at most `N`. -/
theorem odeCoefficientMatrix_mulVec
    (A : ℕ → K[X]) (d N a : ℕ) {p : K[X]} (hp : p.natDegree ≤ N)
    (ℓ : Fin (N + a + 1)) :
    (odeCoefficientMatrix A d N a).mulVec (fun k => p.coeff k) ℓ =
      (differentialOperator A d p).coeff ℓ := by
  have hexp : p = ∑ k ∈ Finset.range (N + 1), p.coeff k • (X ^ k : K[X]) := by
    simpa only [smul_eq_C_mul] using p.as_sum_range_C_mul_X_pow' (by lia : p.natDegree < N + 1)
  conv_rhs => rw [hexp]
  simp only [map_sum, map_smul, finsetSum_coeff, AddMonoidAlgebra.coeff_smul_apply]
  change (∑ k : Fin (N + 1),
    (differentialOperator A d (X ^ (k : ℕ))).coeff ℓ * p.coeff k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (differentialOperator A d (X ^ k)).coeff ℓ * p.coeff k) (N + 1)]
  simp only [smul_eq_mul, mul_comm]

omit [CharZero K] in
/-- The full finite matrix equation is equivalent to the polynomial ODE, once
valid bounds on the polynomial and the coefficient polynomials are supplied. -/
theorem differentialOperator_eq_zero_iff_matrix_mulVec_eq_zero
    (A : ℕ → K[X]) (d N a : ℕ)
    (hA : ∀ j ∈ Finset.range (d + 1), (A j).natDegree ≤ a)
    {p : K[X]} (hp : p.natDegree ≤ N) :
    differentialOperator A d p = 0 ↔
      (odeCoefficientMatrix A d N a).mulVec (fun k => p.coeff k) = 0 := by
  have hdeg : (differentialOperator A d p).natDegree ≤ N + a := by
    change (∑ j ∈ Finset.range (d + 1), A j * derivative^[j] p).natDegree ≤ N + a
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hder := natDegree_iterate_derivative p j
    exact natDegree_mul_le.trans (by have := hA j hj; lia)
  constructor
  · intro hz
    ext ℓ
    rw [odeCoefficientMatrix_mulVec A d N a hp ℓ, hz, coeff_zero]
    rfl
  · intro hz
    ext ℓ
    by_cases hℓ : ℓ < N + a + 1
    · have hc := congrFun hz ⟨ℓ, hℓ⟩
      simpa only [odeCoefficientMatrix_mulVec A d N a hp, Pi.zero_apply, coeff_zero] using hc
    · exact coeff_eq_zero_of_natDegree_lt (by lia)

/-- A bound on the possible-degree set bounds every polynomial solution,
including the zero polynomial. -/
theorem natDegree_le_of_differentialOperator_eq_zero
    (A : ℕ → K[X]) (d N : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    (hI : odeDegreePolynomial A d h ≠ 0)
    (hN : ∀ m ∈ odeDegrees A d h, m ≤ N)
    {p : K[X]} (hode : differentialOperator A d p = 0) : p.natDegree ≤ N := by
  by_cases hp : p = 0
  · simp [hp]
  exact hN p.natDegree ((mem_odeDegrees_iff A d h hI _).mpr
    (eval_odeDegreePolynomial_natDegree_eq_zero A d h hA hp hode))

/-- An empty possible-degree set forces the polynomial kernel to be zero. -/
theorem eq_zero_of_odeDegrees_eq_empty
    (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    (hI : odeDegreePolynomial A d h ≠ 0) (hE : odeDegrees A d h = ∅)
    {p : K[X]} (hode : differentialOperator A d p = 0) : p = 0 := by
  by_contra hp
  have hm := (mem_odeDegrees_iff A d h hI _).mpr
    (eval_odeDegreePolynomial_natDegree_eq_zero A d h hA hp hode)
  rw [hE] at hm
  exact Finset.notMem_empty _ hm

/-- Singleton possible degrees give recognition from a single coefficient. -/
theorem eq_of_odeDegrees_eq_singleton
    (A : ℕ → K[X]) (d N : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    (hI : odeDegreePolynomial A d h ≠ 0) (hE : odeDegrees A d h = {N})
    {p q : K[X]} (hp : differentialOperator A d p = 0)
    (hq : differentialOperator A d q = 0) (hc : p.coeff N = q.coeff N) : p = q := by
  apply eq_of_linearMap_eq_zero_of_coeff_eq (differentialOperator A d) N ?_ hp hq hc
  intro r hr hode
  have hm := (mem_odeDegrees_iff A d h hI _).mpr
    (eval_odeDegreePolynomial_natDegree_eq_zero A d h hA hr hode)
  simpa only [hE, Finset.mem_singleton] using hm

omit [CharZero K] in
/-- All solutions of an inhomogeneous equation form a translate of its homogeneous kernel. -/
theorem differentialOperator_eq_iff_sub_mem_ker
    (A : ℕ → K[X]) (d : ℕ) {p q f : K[X]}
    (hq : differentialOperator A d q = f) :
    differentialOperator A d p = f ↔ p - q ∈ LinearMap.ker (differentialOperator A d) := by
  simp only [LinearMap.mem_ker, map_sub, hq, sub_eq_zero]

end Polynomial
