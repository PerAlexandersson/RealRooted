/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# Degree restrictions for polynomial differential equations

The degree polynomial is the highest coefficient diagonal of the differential
operator, expressed in the falling-factorial basis. Its shift is an integer;
negative shifts, including the case in which the putative output degree is
negative, are included.
Source: unpublished proof notes in RealRooted issue #2343, Theorem 1.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- A finite scalar differential operator, including zero coefficient polynomials. -/
@[expose] noncomputable def differentialOperator (A : ℕ → K[X]) (d : ℕ) :
    K[X] →ₗ[K] K[X] where
  toFun p := ∑ j ∈ Finset.range (d + 1), A j * derivative^[j] p
  map_add' p q := by
    simp [← pow_apply_eq_iterate, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    simp [iterate_derivative_smul, Finset.smul_sum]

/-- The degree shift of a nonzero finite scalar differential operator. -/
@[expose] noncomputable def odeDegreeShift (A : ℕ → K[X]) (d : ℕ)
    (hne : ∃ j ∈ Finset.range (d + 1), A j ≠ 0) : ℤ := by
  classical
  exact ((Finset.range (d + 1)).filter (A · ≠ 0)).sup'
    (by simpa only [Finset.nonempty_def, Finset.mem_filter, exists_prop] using hne)
    (fun j => ((A j).natDegree : ℤ) - j)

/-- Every nonzero coefficient lies below the maximal degree diagonal. -/
theorem natDegree_sub_le_odeDegreeShift (A : ℕ → K[X]) (d : ℕ)
    (hne : ∃ j ∈ Finset.range (d + 1), A j ≠ 0)
    {j : ℕ} (hj : j ∈ Finset.range (d + 1)) (hAj : A j ≠ 0) :
    ((A j).natDegree : ℤ) - j ≤ odeDegreeShift A d hne := by
  classical
  exact Finset.le_sup' (fun j => ((A j).natDegree : ℤ) - j)
    (Finset.mem_filter.mpr ⟨hj, hAj⟩)

/-- The degree polynomial on a specified integer diagonal. For the leading
diagonal, use `odeDegreeShift`. Zero coefficient polynomials are excluded. -/
@[expose] noncomputable def odeDegreePolynomial (A : ℕ → K[X]) (d : ℕ) (h : ℤ) : K[X] := by
  classical
  exact ∑ j ∈ (Finset.range (d + 1)).filter
      (fun j => A j ≠ 0 ∧ ((A j).natDegree : ℤ) - j = h),
    C (A j).leadingCoeff * descPochhammer K j

open Classical in
/-- Natural-number evaluation of the degree polynomial. -/
theorem eval_odeDegreePolynomial (A : ℕ → K[X]) (d m : ℕ) (h : ℤ) :
    (odeDegreePolynomial A d h).eval (m : K) =
      ∑ j ∈ (Finset.range (d + 1)).filter
        (fun j => A j ≠ 0 ∧ ((A j).natDegree : ℤ) - j = h),
        (A j).leadingCoeff * (m.descFactorial j : K) := by
  classical
  simp [odeDegreePolynomial, eval_finsetSum, descPochhammer_eval_eq_descFactorial]

open Classical in
/-- One summand on the maximal degree diagonal, at a nonnegative output index. -/
private theorem coeff_mul_iterate_derivative_top
    (A p : K[X]) (j N : ℕ) (h : ℤ)
    (hN : (N : ℤ) = p.natDegree + h)
    (hA : A ≠ 0 → (A.natDegree : ℤ) - j ≤ h) :
    (A * derivative^[j] p).coeff N =
      if A ≠ 0 ∧ (A.natDegree : ℤ) - j = h then
        A.leadingCoeff * (p.natDegree.descFactorial j : K) * p.leadingCoeff else 0 := by
  by_cases hAj : A = 0
  · simp [hAj]
  by_cases hj : j ≤ p.natDegree
  · have hd := natDegree_iterate_derivative p j
    by_cases heq : (A.natDegree : ℤ) - j = h
    · rw [ite_eq_left ⟨hAj, heq⟩]
      have hN' : N = A.natDegree + (p.natDegree - j) := by lia
      rw [hN', coeff_mul_add_eq_of_natDegree_le le_rfl hd, coeff_natDegree,
        coeff_iterate_derivative, Nat.sub_add_cancel hj, nsmul_eq_mul, coeff_natDegree]
      ring
    · rw [ite_eq_right (by simp [heq])]
      apply coeff_eq_zero_of_natDegree_lt
      have := natDegree_mul_le (p := A) (q := derivative^[j] p)
      have := hA hAj
      lia
  · have hj' : p.natDegree < j := by lia
    rw [iterate_derivative_eq_zero hj', mul_zero, coeff_zero,
      Nat.descFactorial_of_lt hj']
    simp

/-- The leading-diagonal coefficient identity when the output exponent is nonnegative. -/
theorem coeff_differentialOperator_top (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    (p : K[X]) (N : ℕ) (hN : (N : ℤ) = p.natDegree + h) :
    (differentialOperator A d p).coeff N =
      (odeDegreePolynomial A d h).eval (p.natDegree : K) * p.leadingCoeff := by
  classical
  rw [differentialOperator, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff,
    eval_odeDegreePolynomial, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_mul_iterate_derivative_top _ _ _ _ _ hN (hA j hj)]

/-- If the putative leading output exponent is negative, every falling factorial
on the leading diagonal already vanishes. -/
theorem eval_odeDegreePolynomial_eq_zero_of_add_neg
    (A : ℕ → K[X]) (d m : ℕ) (h : ℤ) (hm : (m : ℤ) + h < 0) :
    (odeDegreePolynomial A d h).eval (m : K) = 0 := by
  classical
  rw [eval_odeDegreePolynomial]
  apply Finset.sum_eq_zero
  intro j hj
  have heq := (Finset.mem_filter.mp hj).2.2
  have hjm : m < j := by lia
  simp [Nat.descFactorial_of_lt hjm]

/-- The degree of every nonzero homogeneous polynomial solution is a natural root
of the degree polynomial. Both signs of the integer shift are allowed. -/
theorem eval_odeDegreePolynomial_natDegree_eq_zero
    (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    {p : K[X]} (hp : p ≠ 0) (hode : differentialOperator A d p = 0) :
    (odeDegreePolynomial A d h).eval (p.natDegree : K) = 0 := by
  by_cases hm : (p.natDegree : ℤ) + h < 0
  · exact eval_odeDegreePolynomial_eq_zero_of_add_neg A d p.natDegree h hm
  have hN : (((p.natDegree : ℤ) + h).toNat : ℤ) = p.natDegree + h :=
    Int.toNat_of_nonneg (by lia)
  have hc := coeff_differentialOperator_top A d h hA p _ hN
  rw [hode, coeff_zero] at hc
  exact (mul_eq_zero.mp hc.symm).resolve_right (leadingCoeff_ne_zero.mpr hp)

/-- The inhomogeneous degree restriction: a nonzero solution either has a degree
root of the degree polynomial, or its shifted degree does not exceed that of the forcing term. -/
theorem eval_odeDegreePolynomial_eq_zero_or_degree_le
    (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hA : ∀ j ∈ Finset.range (d + 1), A j ≠ 0 → ((A j).natDegree : ℤ) - j ≤ h)
    {p f : K[X]} (hp : p ≠ 0) (hode : differentialOperator A d p = f) :
    (odeDegreePolynomial A d h).eval (p.natDegree : K) = 0 ∨
      (p.natDegree : ℤ) + h ≤ f.natDegree := by
  by_cases hm : (p.natDegree : ℤ) + h ≤ f.natDegree
  · exact Or.inr hm
  left
  have hN : (((p.natDegree : ℤ) + h).toNat : ℤ) = p.natDegree + h :=
    Int.toNat_of_nonneg (by lia)
  have hc := coeff_differentialOperator_top A d h hA p _ hN
  rw [hode, coeff_eq_zero_of_natDegree_lt (by lia)] at hc
  exact (mul_eq_zero.mp hc.symm).resolve_right (leadingCoeff_ne_zero.mpr hp)

/-- Every degree diagonal has polynomial degree at most the differential order. -/
theorem natDegree_odeDegreePolynomial_le (A : ℕ → K[X]) (d : ℕ) (h : ℤ) :
    (odeDegreePolynomial A d h).natDegree ≤ d := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjd := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  exact (natDegree_C_mul_le _ _).trans (by simp; lia)

/-- A nonempty degree diagonal cannot cancel, since falling factorials have
pairwise distinct degrees and nonzero leading coefficients. -/
theorem odeDegreePolynomial_ne_zero_of_exists
    (A : ℕ → K[X]) (d : ℕ) (h : ℤ)
    (hne : ∃ j ∈ Finset.range (d + 1), A j ≠ 0 ∧ ((A j).natDegree : ℤ) - j = h) :
    odeDegreePolynomial A d h ≠ 0 := by
  classical
  let S := (Finset.range (d + 1)).filter
    (fun j => A j ≠ 0 ∧ ((A j).natDegree : ℤ) - j = h)
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hAj⟩ := hne
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hAj⟩⟩
  let m := S.max' hS
  have hm : m ∈ S := Finset.max'_mem S hS
  have hc : (odeDegreePolynomial A d h).coeff m = (A m).leadingCoeff := by
    change (∑ j ∈ S, C (A j).leadingCoeff * descPochhammer K j).coeff m = _
    rw [finsetSum_coeff, Finset.sum_eq_single_of_mem m hm]
    · have hmonic : (descPochhammer K m).coeff m = 1 := by
        simpa only [descPochhammer_natDegree] using
          (monic_descPochhammer K m).coeff_natDegree
      rw [coeff_C_mul, hmonic, mul_one]
    · intro j hj hne
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      have hjm : j ≤ m := Finset.le_max' S j hj
      simp only [descPochhammer_natDegree]
      lia
  intro hz
  rw [hz, coeff_zero] at hc
  exact (leadingCoeff_ne_zero.mpr (Finset.mem_filter.mp hm).2.1) hc.symm

/-- The canonical leading degree polynomial is nonzero. -/
theorem odeDegreePolynomial_odeDegreeShift_ne_zero
    (A : ℕ → K[X]) (d : ℕ) (hne : ∃ j ∈ Finset.range (d + 1), A j ≠ 0) :
    odeDegreePolynomial A d (odeDegreeShift A d hne) ≠ 0 := by
  classical
  apply odeDegreePolynomial_ne_zero_of_exists
  have hS : ((Finset.range (d + 1)).filter (A · ≠ 0)).Nonempty := by
    simpa only [Finset.nonempty_def, Finset.mem_filter, exists_prop] using hne
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' hS
    (fun j => ((A j).natDegree : ℤ) - j)
  exact ⟨j, (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2, heq.symm⟩

end Polynomial
