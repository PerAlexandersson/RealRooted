/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetProduct
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# The finite inventory differential equation

All identities are algebraic modulo a power of the outer variable. No analytic
logarithm or infinite product is needed to obtain the coefficient recurrence.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [BinomialRing R]

private theorem multichoose_step (M : R) (a : ℕ) :
    ((a + 1 : ℕ) : R) * Ring.multichoose M (a + 1) =
      (M + (a : R)) * Ring.multichoose M a := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer M (a + 1)
  have g := Ring.factorial_nsmul_multichoose_eq_ascPochhammer M a
  simp only [nsmul_eq_mul, ascPochhammer_smeval_eq_eval] at h g
  rw [ascPochhammer_succ_right] at h
  simp only [eval_mul, eval_add, eval_X, eval_natCast, ← g, Nat.factorial_succ,
    Nat.cast_mul] at h
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a) :
    (a.factorial : R) ≠ 0)
  linear_combination h

private theorem multichoose_sum (M : R) (a : ℕ) :
    (a : R) * Ring.multichoose M a = (∑ i ∈ range a, Ring.multichoose M i) * M := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [multichoose_step, sum_range_succ]
    linear_combination ih

/-- The finite multiset factor with multiplicities through H. -/
def inventoryFactor (H : ℕ) (M : R) : R[X] :=
  ∑ i ∈ range (H + 1), monomial i (Ring.multichoose M i)

/-- The Euler logarithmic kernel of one finite multiset factor. -/
def inventoryKernel (H : ℕ) (M : R) : R[X] :=
  ∑ i ∈ range (H + 1), monomial i (if i = 0 then 0 else M)

omit [IsDomain R] [CharZero R] in
@[simp] theorem coeff_inventoryFactor {H i : ℕ} (hi : i ≤ H) (M : R) :
    (inventoryFactor H M).coeff i = Ring.multichoose M i := by
  rw [inventoryFactor, finsetSum_coeff]
  simp only [coeff_monomial_apply]
  simp [mem_range.mpr (Nat.lt_succ_of_le hi)]

omit [IsDomain R] [CharZero R] [BinomialRing R] in
@[simp] theorem coeff_inventoryKernel {H i : ℕ} (hi : i ≤ H) (M : R) :
    (inventoryKernel H M).coeff i = if i = 0 then 0 else M := by
  rw [inventoryKernel, finsetSum_coeff]
  simp only [coeff_monomial_apply]
  simp [mem_range.mpr (Nat.lt_succ_of_le hi)]

/-- The multiset factor solves the Euler equation through the truncation degree. -/
theorem inventoryFactor_equation (H : ℕ) (M : R) :
    X ^ (H + 1) ∣ inventoryKernel H M * inventoryFactor H M -
      X * (inventoryFactor H M).derivative := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  rw [coeff_sub, coeff_X_mul_derivative, mul_comm (inventoryKernel H M), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [Nat.sub_self, coeff_inventoryKernel (Nat.zero_le H), ite_true,
    mul_zero, add_zero, coeff_inventoryFactor (Nat.le_of_lt_succ hn)]
  apply sub_eq_zero.mpr
  rw [multichoose_sum, sum_mul]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  rw [coeff_inventoryFactor (by lia : i ≤ H), coeff_inventoryKernel (by lia : n - i ≤ H),
    ite_eq_right (by lia)]

omit [IsDomain R] [CharZero R] [BinomialRing R] in
private theorem expanded_euler {j : ℕ} (hj : 0 < j) (F : R[X]) :
    X * (expand R j F).derivative = (j : R[X]) * expand R j (X * F.derivative) := by
  simp only [derivative_expand, map_mul, expand_X]
  have hx : (X : R[X]) ^ j = X * X ^ (j - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hj]
  rw [hx]
  ring

/-- Expanding the length variable preserves the truncated inventory equation. -/
theorem expand_inventoryFactor_equation (H : ℕ) {j : ℕ} (hj : 0 < j) (M : R) :
    X ^ (H + 1) ∣ ((j : R[X]) * expand R j (inventoryKernel H M)) *
      expand R j (inventoryFactor H M) - X * (expand R j (inventoryFactor H M)).derivative := by
  obtain ⟨P, hP⟩ := inventoryFactor_equation H M
  have he := congrArg (expand R j) hP
  simp only [map_sub, map_mul, map_pow, expand_X, ← pow_mul] at he
  have hle : H + 1 ≤ j * (H + 1) := Nat.le_mul_of_pos_left _ hj
  rw [expanded_euler hj, mul_assoc, ← mul_sub]
  simp only [map_mul, expand_X]
  rw [he]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow X hle) _) _

omit [IsDomain R] [CharZero R] [BinomialRing R] in
/-- Truncated logarithmic kernels add when the inventory factors multiply. -/
theorem prod_inventoryFactor_equation {ι : Type*} (s : Finset ι) (F K : ι → R[X]) (H : ℕ)
    (h : ∀ i ∈ s, X ^ (H + 1) ∣ K i * F i - X * (F i).derivative) :
    X ^ (H + 1) ∣ (∑ i ∈ s, K i) * (∏ i ∈ s, F i) - X * (∏ i ∈ s, F i).derivative := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [sum_insert hi, prod_insert hi, derivative_mul]
    have u := h i (mem_insert_self i t)
    have v := ih (fun j hj => h j (mem_insert_of_mem hj))
    have w := dvd_add (dvd_mul_of_dvd_left u (∏ j ∈ t, F j))
      (dvd_mul_of_dvd_right v (F i))
    convert w using 1; ring

end Generic

/-- The actual rational alphabet product, with a fixed finite jet bound. -/
def alphabetProduct (H k : ℕ) : ℚ[X][X] :=
  ∏ i : Fin H, expand ℚ[X] (i.val + 1)
    (inventoryFactor H (if i.val + 1 < k then 0 else necklacePolynomial (i.val + 1)))

/-- The sum of the length-wise Euler kernels of the rational alphabet product. -/
def alphabetProductKernel (H k : ℕ) : ℚ[X][X] :=
  ∑ i : Fin H, ((i.val + 1 : ℕ) : ℚ[X][X]) * expand ℚ[X] (i.val + 1)
    (inventoryKernel H (if i.val + 1 < k then 0 else necklacePolynomial (i.val + 1)))

/-- The rational product has the exact logarithmic kernel through H. -/
theorem alphabetProduct_equation (H k : ℕ) :
    X ^ (H + 1) ∣ alphabetProductKernel H k * alphabetProduct H k -
      X * (alphabetProduct H k).derivative :=
  prod_inventoryFactor_equation univ _ _ H
    (fun i _ => expand_inventoryFactor_equation H (Nat.succ_pos i.val) _)

private theorem expand_inventoryFactor (n j : ℕ) (M : ℚ[X]) :
    expand ℚ[X] j (inventoryFactor n M) =
      ∑ a : Fin (n + 1), monomial (j * a.val) (Ring.multichoose M a.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun a => monomial (j * a) (Ring.multichoose M a))]
  simp only [inventoryFactor, map_sum, expand_monomial]
  apply sum_congr rfl
  intro a _
  rw [Nat.mul_comm]

private theorem prod_monomial {ι : Type*} (s : Finset ι) (e : ι → ℕ) (c : ι → ℚ[X]) :
    (∏ i ∈ s, monomial (e i) (c i)) = monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [prod_insert hi, sum_insert hi, ih, monomial_mul_monomial]

/-- Extracting the diagonal coefficient recovers the genuine alphabet polynomial. -/
theorem alphabetProduct_coeff (n k : ℕ) : (alphabetProduct n k).coeff n = cycleAlphabet n k := by
  classical
  simp only [alphabetProduct, expand_inventoryFactor, Fintype.prod_sum, prod_monomial,
    finsetSum_coeff, coeff_monomial_apply]
  let valid (f : Fin n → Fin (n + 1)) : Prop :=
    (∑ i, (i.val + 1) * (f i).val) = n ∧ ∀ i, i.val + 1 < k → f i = 0
  let weight (f : Fin n → Fin (n + 1)) :=
    ∏ i, Ring.multichoose (necklacePolynomial (i.val + 1)) (f i).val
  have he : cycleAlphabet n k = ∑ f ∈ univ.filter valid, weight f := by
    exact (Finset.sum_subtype (p := valid) (univ.filter valid)
      (fun _ => by simp only [mem_filter, mem_univ, true_and]) weight).symm
  rw [he, sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases total : (∑ i, (i.val + 1) * (f i).val) = n
  · by_cases cutoff : ∀ i : Fin n, i.val + 1 < k → f i = 0
    · rw [ite_eq_left total, ite_eq_left (show valid f from ⟨total, cutoff⟩)]
      apply prod_congr rfl
      intro i _
      by_cases hc : i.val + 1 < k
      · simp [hc, cutoff i hc]
      · rw [ite_eq_right hc]
    · rw [ite_eq_left total, ite_eq_right (show ¬valid f from fun h => cutoff h.2)]
      push Not at cutoff
      obtain ⟨i, hi, ha⟩ := cutoff
      apply Finset.prod_eq_zero (mem_univ i)
      have hn : (f i).val ≠ 0 := fun hh => ha (Fin.ext hh)
      obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [hi, hv, Ring.multichoose_zero_succ]
  · rw [ite_eq_right total, ite_eq_right (show ¬valid f from fun h => total h.1)]

end RealRooted.LongCycleDescents.Structural
