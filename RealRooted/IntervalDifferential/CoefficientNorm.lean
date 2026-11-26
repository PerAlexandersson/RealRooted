/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A weighted coefficient norm

The elementary weighted sum of absolute coefficients is submultiplicative.
We keep its values in the coefficient field so rational certificates use exact
arithmetic without a second definition.
-/

@[expose] public section

noncomputable section

open Finset

namespace Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The sum of absolute coefficients weighted by powers of a nonnegative radius. -/
def coefficientNorm (r : K) (p : K[X]) : K := p.sum fun i a => |a| * r ^ i

/-- A common finite coefficient range can be used to compute the weighted norm. -/
theorem coefficientNorm_eq_sum {r : K} {p : K[X]} {s : Finset ℕ}
    (hs : p.support ⊆ s) : coefficientNorm r p = ∑ i ∈ s, |p.coeff i| * r ^ i :=
  sum_eq_of_subset _ (by simp) hs

omit [IsStrictOrderedRing K] in
@[simp] theorem coefficientNorm_zero (r : K) : coefficientNorm r (0 : K[X]) = 0 := by
  simp [coefficientNorm]

@[simp] theorem coefficientNorm_monomial (r a : K) (i : ℕ) :
    coefficientNorm r (monomial i a) = |a| * r ^ i := by
  simp [coefficientNorm, sum_monomial_index]

/-- The coefficient norm is nonnegative at a nonnegative radius. -/
theorem coefficientNorm_nonneg {r : K} (hr : 0 ≤ r) (p : K[X]) :
    0 ≤ coefficientNorm r p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hr _)

/-- Triangle inequality for the coefficient norm. -/
theorem coefficientNorm_add_le {r : K} (hr : 0 ≤ r) (p q : K[X]) :
    coefficientNorm r (p + q) ≤ coefficientNorm r p + coefficientNorm r q := by
  classical
  let s := p.support ∪ q.support
  rw [coefficientNorm_eq_sum (s := s) (support_add.trans (by rfl)),
    coefficientNorm_eq_sum (s := s) subset_union_left,
    coefficientNorm_eq_sum (s := s) subset_union_right, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  rw [coeff_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hr _)

/-- Triangle inequality for a finite polynomial sum. -/
theorem coefficientNorm_sum_le {ι : Type*} {r : K} (hr : 0 ≤ r)
    (s : Finset ι) (p : ι → K[X]) :
    coefficientNorm r (∑ i ∈ s, p i) ≤ ∑ i ∈ s, coefficientNorm r (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (coefficientNorm_add_le hr _ _).trans (add_le_add_right ih _)

/-- Submultiplicativity of the weighted coefficient norm. -/
theorem coefficientNorm_mul_le {r : K} (hr : 0 ≤ r) (p q : K[X]) :
    coefficientNorm r (p * q) ≤ coefficientNorm r p * coefficientNorm r q := by
  classical
  rw [mul_eq_sum_sum]
  apply (coefficientNorm_sum_le hr _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        coefficientNorm r (monomial (i + j) (p.coeff i * q.coeff j)) := by
      apply sum_le_sum
      intro i _
      exact coefficientNorm_sum_le hr _ _
    _ = coefficientNorm r p * coefficientNorm r q := by
      simp_rw [coefficientNorm_monomial, abs_mul, pow_add]
      simp only [coefficientNorm, sum_def]
      rw [sum_mul]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring

/-- The weighted norm of a constant. -/
@[simp] theorem coefficientNorm_C (r a : K) : coefficientNorm r (C a) = |a| := by
  rw [show C a = monomial 0 a from rfl, coefficientNorm_monomial, pow_zero, mul_one]

/-- Scalar multiplication scales the norm by the absolute scalar. -/
theorem coefficientNorm_C_mul (r a : K) (p : K[X]) :
    coefficientNorm r (C a * p) = |a| * coefficientNorm r p := by
  classical
  have hs : (C a * p).support ⊆ p.support := by
    intro i hi
    simp only [mem_support_iff] at hi ⊢
    intro he
    exact hi (by rw [coeff_C_mul, he, mul_zero])
  rw [coefficientNorm_eq_sum hs, coefficientNorm, sum_def, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [coeff_C_mul, abs_mul]
  ring

/-- Negation leaves the coefficient norm unchanged. -/
@[simp] theorem coefficientNorm_neg (r : K) (p : K[X]) :
    coefficientNorm r (-p) = coefficientNorm r p := by
  simpa using coefficientNorm_C_mul r (-1) p

/-- Strict coefficient dominance is preserved by every nonzero nonnegative
finite mixture. -/
theorem coefficientNorm_sum_sub_constant_lt {ι : Type*} {r : K} (hr : 0 ≤ r)
    (s : Finset ι) (p : ι → K[X]) (w : ι → K)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp : ∃ i ∈ s, 0 < w i)
    (hd : ∀ i ∈ s, coefficientNorm r (p i - C ((p i).coeff 0)) < (p i).coeff 0) :
    let f := ∑ i ∈ s, C (w i) * p i
    coefficientNorm r (f - C (f.coeff 0)) < f.coeff 0 := by
  classical
  dsimp only
  have he : (∑ i ∈ s, C (w i) * p i) - C ((∑ i ∈ s, C (w i) * p i).coeff 0) =
      ∑ i ∈ s, C (w i) * (p i - C ((p i).coeff 0)) := by
    simp only [finsetSum_coeff, coeff_C_mul, map_sum, map_mul]
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by ring)
  rw [he]
  apply (coefficientNorm_sum_le hr _ _).trans_lt
  simp only [coefficientNorm_C_mul, finsetSum_coeff, coeff_C_mul]
  have hl i hi : |w i| = w i := abs_of_nonneg (hw i hi)
  apply sum_lt_sum
  · intro i hi
    rw [hl i hi]
    exact mul_le_mul_of_nonneg_left (hd i hi).le (hw i hi)
  · obtain ⟨i, hi, hwi⟩ := hp
    refine ⟨i, hi, ?_⟩
    rw [hl i hi]
    exact mul_lt_mul_of_pos_left (hd i hi) hwi

/-- The constant coefficient and the remaining coefficients have disjoint norm
contributions. -/
theorem coefficientNorm_eq_abs_constant_add (r : K) (p : K[X]) :
    coefficientNorm r p = |p.coeff 0| + coefficientNorm r (p - C (p.coeff 0)) := by
  classical
  have hs : (p - C (p.coeff 0)).support ⊆ insert 0 p.support := by
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · apply mem_insert_of_mem
      simp only [mem_support_iff] at hi ⊢
      intro hz
      exact hi (by simp [coeff_C, hi0, hz])
  rw [coefficientNorm_eq_sum (subset_insert 0 p.support), coefficientNorm_eq_sum hs]
  have hc : (∑ i ∈ insert 0 p.support, if i = 0 then |p.coeff 0| else 0) = |p.coeff 0| := by
    simp
  rw [← hc, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : i = 0 <;> simp [hi, coeff_C]

/-- Strict constant dominance survives any perturbation smaller than its
coefficient margin. -/
theorem coefficientNorm_add_sub_constant_lt {r : K} (hr : 0 ≤ r) (p q : K[X])
    (hq : coefficientNorm r q < p.coeff 0 - coefficientNorm r (p - C (p.coeff 0))) :
    coefficientNorm r (p + q - C ((p + q).coeff 0)) < (p + q).coeff 0 := by
  have he : p + q - C ((p + q).coeff 0) =
      (p - C (p.coeff 0)) + (q - C (q.coeff 0)) := by
    simp only [coeff_add, map_add]
    ring
  rw [he]
  apply (coefficientNorm_add_le hr _ _).trans_lt
  have hn := coefficientNorm_eq_abs_constant_add r q
  have hz := neg_abs_le (q.coeff 0)
  rw [coeff_add]
  linarith

end Polynomial
