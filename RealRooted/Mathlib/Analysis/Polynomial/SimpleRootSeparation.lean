/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs

public import Mathlib.Algebra.Polynomial.Eval.Defs

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear root bounds from separated factors


A matched root has a linear coefficient-error bound once all other reference
factors stay uniformly away from zero. The estimate uses only finite products.
-/

public section

open Finset

namespace Polynomial

/-- A uniform coefficient bound controls the difference of two bounded-degree
polynomials on a bounded real interval. -/
theorem abs_eval_sub_le_of_coeff_le {p q : ℝ[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) {δ B x : ℝ}
    (hδ : 0 ≤ δ) (hcoeff : ∀ k ≤ n, |p.coeff k - q.coeff k| ≤ δ)
    (hx : |x| ≤ B) :
    |p.eval x - q.eval x| ≤ δ * ∑ k ∈ range (n + 1), B ^ k := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp),
    eval_eq_sum_range' (Nat.lt_succ_of_le hq), ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    |∑ k ∈ range (n + 1), (p.coeff k - q.coeff k) * x ^ k| ≤
        ∑ k ∈ range (n + 1), |(p.coeff k - q.coeff k) * x ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), δ * B ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hcoeff k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
        (pow_le_pow_left₀ (abs_nonneg x) hx k) (pow_nonneg (abs_nonneg x) k) hδ
    _ = δ * ∑ k ∈ range (n + 1), B ^ k := by rw [Finset.mul_sum]

/-- Separated factors give a lower bound on the absolute value of a product,
with one factor left unbounded. -/
theorem abs_sub_mul_pow_le_abs_prod {n : ℕ} (r : Fin n → ℝ)
    {x η : ℝ} (hη : 0 ≤ η) (i : Fin n)
    (hsep : ∀ j : Fin n, j ≠ i → η ≤ |x - r j|) :
    |x - r i| * η ^ (n - 1) ≤ |∏ j : Fin n, (x - r j)| := by
  have hprod : η ^ (n - 1) ≤ ∏ j ∈ univ.erase i, |x - r j| := by
    calc
      η ^ (n - 1) = ∏ _j ∈ (univ : Finset (Fin n)).erase i, η := by
        simp [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      _ ≤ ∏ j ∈ univ.erase i, |x - r j| := by
        apply Finset.prod_le_prod₀
        · intro j _
          exact hη
        · intro j hj
          exact hsep j (Finset.mem_erase.mp hj).1
  calc
    |x - r i| * η ^ (n - 1) ≤
        |x - r i| * ∏ j ∈ univ.erase i, |x - r j| :=
      mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = ∏ j : Fin n, |x - r j| :=
      Finset.mul_prod_erase univ (fun j => |x - r j|) (Finset.mem_univ i)
    _ = |∏ j : Fin n, (x - r j)| := by rw [Finset.abs_prod]

/-- A root of the perturbed polynomial lies linearly close to its matched
reference root when the remaining reference factors are separated. -/
theorem abs_sub_le_of_isRoot_of_factor_separation {p q : ℝ[X]} {n : ℕ}
    (r : Fin n → ℝ) (hp : p = ∏ j : Fin n, (X - C (r j)))
    (hq : q.natDegree ≤ n) {x η B δ : ℝ} (hx : q.IsRoot x)
    (hη : 0 < η) (hB : |x| ≤ B) (hδ : 0 ≤ δ)
    (hcoeff : ∀ k ≤ n, |p.coeff k - q.coeff k| ≤ δ)
    (i : Fin n) (hsep : ∀ j : Fin n, j ≠ i → η ≤ |x - r j|) :
    |x - r i| ≤ ((∑ k ∈ range (n + 1), B ^ k) / η ^ (n - 1)) * δ := by
  have hpdeg : p.natDegree ≤ n := by
    rw [hp]
    calc
      (∏ j : Fin n, (X - C (r j))).natDegree ≤
          ∑ j : Fin n, (X - C (r j)).natDegree := natDegree_prod_le _ _
      _ = n := by simp
  have hprod := abs_sub_mul_pow_le_abs_prod r hη.le i hsep
  have hvalue : |∏ j : Fin n, (x - r j)| = |p.eval x - q.eval x| := by
    rw [hx.eq_zero, sub_zero, hp]
    simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [hvalue] at hprod
  have hbound := hprod.trans (abs_eval_sub_le_of_coeff_le hpdeg hq hδ hcoeff hB)
  calc
    |x - r i| ≤ (δ * ∑ k ∈ range (n + 1), B ^ k) / η ^ (n - 1) :=
      (le_div_iff₀ (pow_pos hη _)).mpr hbound
    _ = ((∑ k ∈ range (n + 1), B ^ k) / η ^ (n - 1)) * δ := by ring

/-- Coarse matching within `η` and a reference gap of at least `2η` supply the
factor-separation hypotheses needed for a linear coefficient-error bound. -/
theorem abs_sub_le_of_isRoot_of_close {p q : ℝ[X]} {n : ℕ}
    (r : Fin n → ℝ) (hp : p = ∏ j : Fin n, (X - C (r j)))
    (hq : q.natDegree ≤ n) {x η B δ : ℝ} (hx : q.IsRoot x)
    (hη : 0 < η) (hB : ∀ j, |r j| ≤ B) (hδ : 0 ≤ δ)
    (hcoeff : ∀ k ≤ n, |p.coeff k - q.coeff k| ≤ δ)
    (i : Fin n) (hclose : |x - r i| ≤ η)
    (hsep : ∀ j : Fin n, j ≠ i → 2 * η ≤ |r i - r j|) :
    |x - r i| ≤
      ((∑ k ∈ range (n + 1), (B + η) ^ k) / η ^ (n - 1)) * δ := by
  have hxB : |x| ≤ B + η := by
    have htri : |x| ≤ |x - r i| + |r i| := by
      simpa only [sub_add_cancel] using abs_add_le (x - r i) (r i)
    linarith [hB i]
  apply abs_sub_le_of_isRoot_of_factor_separation r hp hq hx hη hxB hδ hcoeff i
  intro j hji
  have htri := abs_sub_le (r i) x (r j)
  rw [abs_sub_comm (r i) x] at htri
  linarith [hsep j hji]

end Polynomial
