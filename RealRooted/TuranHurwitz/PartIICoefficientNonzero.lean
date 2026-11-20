module

public import RealRooted.TuranHurwitz.PartIIConvexRoots
import Mathlib.Tactic.NormNum

/-!
# Nonzero coefficients from a convex root region avoiding zero

Repeated Gauss–Lucas preservation shows that every derivative up to the
degree has nonzero value at the origin.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Over the complex numbers, iterated differentiation reduces the degree by its order. -/
theorem natDegree_iterate_derivative_eq (p : ℂ[X]) (k : ℕ) :
    (derivative^[k] p).natDegree = p.natDegree - k := by
  apply le_antisymm (natDegree_iterate_derivative p k)
  by_cases hk : k ≤ p.natDegree
  · by_cases hp : p = 0
    · subst p
      simp
    · apply le_natDegree_of_ne_zero
      rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
      exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne')
        (leadingCoeff_ne_zero.mpr hp)
  · simp only [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hk)]
    exact Nat.zero_le _

/-- Differentiating no more than the degree cannot annihilate a nonzero complex polynomial. -/
theorem iterate_derivative_ne_zero_of_le_natDegree {p : ℂ[X]} (hp : p ≠ 0)
    {k : ℕ} (hk : k ≤ p.natDegree) : derivative^[k] p ≠ 0 := by
  intro heq
  have h := congrArg (fun q : ℂ[X] => q.coeff (p.natDegree - k)) heq
  rw [coeff_zero, coeff_iterate_derivative, Nat.sub_add_cancel hk,
    nsmul_eq_mul, coeff_natDegree] at h
  have hfac : (p.natDegree.descFactorial k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
  exact mul_ne_zero hfac (leadingCoeff_ne_zero.mpr hp) h

/-- Every iterated derivative has all its roots in the same convex region. -/
theorem iterate_derivative_roots_mem_convex {S : Set ℂ} (hS : Convex ℝ S) {p : ℂ[X]}
    (hr : ∀ z ∈ p.roots, z ∈ S) (k : ℕ) :
    ∀ z ∈ (derivative^[k] p).roots, z ∈ S := by
  induction k with
  | zero => exact hr
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact derivative_roots_mem_convex hS ih

/-- Every coefficient through the degree is nonzero when a convex root region excludes zero. -/
theorem coeff_ne_zero_of_roots_mem_convex {S : Set ℂ} (hS : Convex ℝ S) (hzero : 0 ∉ S)
    {p : ℂ[X]} (hp : p ≠ 0) (hr : ∀ z ∈ p.roots, z ∈ S) {k : ℕ}
    (hk : k ≤ p.natDegree) : p.coeff k ≠ 0 := by
  intro hcoeff
  have hne := iterate_derivative_ne_zero_of_le_natDegree hp hk
  have heval : (derivative^[k] p).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, Nat.zero_add,
      hcoeff, nsmul_zero]
  exact hzero (iterate_derivative_roots_mem_convex hS hr k 0 ((mem_roots hne).mpr heval))

end RealRooted.TuranHurwitz
