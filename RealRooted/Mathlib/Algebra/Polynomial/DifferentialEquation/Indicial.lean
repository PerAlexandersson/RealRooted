/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Pochhammer

import Mathlib.Tactic

/-!
# Indicial equations for polynomial differential equations

We compare the first possibly nonzero Taylor coefficient of a polynomial ODE.
The vanishing hypotheses are divisibilities, so zero coefficient polynomials
need no exceptional convention. Source: the unpublished proof notes in
https://github.com/PerAlexandersson/RealRooted/issues/2341, Proposition 1
and Corollaries 2 and 3.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- The indicial polynomial at `r` and shift `s`, in the falling-factorial basis. -/
@[expose] noncomputable def indicialPolynomial (A : ℕ → K[X]) (d s : ℕ) (r : K) : K[X] :=
  ∑ j ∈ (Finset.range (d + 1)).filter (s ≤ ·),
    C ((taylor r (A j)).coeff (j - s)) * descPochhammer K j

/-- Evaluation of the indicial polynomial at a natural number. -/
theorem eval_indicialPolynomial (A : ℕ → K[X]) (d s m : ℕ) (r : K) :
    (indicialPolynomial A d s r).eval (m : K) =
      ∑ j ∈ (Finset.range (d + 1)).filter (s ≤ ·),
        (taylor r (A j)).coeff (j - s) * (m.descFactorial j : K) := by
  simp [indicialPolynomial, eval_finsetSum, descPochhammer_eval_eq_descFactorial]

/-- A product's first possible coefficient is the product of the first possible
coefficients, even if either coefficient or polynomial vanishes. -/
theorem coeff_mul_add_of_coeff_eq_zero {R : Type*} [Semiring R] {p q : R[X]} {a b : ℕ}
    (hp : ∀ i < a, p.coeff i = 0) (hq : ∀ i < b, q.coeff i = 0) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [coeff_mul]
  refine Finset.sum_eq_single_of_mem (a, b) (Finset.mem_antidiagonal.mpr rfl) ?_
  rintro ⟨i, j⟩ hij hne
  have hij' := Finset.mem_antidiagonal.mp hij
  by_cases hi : i < a
  · simp [hp i hi]
  by_cases hj : j < b
  · simp [hq j hj]
  exact (hne (Prod.ext (by lia) (by lia))).elim

/-- The coefficient at the indicial exponent in one term of a polynomial ODE. -/
theorem coeff_mul_iterate_derivative_of_X_pow_dvd
    (A p : K[X]) {m s j : ℕ} (hsm : s ≤ m) (hsj : s ≤ j)
    (hp : ∀ i < m, p.coeff i = 0) (hA : X ^ (j - s) ∣ A) :
    (A * derivative^[j] p).coeff (m - s) =
      A.coeff (j - s) * (m.descFactorial j : K) * p.coeff m := by
  by_cases hjm : j ≤ m
  · have hd : ∀ i < m - j, (derivative^[j] p).coeff i = 0 := by
      intro i hi
      rw [coeff_iterate_derivative, hp (i + j) (by lia), smul_zero]
    rw [show m - s = (j - s) + (m - j) by lia,
      coeff_mul_add_of_coeff_eq_zero (X_pow_dvd_iff.mp hA) hd,
      coeff_iterate_derivative, Nat.sub_add_cancel hjm, nsmul_eq_mul]
    ring
  · have hz : (A * derivative^[j] p).coeff (m - s) = 0 := by
      apply X_pow_dvd_iff.mp (dvd_mul_of_dvd_left hA _) _ (by lia)
    rw [hz, Nat.descFactorial_of_lt (by lia : m < j)]
    simp

/-- Terms below the indicial order do not contribute to its coefficient. -/
private theorem coeff_mul_iterate_derivative_eq_zero
    (A p : K[X]) {m s j : ℕ} (hsm : s ≤ m) (hjs : j < s)
    (hp : ∀ i < m, p.coeff i = 0) :
    (A * derivative^[j] p).coeff (m - s) = 0 := by
  apply X_pow_dvd_iff.mp (dvd_mul_of_dvd_right
    ((X_pow_dvd_iff (n := m - j)).mpr ?_) A) _ (by lia)
  intro i hi
  rw [coeff_iterate_derivative, hp (i + j) (by lia), smul_zero]

/-- The finite-point indicial equation for a nonzero polynomial solution of an
arbitrary-order ODE. The summation is over derivative orders at least `s`. -/
theorem rootMultiplicity_lt_or_indicial_eq_zero
    (A : ℕ → K[X]) (d s : ℕ) (r : K) {p : K[X]} (hp : p ≠ 0)
    (hode : ∑ j ∈ Finset.range (d + 1), A j * derivative^[j] p = 0)
    (hA : ∀ j ∈ Finset.range (d + 1), s ≤ j → (X - C r) ^ (j - s) ∣ A j) :
    p.rootMultiplicity r < s ∨
      ∑ j ∈ (Finset.range (d + 1)).filter (s ≤ ·),
        (taylor r (A j)).coeff (j - s) *
          (p.rootMultiplicity r).descFactorial j = 0 := by
  classical
  by_cases hms : p.rootMultiplicity r < s
  · exact Or.inl hms
  right
  let m := p.rootMultiplicity r
  let q := taylor r p
  have hsm : s ≤ m := by dsimp [m]; lia
  have hmq : m = q.natTrailingDegree := rootMultiplicity_eq_natTrailingDegree
  have hq : q ≠ 0 := (taylor_eq_zero r p).not.mpr hp
  have hcoeff : q.coeff m ≠ 0 := by
    rw [hmq]
    exact coeff_natTrailingDegree_ne_zero.mpr hq
  have hlow : ∀ i < m, q.coeff i = 0 := by
    intro i hi
    exact coeff_eq_zero_of_lt_natTrailingDegree (hmq ▸ hi)
  have hdiv (j : ℕ) (hj : j ∈ Finset.range (d + 1)) (hsj : s ≤ j) :
      X ^ (j - s) ∣ taylor r (A j) := by
    obtain ⟨B, hB⟩ := hA j hj hsj
    refine ⟨taylor r B, ?_⟩
    simp [hB, map_sub, taylor_pow, taylor_mul]
  have heq := congrArg (fun f : K[X] => (taylor r f).coeff (m - s)) hode
  simp only [map_sum, taylor_mul, taylor_iterate_derivative, finsetSum_coeff,
    map_zero, coeff_zero] at heq
  have hterm (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      (taylor r (A j) * derivative^[j] q).coeff (m - s) =
        if s ≤ j then
          (taylor r (A j)).coeff (j - s) * (m.descFactorial j : K) * q.coeff m
        else 0 := by
    split_ifs with hsj
    · exact coeff_mul_iterate_derivative_of_X_pow_dvd _ _ hsm hsj hlow (hdiv j hj hsj)
    · exact coeff_mul_iterate_derivative_eq_zero _ _ hsm (by lia) hlow
  change (∑ j ∈ Finset.range (d + 1),
    (taylor r (A j) * derivative^[j] q).coeff (m - s)) = 0 at heq
  rw [Finset.sum_congr rfl hterm] at heq
  rw [← Finset.sum_filter, ← Finset.sum_mul] at heq
  exact (mul_eq_zero.mp heq).resolve_right hcoeff

/-- A nonzero polynomial solution has either multiplicity below the indicial
shift or a multiplicity that is a root of the indicial polynomial. -/
theorem rootMultiplicity_lt_or_eval_indicialPolynomial_eq_zero
    (A : ℕ → K[X]) (d s : ℕ) (r : K) {p : K[X]} (hp : p ≠ 0)
    (hode : ∑ j ∈ Finset.range (d + 1), A j * derivative^[j] p = 0)
    (hA : ∀ j ∈ Finset.range (d + 1), s ≤ j → (X - C r) ^ (j - s) ∣ A j) :
    p.rootMultiplicity r < s ∨
      (indicialPolynomial A d s r).eval (p.rootMultiplicity r : K) = 0 := by
  simpa only [eval_indicialPolynomial] using
    rootMultiplicity_lt_or_indicial_eq_zero A d s r hp hode hA

variable [CharZero K]

/-- At an ordinary point of an order-`d` ODE, a nonzero polynomial solution
has multiplicity strictly smaller than `d`. This includes order zero. -/
theorem rootMultiplicity_lt_of_ode
    (A : ℕ → K[X]) (d : ℕ) (r : K) {p : K[X]} (hp : p ≠ 0)
    (hode : ∑ j ∈ Finset.range (d + 1), A j * derivative^[j] p = 0)
    (hA : (A d).eval r ≠ 0) : p.rootMultiplicity r < d := by
  rcases rootMultiplicity_lt_or_indicial_eq_zero A d d r hp hode
      (fun j hj hdj => by
        have hjd : j = d := by have := Finset.mem_range.mp hj; lia
        subst j
        simp) with h | h
  · exact h
  have hfilter : (Finset.range (d + 1)).filter (d ≤ ·) = {d} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    lia
  rw [hfilter] at h
  simp only [Finset.sum_singleton, Nat.sub_self, taylor_coeff_zero] at h
  have hz : (p.rootMultiplicity r).descFactorial d = 0 :=
    Nat.cast_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hA)
  exact Nat.descFactorial_eq_zero_iff_lt.mp hz

/-- The singular-point identity for any nonzero polynomial solution of a
second-order equation, without dividing by the derivative of its leading coefficient. -/
theorem rootMultiplicity_sub_one_mul_eval_derivative_add_eq_zero
    {p A B C₀ : K[X]} {r : K} (hp : p ≠ 0)
    (hode : A * p.derivative.derivative + B * p.derivative + C₀ * p = 0)
    (hAr : A.eval r = 0) (hr : p.IsRoot r) :
    ((p.rootMultiplicity r : K) - 1) * A.derivative.eval r + B.eval r = 0 := by
  let F : ℕ → K[X] := fun j => if j = 0 then C₀ else if j = 1 then B else A
  have heq : ∑ j ∈ Finset.range (2 + 1), F j * derivative^[j] p = 0 := by
    simpa [F, Finset.sum_range_succ, Function.iterate_succ_apply', add_comm,
      add_left_comm, add_assoc] using hode
  have hdiv : ∀ j ∈ Finset.range (2 + 1), 1 ≤ j →
      (X - C r) ^ (j - 1) ∣ F j := by
    intro j hj hsj
    have hj2 := Finset.mem_range.mp hj
    interval_cases j
    · simp [F]
    · simpa [F] using (dvd_iff_isRoot.mpr hAr)
  rcases rootMultiplicity_lt_or_indicial_eq_zero F 2 1 r hp heq hdiv with h | h
  · have := (rootMultiplicity_pos hp).mpr hr
    lia
  have hm : (p.rootMultiplicity r : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((rootMultiplicity_pos hp).mpr hr).ne'
  norm_num [Finset.sum_range_succ, Finset.sum_filter, F, Nat.descFactorial_succ,
    taylor_coeff_zero, taylor_coeff_one] at h
  have hmpos : 1 ≤ p.rootMultiplicity r := (rootMultiplicity_pos hp).mpr hr
  rw [Nat.cast_sub hmpos] at h
  apply (mul_eq_zero.mp (show (p.rootMultiplicity r : K) *
    (((p.rootMultiplicity r : K) - 1) * A.derivative.eval r + B.eval r) = 0 by
      linear_combination h)).resolve_left hm

end Polynomial
