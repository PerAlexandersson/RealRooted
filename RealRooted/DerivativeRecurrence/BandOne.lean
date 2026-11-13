/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
import RealRooted.DerivativeRecurrence.Degree
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import RealRooted.Mathlib.Algebra.Polynomial.Degree.SmallDegree
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Exact endpoints of band-one derivative-lag recurrences

The degree cap, the top two coefficients, and the constant term are independent
of root geometry. In particular, the endpoint decision below applies to any
polynomial with the displayed cap, including operators with higher-band cancellation.
The variable-degree induction allows any prescribed path with increments zero or one.
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- Under a one-band cap, the signs of the top two prospective coefficients
decide exactly whether the degree is one of the two endpoints with positive leader.
This includes `m = 0` and does not assume nonnegative coefficients. -/
theorem natDegree_endpoints_leadingCoeff_pos_iff {r : ℝ[X]} {m : ℕ}
    (hr : r.natDegree ≤ m + 1) :
    ((r.natDegree = m + 1 ∧ 0 < r.leadingCoeff) ∨
      (r.natDegree = m ∧ 0 < r.leadingCoeff)) ↔
      0 < r.coeff (m + 1) ∨ (r.coeff (m + 1) = 0 ∧ 0 < r.coeff m) := by
  constructor
  · rintro (⟨hdeg, hpos⟩ | ⟨hdeg, hpos⟩)
    · left
      simpa [leadingCoeff, hdeg] using hpos
    · right
      exact ⟨coeff_eq_zero_of_natDegree_lt (by lia),
        by simpa [leadingCoeff, hdeg] using hpos⟩
  · rintro (htop | ⟨htop, hnext⟩)
    · have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hr htop.ne'
      exact Or.inl ⟨hdeg, by simpa [leadingCoeff, hdeg] using htop⟩
    · have hle : r.natDegree ≤ m := by
        by_contra h
        have heq : r.natDegree = m + 1 := by lia
        have hne : r ≠ 0 := by intro hz; simp [hz] at hnext
        exact (leadingCoeff_ne_zero.mpr hne) (by simpa [leadingCoeff, heq] using htop)
      have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hle hnext.ne'
      exact Or.inr ⟨hdeg, by simpa [leadingCoeff, hdeg] using hnext⟩

end Polynomial

namespace RealRooted.BandOne

variable {U V L p q : ℝ[X]} {m d δ : ℕ}

/-- Affine current, quadratic derivative multiplier, and bounded lag give a
one-band output cap. Zero inputs are allowed without assigning them an exact degree. -/
theorem natDegree_step_le (hU : U.natDegree ≤ 1) (hV : V.natDegree ≤ 2)
    (hL : L.natDegree ≤ δ + 1) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ m)
    (hd : d + δ = m) :
    (U * q + V * q.derivative + L * p).natDegree ≤ m + 1 := by
  have hUd := natDegree_mul_iterate_derivative_le (d := 1) (j := 0) hU hq
  have hVd := natDegree_mul_iterate_derivative_le (d := 1) (j := 1) hV hq
  simp only [Function.iterate_zero, Function.iterate_one, id_eq] at hUd hVd
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hUd hVd)
    ((natDegree_mul_le_of_le hL hp).trans (by lia))

/-- The prospective coefficient in degree `m + 1`. The hypotheses are bounds,
so the identity includes zero inputs and leading cancellation. -/
theorem coeff_step_succ (hU : U.natDegree ≤ 1) (hV : V.natDegree ≤ 2)
    (hL : L.natDegree ≤ δ + 1) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ m)
    (hd : d + δ = m) :
    (U * q + V * q.derivative + L * p).coeff (m + 1) =
      (U.coeff 1 + (m : ℝ) * V.coeff 2) * q.coeff m +
        L.coeff (δ + 1) * p.coeff d := by
  have hUc := coeff_mul_iterate_derivative_of_natDegree_le (d := 1) (j := 0) hU hq
  have hVc := coeff_mul_iterate_derivative_of_natDegree_le (d := 1) (j := 1) hV hq
  simp only [Function.iterate_zero, Function.iterate_one, id_eq,
    Nat.descFactorial_zero, Nat.descFactorial_one, Nat.cast_one, mul_one] at hUc hVc
  rw [coeff_add, coeff_add, hUc, hVc, show m + 1 = (δ + 1) + d by lia,
    coeff_mul_add_of_natDegree_le hL hp]
  ring

/-- The coefficient of an affine/quadratic current in a positive degree.
The constant derivative multiplier is kept explicitly. -/
private theorem coeff_current_succ (hU : U.natDegree ≤ 1) (hV : V.natDegree ≤ 2)
    (k : ℕ) :
    (U * q + V * q.derivative).coeff (k + 1) =
      (U.coeff 0 + ((k : ℝ) + 1) * V.coeff 1) * q.coeff (k + 1) +
        (U.coeff 1 + (k : ℝ) * V.coeff 2) * q.coeff k +
        V.coeff 0 * ((k : ℝ) + 2) * q.coeff (k + 2) := by
  have heq : U * q + V * q.derivative =
      ((C (V.coeff 1) * X + C (V.coeff 2) * X ^ 2) * q.derivative +
        (C (U.coeff 0) + C (U.coeff 1) * X) * q) + C (V.coeff 0) * q.derivative := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hU,
      eq_X_sq_add_X_add_C_of_natDegree_le_two hV]
    ring
  rw [heq, coeff_add, coeff_quadratic_derivative_add_linear_mul_succ,
    coeff_C_mul, coeff_derivative]
  push_cast
  ring

/-- The lag coefficient immediately below its degree cap. The guarded index
is zero when the predecessor is constant, rather than its constant coefficient. -/
private theorem coeff_lag (hL : L.natDegree ≤ δ + 1) (hp : p.natDegree ≤ d)
    (hd : d + δ = m) :
    (L * p).coeff m = L.coeff δ * p.coeff d +
      L.coeff (δ + 1) * (if d = 0 then 0 else p.coeff (d - 1)) := by
  cases d with
  | zero =>
      have hm : m = δ := by lia
      rw [hm, eq_C_of_natDegree_le_zero hp, coeff_mul_C]
      simp
  | succ d =>
      have heq : m = δ + d + 1 := by lia
      rw [heq, coeff_mul_add_add_one_eq_of_natDegree_le hL hp]
      simp
      ring

/-- The prospective coefficient in degree `m`, including a constant predecessor.
All casts of degrees are real casts; no sign assumptions on the output are used. -/
theorem coeff_step (hm : m ≠ 0) (hU : U.natDegree ≤ 1) (hV : V.natDegree ≤ 2)
    (hL : L.natDegree ≤ δ + 1) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ m)
    (hd : d + δ = m) :
    (U * q + V * q.derivative + L * p).coeff m =
      (U.coeff 0 + (m : ℝ) * V.coeff 1) * q.coeff m +
        (U.coeff 1 + ((m : ℝ) - 1) * V.coeff 2) * q.coeff (m - 1) +
        L.coeff δ * p.coeff d +
        L.coeff (δ + 1) * (if d = 0 then 0 else p.coeff (d - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  have hz : q.coeff (k + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  rw [coeff_add, coeff_current_succ hU hV, coeff_lag hL hp hd, hz]
  push_cast
  simp
  ring

/-- Constant-term recurrence, independent of every degree hypothesis. -/
theorem coeff_step_zero (U V L p q : ℝ[X]) :
    (U * q + V * q.derivative + L * p).coeff 0 =
      U.coeff 0 * q.coeff 0 + V.coeff 0 * q.coeff 1 + L.coeff 0 * p.coeff 0 := by
  simp [coeff_derivative]

/-- With a zero predecessor the lag disappears, with no degree attached to zero. -/
theorem step_zero_predecessor (U V L q : ℝ[X]) :
    U * q + V * q.derivative + L * 0 = U * q + V * q.derivative := by simp

/-- A constant current has zero derivative, even when the constant is zero. -/
theorem step_of_natDegree_eq_zero (hq : q.natDegree = 0) :
    U * q + V * q.derivative + L * p = U * q + L * p := by
  rw [derivative_eq_zero.mpr hq]
  simp

/-- The constant-current branch has a linear cap when the lag product does.
Its two coefficients are valid without a fake degree for a zero predecessor. -/
theorem constant_step (hU : U.natDegree ≤ 1) (hq : q.natDegree = 0)
    (hLp : (L * p).natDegree ≤ 1) :
    (U * q + V * q.derivative + L * p).natDegree ≤ 1 ∧
      (U * q + V * q.derivative + L * p).coeff 1 =
        U.coeff 1 * q.coeff 0 + (L * p).coeff 1 ∧
      (U * q + V * q.derivative + L * p).coeff 0 =
        U.coeff 0 * q.coeff 0 + L.coeff 0 * p.coeff 0 := by
  rw [step_of_natDegree_eq_zero hq]
  refine ⟨natDegree_add_le_of_degree_le
    ((natDegree_mul_le_of_le hU hq.le).trans (by lia)) hLp, ?_, ?_⟩
  · rw [coeff_add, eq_C_of_natDegree_eq_zero hq, coeff_mul_C]
    simp
  · simp

/-- The degree cap and both endpoints with zero predecessor. The lag multiplier
is absent, so no bound on it and no degree for the zero polynomial are required. -/
theorem zero_predecessor_endpoints (hm : m ≠ 0) (hU : U.natDegree ≤ 1)
    (hV : V.natDegree ≤ 2) (hq : q.natDegree ≤ m) :
    (U * q + V * q.derivative).natDegree ≤ m + 1 ∧
      (U * q + V * q.derivative).coeff (m + 1) =
        (U.coeff 1 + (m : ℝ) * V.coeff 2) * q.coeff m ∧
      (U * q + V * q.derivative).coeff m =
        (U.coeff 0 + (m : ℝ) * V.coeff 1) * q.coeff m +
          (U.coeff 1 + ((m : ℝ) - 1) * V.coeff 2) * q.coeff (m - 1) := by
  have hL : (0 : ℝ[X]).natDegree ≤ 1 := by simp
  have hp : (0 : ℝ[X]).natDegree ≤ m := by simp
  refine ⟨?_, ?_, ?_⟩
  · simpa using natDegree_step_le (δ := 0) hU hV hL hp hq (by simp)
  · simpa using coeff_step_succ (δ := 0) hU hV hL hp hq (by simp)
  · simpa using coeff_step (δ := 0) hm hU hV hL hp hq (by simp)

/-- The exact band-one endpoint test in coefficient form. The predecessor
index is guarded even when its degree is zero; lower output degrees are excluded. -/
theorem step_endpoints_iff (hm : m ≠ 0) (hU : U.natDegree ≤ 1)
    (hV : V.natDegree ≤ 2) (hL : L.natDegree ≤ δ + 1)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ m) (hd : d + δ = m) :
    let r := U * q + V * q.derivative + L * p
    ((r.natDegree = m + 1 ∧ 0 < r.leadingCoeff) ∨
      (r.natDegree = m ∧ 0 < r.leadingCoeff)) ↔
      0 < (U.coeff 1 + (m : ℝ) * V.coeff 2) * q.coeff m +
        L.coeff (δ + 1) * p.coeff d ∨
      ((U.coeff 1 + (m : ℝ) * V.coeff 2) * q.coeff m +
          L.coeff (δ + 1) * p.coeff d = 0 ∧
        0 < (U.coeff 0 + (m : ℝ) * V.coeff 1) * q.coeff m +
          (U.coeff 1 + ((m : ℝ) - 1) * V.coeff 2) * q.coeff (m - 1) +
          L.coeff δ * p.coeff d +
          L.coeff (δ + 1) * (if d = 0 then 0 else p.coeff (d - 1))) := by
  dsimp only
  rw [Polynomial.natDegree_endpoints_leadingCoeff_pos_iff
    (natDegree_step_le hU hV hL hp hq hd), coeff_step_succ hU hV hL hp hq hd,
    coeff_step hm hU hV hL hp hq hd]

/-- Prospective top coefficient for a degree path with predecessor degree `d`
and current degree `m`. -/
def topCoeff (U V L p q : ℝ[X]) (d m : ℕ) : ℝ :=
  (U.coeff 1 + (m : ℝ) * V.coeff 2) * q.coeff m +
    L.coeff (m - d + 1) * p.coeff d

/-- Prospective current-degree coefficient. Both potentially negative indices
are guarded, and the constant-current branch retains the constant derivative term. -/
def currentCoeff (U V L p q : ℝ[X]) (d m : ℕ) : ℝ :=
  if m = 0 then
    U.coeff 0 * q.coeff 0 + V.coeff 0 * q.coeff 1 + L.coeff 0 * p.coeff 0
  else
    (U.coeff 0 + (m : ℝ) * V.coeff 1) * q.coeff m +
      (U.coeff 1 + ((m : ℝ) - 1) * V.coeff 2) * q.coeff (m - 1) +
      L.coeff (m - d) * p.coeff d +
      L.coeff (m - d + 1) * (if d = 0 then 0 else p.coeff (d - 1))

/-- Exact degrees and positive leaders along any prescribed nondecreasing
degree path with increments at most one. Endpoint inequalities may use the
already established degrees and positive leaders, and remain explicit obligations. -/
theorem natDegree_eq_and_leadingCoeff_pos {P U V L : ℕ → ℝ[X]} {D : ℕ → ℕ}
    (hrec : ∀ n, P (n + 2) =
      U n * P (n + 1) + V n * (P (n + 1)).derivative + L n * P n)
    (hpath : ∀ n, D n ≤ D (n + 1) ∧ D (n + 1) ≤ D n + 1)
    (hU : ∀ n, (U n).natDegree ≤ 1) (hV : ∀ n, (V n).natDegree ≤ 2)
    (hL : ∀ n, (L n).natDegree ≤ D (n + 1) - D n + 1)
    (h0 : (P 0).natDegree = D 0 ∧ 0 < (P 0).leadingCoeff)
    (h1 : (P 1).natDegree = D 1 ∧ 0 < (P 1).leadingCoeff)
    (hend : ∀ n, (P n).natDegree = D n → 0 < (P n).leadingCoeff →
      (P (n + 1)).natDegree = D (n + 1) → 0 < (P (n + 1)).leadingCoeff →
      if D (n + 2) = D (n + 1) + 1 then
        0 < topCoeff (U n) (V n) (L n) (P n) (P (n + 1)) (D n) (D (n + 1))
      else
        topCoeff (U n) (V n) (L n) (P n) (P (n + 1)) (D n) (D (n + 1)) = 0 ∧
          0 < currentCoeff (U n) (V n) (L n) (P n) (P (n + 1)) (D n) (D (n + 1))) :
    ∀ n, (P n).natDegree = D n ∧ 0 < (P n).leadingCoeff := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
      have hd : D n + (D (n + 1) - D n) = D (n + 1) := by
        have := (hpath n).1
        lia
      have hcap : (P (n + 2)).natDegree ≤ D (n + 1) + 1 := by
        rw [hrec n]
        exact natDegree_step_le (hU n) (hV n) (hL n) ih0.1.le ih1.1.le hd
      have ht : (P (n + 2)).coeff (D (n + 1) + 1) =
          topCoeff (U n) (V n) (L n) (P n) (P (n + 1)) (D n) (D (n + 1)) := by
        rw [hrec n]
        exact coeff_step_succ (hU n) (hV n) (hL n) ih0.1.le ih1.1.le hd
      have hc : (P (n + 2)).coeff (D (n + 1)) =
          currentCoeff (U n) (V n) (L n) (P n) (P (n + 1)) (D n) (D (n + 1)) := by
        rw [hrec n]
        by_cases hm : D (n + 1) = 0
        · simp only [currentCoeff, hm, ↓reduceIte]
          exact coeff_step_zero _ _ _ _ _
        · simp only [currentCoeff, hm, ↓reduceIte]
          exact coeff_step hm (hU n) (hV n) (hL n) ih0.1.le ih1.1.le hd
      have he := hend n ih0.1 ih0.2 ih1.1 ih1.2
      by_cases hrise : D (n + 2) = D (n + 1) + 1
      · simp only [hrise, ↓reduceIte] at he
        have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hcap (ht.symm ▸ he.ne')
        exact ⟨hdeg.trans hrise.symm, by simpa [leadingCoeff, hdeg, ht] using he⟩
      · simp only [hrise, ↓reduceIte] at he
        have hplateau : D (n + 2) = D (n + 1) := by
          have := hpath (n + 1)
          lia
        have hout := (Polynomial.natDegree_endpoints_leadingCoeff_pos_iff hcap).mpr
          (Or.inr ⟨ht.trans he.1, hc.symm ▸ he.2⟩)
        rcases hout with ⟨hdeg, hpos⟩ | ⟨hdeg, hpos⟩
        · have hz := ht.trans he.1
          have : 0 < (P (n + 2)).coeff (D (n + 1) + 1) := by
            simpa [leadingCoeff, hdeg] using hpos
          simp [hz] at this
        · exact ⟨hdeg.trans hplateau.symm, hpos⟩

/-- A sequence's constant-term recurrence is separate from its degree path. -/
theorem coeff_sequence_zero {P U V L : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) =
      U n * P (n + 1) + V n * (P (n + 1)).derivative + L n * P n) (n : ℕ) :
    (P (n + 2)).coeff 0 = (U n).coeff 0 * (P (n + 1)).coeff 0 +
      (V n).coeff 0 * (P (n + 1)).coeff 1 + (L n).coeff 0 * (P n).coeff 0 := by
  rw [hrec n]
  exact coeff_step_zero _ _ _ _ _

/-- Endpoints of `I + θ` with a positive-X lag. This includes the constant
current and both the equal-degree and successor-degree input cases. -/
theorem eulerLag_endpoints (p q : ℝ[X]) (lam : ℝ) {m : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m) :
    (q + X * q.derivative + C lam * X * p).natDegree ≤ m + 1 ∧
      (q + X * q.derivative + C lam * X * p).coeff (m + 1) = lam * p.coeff m ∧
      (q + X * q.derivative + C lam * X * p).coeff m =
        ((m : ℝ) + 1) * q.coeff m +
          lam * (if m = 0 then 0 else p.coeff (m - 1)) := by
  have hcap := natDegree_step_le (δ := 0) (U := 1) (V := X) (L := C lam * X)
    (by simp) (by simp) (by compute_degree) hp hq (by simp)
  have hqzero : q.coeff (m + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  refine ⟨by simpa using hcap, ?_, ?_⟩
  · rw [coeff_add, coeff_add, coeff_X_mul_derivative,
      show C lam * X * p = C lam * (X * p) by ring,
      coeff_C_mul, coeff_X_mul, hqzero]
    ring
  · cases m with
    | zero => simp [mul_assoc]
    | succ m =>
        rw [coeff_add, coeff_add, coeff_X_mul_derivative,
          show C lam * X * p = C lam * (X * p) by ring, coeff_C_mul, coeff_X_mul]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel]
        ring

/-- Positive lag scalars in an `I + θ` recurrence give the alternating
rise/plateau path `floor(n/2)`, including the two constant seed rows. -/
theorem eulerLag_natDegree {P : ℕ → ℝ[X]} {lam : ℕ → ℝ}
    (hrec : ∀ n, P (n + 2) = P (n + 1) + X * (P (n + 1)).derivative +
      C (lam n) * X * P n)
    (h0 : (P 0).natDegree = 0 ∧ 0 < (P 0).leadingCoeff)
    (h1 : (P 1).natDegree = 0 ∧ 0 < (P 1).leadingCoeff)
    (hlam : ∀ n, 0 < lam n) :
    ∀ n, (P n).natDegree = n / 2 ∧ 0 < (P n).leadingCoeff := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
      have hle : (P n).natDegree ≤ (n + 1) / 2 := by lia
      obtain ⟨hcap, ht, hc⟩ := eulerLag_endpoints (P n) (P (n + 1)) (lam n)
        hle ih1.1.le
      rw [← hrec n] at hcap ht hc
      by_cases heven : n % 2 = 0
      · have heq : n / 2 = (n + 1) / 2 := by lia
        have hnext : (n + 2) / 2 = (n + 1) / 2 + 1 := by lia
        have hp : 0 < (P n).coeff ((n + 1) / 2) := by
          simpa [leadingCoeff, ih0.1, heq] using ih0.2
        have htop : 0 < (P (n + 2)).coeff ((n + 1) / 2 + 1) := by
          rw [ht]
          exact mul_pos (hlam n) hp
        have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hcap htop.ne'
        exact ⟨hdeg.trans hnext.symm, by simpa [leadingCoeff, hdeg] using htop⟩
      · have hgap : n / 2 + 1 = (n + 1) / 2 := by lia
        have hnext : (n + 2) / 2 = (n + 1) / 2 := by lia
        have hm : (n + 1) / 2 ≠ 0 := by lia
        have hpzero : (P n).coeff ((n + 1) / 2) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        have hp : 0 < (P n).coeff ((n + 1) / 2 - 1) := by
          have heq : (n + 1) / 2 - 1 = n / 2 := by lia
          simpa [leadingCoeff, ih0.1, heq] using ih0.2
        have hq : 0 < (P (n + 1)).coeff ((n + 1) / 2) := by
          simpa [leadingCoeff, ih1.1] using ih1.2
        have hz : (P (n + 2)).coeff ((n + 1) / 2 + 1) = 0 := by simp [ht, hpzero]
        have hpos : 0 < (P (n + 2)).coeff ((n + 1) / 2) := by
          rw [hc, ite_eq_right hm]
          exact add_pos (mul_pos (by positivity) hq) (mul_pos (hlam n) hp)
        have hout := (Polynomial.natDegree_endpoints_leadingCoeff_pos_iff hcap).mpr
          (Or.inr ⟨hz, hpos⟩)
        rcases hout with ⟨hdeg, hlead⟩ | ⟨hdeg, hlead⟩
        · have : 0 < (P (n + 2)).coeff ((n + 1) / 2 + 1) := by
            simpa [leadingCoeff, hdeg] using hlead
          simp [hz] at this
        · exact ⟨hdeg.trans hnext.symm, hlead⟩

/-- For the Eulerian current with drift `m + 1`, a lower-degree linear lag
does not contribute at the top, whose coefficient is exactly `q_m`. -/
theorem eulerianLag_endpoints (p q : ℝ[X]) (lam : ℝ) {m : ℕ}
    (hp : p.natDegree + 1 ≤ m) (hq : q.natDegree ≤ m) :
    ((1 + C ((m : ℝ) + 1) * X) * q +
      (X - X ^ 2) * q.derivative + C lam * X * p).natDegree ≤ m + 1 ∧
      ((1 + C ((m : ℝ) + 1) * X) * q +
        (X - X ^ 2) * q.derivative + C lam * X * p).coeff (m + 1) = q.coeff m := by
  have hU : (1 + C ((m : ℝ) + 1) * X).natDegree ≤ 1 := by compute_degree
  have hV : (X - X ^ 2 : ℝ[X]).natDegree ≤ 2 := by compute_degree
  have hL : (C lam * X).natDegree ≤ 1 := by compute_degree
  have hpzero : p.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  refine ⟨natDegree_step_le (δ := 0) (d := m) hU hV hL (by lia) hq (by simp), ?_⟩
  rw [coeff_step_succ (δ := 0) (d := m) hU hV hL (by lia) hq (by simp)]
  simp [hpzero, coeff_sub, coeff_add, coeff_one, coeff_X]

/-- Exact rising degrees for the Eulerian current, uniformly in its lag scalar. -/
theorem eulerianLag_natDegree {P : ℕ → ℝ[X]} {lam : ℕ → ℝ} {D : ℕ}
    (hrec : ∀ n, P (n + 2) =
      (1 + C ((n : ℝ) + (D : ℝ) + 2) * X) * P (n + 1) +
        (X - X ^ 2) * (P (n + 1)).derivative + C (lam n) * X * P n)
    (h0 : (P 0).natDegree = D ∧ 0 < (P 0).leadingCoeff)
    (h1 : (P 1).natDegree = D + 1 ∧ 0 < (P 1).leadingCoeff) :
    ∀ n, (P n).natDegree = D + n ∧ 0 < (P n).leadingCoeff := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => exact h1
  | more n ih0 ih1 =>
      obtain ⟨hcap, ht⟩ := eulerianLag_endpoints (P n) (P (n + 1)) (lam n)
        (m := D + (n + 1)) (by lia) ih1.1.le
      have hscalar : ((D + (n + 1) : ℕ) : ℝ) + 1 = (n : ℝ) + (D : ℝ) + 2 := by
        push_cast
        ring
      rw [hscalar, ← hrec n] at hcap ht
      have htop : 0 < (P (n + 2)).coeff (D + (n + 1) + 1) := by
        rw [ht]
        simpa [leadingCoeff, ih1.1] using ih1.2
      have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hcap htop.ne'
      exact ⟨by lia, by simpa [leadingCoeff, hdeg] using htop⟩

/-- The top two coefficients and degree cap of the polar current.
The coefficient formulas work for either input degree gap and any lag sign. -/
theorem polarLag_endpoints (p q : ℝ[X]) (u v b a lam : ℝ) {m : ℕ}
    (hm : m ≠ 0) (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m) :
    let r := (C u + C (v + (m : ℝ) * a) * X) * q +
      (C b * X + C (-a) * X ^ 2) * q.derivative + C lam * X * p
    r.natDegree ≤ m + 1 ∧
      r.coeff (m + 1) = v * q.coeff m + lam * p.coeff m ∧
      r.coeff m = (u + (m : ℝ) * b) * q.coeff m +
        (v + a) * q.coeff (m - 1) + lam * p.coeff (m - 1) := by
  intro r
  have hU : (C u + C (v + (m : ℝ) * a) * X).natDegree ≤ 1 := by compute_degree
  have hV : (C b * X + C (-a) * X ^ 2).natDegree ≤ 2 := by compute_degree
  have hL : (C lam * X).natDegree ≤ 1 := by compute_degree
  refine ⟨natDegree_step_le (δ := 0) hU hV hL hp hq (by simp), ?_, ?_⟩
  · dsimp only [r]
    rw [coeff_step_succ (δ := 0) hU hV hL hp hq (by simp)]
    norm_num [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
    dsimp only [r]
    rw [coeff_add, add_comm (_ * q) (_ * q.derivative),
      coeff_quadratic_derivative_add_linear_mul_succ,
      show C lam * X * p = C lam * (X * p) by ring, coeff_C_mul, coeff_X_mul]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

end RealRooted.BandOne
