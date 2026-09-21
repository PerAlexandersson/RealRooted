import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Grind

/-!
# Finite divided differences

This file defines the divided difference of a polynomial at a nonempty finite
ordered family of nodes.  The indexing by `Fin (n + 1)` makes the recursive
deletion of the first or last node explicit and avoids a separate convention
for the empty family.

The linear-factor product rule is the finite algebraic input used in the
Micchelli--Willoughby spectral-product argument.
-/

open Finset

namespace Polynomial

variable {K : Type*} [Field K]

/-- The order-`n` divided difference of `p` at the nodes `v 0, ..., v n`. -/
noncomputable def dividedDifference :
    (n : ℕ) → (Fin (n + 1) → K) → K[X] → K
  | 0, v, p => p.eval (v 0)
  | n + 1, v, p =>
      (dividedDifference n (fun i => v i.succ) p -
          dividedDifference n (fun i => v i.castSucc) p) /
        (v (Fin.last (n + 1)) - v 0)

@[simp]
theorem dividedDifference_zero (v : Fin 1 → K) (p : K[X]) :
    dividedDifference 0 v p = p.eval (v 0) :=
  rfl

theorem dividedDifference_succ (n : ℕ) (v : Fin (n + 2) → K) (p : K[X]) :
    dividedDifference (n + 1) v p =
      (dividedDifference n (fun i => v i.succ) p -
          dividedDifference n (fun i => v i.castSucc) p) /
        (v (Fin.last (n + 1)) - v 0) :=
  rfl

@[simp]
theorem dividedDifference_zero_polynomial (n : ℕ) (v : Fin (n + 1) → K) :
    dividedDifference n v 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [dividedDifference_succ, ih]

theorem dividedDifference_add (n : ℕ) (v : Fin (n + 1) → K) (p q : K[X]) :
    dividedDifference n v (p + q) =
      dividedDifference n v p + dividedDifference n v q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [dividedDifference_succ, dividedDifference_succ, dividedDifference_succ]
      rw [ih, ih]
      ring

theorem dividedDifference_smul (n : ℕ) (v : Fin (n + 1) → K) (a : K) (p : K[X]) :
    dividedDifference n v (a • p) = a * dividedDifference n v p := by
  induction n with
  | zero => exact Polynomial.eval_smul a p (v 0)
  | succ n ih =>
      rw [dividedDifference_succ, dividedDifference_succ]
      rw [ih, ih]
      ring

theorem dividedDifference_finset_sum {ι : Type*} (s : Finset ι)
    (n : ℕ) (v : Fin (n + 1) → K) (p : ι → K[X]) :
    dividedDifference n v (∑ i ∈ s, p i) =
      ∑ i ∈ s, dividedDifference n v (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, dividedDifference_add]

/-- A divided difference vanishes when the polynomial vanishes at every one
of its nodes. -/
theorem dividedDifference_eq_zero_of_eval_eq_zero (n : ℕ)
    (v : Fin (n + 1) → K) (p : K[X]) (hp : ∀ i, p.eval (v i) = 0) :
    dividedDifference n v p = 0 := by
  induction n with
  | zero => simpa using hp 0
  | succ n ih =>
      rw [dividedDifference_succ]
      rw [ih _ (fun i => hp i.succ), ih _ (fun i => hp i.castSucc)]
      simp

omit [Field K] in
private theorem injective_succ {n : ℕ} {v : Fin (n + 2) → K}
    (hv : Function.Injective v) : Function.Injective (fun i : Fin (n + 1) => v i.succ) :=
  hv.comp (Fin.succ_injective (n + 1))

omit [Field K] in
private theorem injective_castSucc {n : ℕ} {v : Fin (n + 2) → K}
    (hv : Function.Injective v) :
    Function.Injective (fun i : Fin (n + 1) => v i.castSucc) :=
  hv.comp (Fin.castSucc_injective (n + 1))

@[simp]
theorem dividedDifference_zero_mul_X_sub_C (v : Fin 1 → K) (p : K[X]) (r : K) :
    dividedDifference 0 v (p * (X - C r)) =
      dividedDifference 0 v p * (v 0 - r) := by
  simp

/-- Multiplication by a linear factor obeys the two-term divided-difference
product rule. -/
theorem dividedDifference_mul_X_sub_C :
    ∀ (n : ℕ) (v : Fin (n + 2) → K), Function.Injective v →
      ∀ (p : K[X]) (r : K),
        dividedDifference (n + 1) v (p * (X - C r)) =
          dividedDifference (n + 1) v p * (v (Fin.last (n + 1)) - r) +
            dividedDifference n (fun i : Fin (n + 1) => v i.castSucc) p := by
  intro n
  induction n with
  | zero =>
      intro v hv p r
      rw [dividedDifference_succ 0 v, dividedDifference_succ 0 v]
      simp only [dividedDifference_zero_mul_X_sub_C]
      have hden : v (Fin.last 1) - v 0 ≠ 0 := by
        apply sub_ne_zero.mpr
        exact hv.ne (by simp)
      have hsucc : (Fin.succ 0 : Fin 2) = Fin.last 1 := rfl
      have hcast : (Fin.castSucc 0 : Fin 2) = 0 := rfl
      field_simp
      rw [hsucc, hcast]
      ring
  | succ n ih =>
      intro v hv p r
      rw [dividedDifference_succ (n + 1) v]
      rw [ih _ (injective_succ hv), ih _ (injective_castSucc hv)]
      rw [dividedDifference_succ (n + 1) v p]
      rw [dividedDifference_succ n (fun i : Fin (n + 2) => v i.castSucc) p]
      have hlast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
        apply Fin.ext
        simp
      have hmiddle :
          (fun i : Fin (n + 1) => v i.castSucc.succ) =
            fun i : Fin (n + 1) => v i.succ.castSucc := by
        funext i
        congr 1
      have hzero : (Fin.castSucc 0 : Fin (n + 3)) = 0 := rfl
      rw [hlast, hmiddle, hzero]
      have hden : v (Fin.last (n + 2)) - v 0 ≠ 0 := by
        apply sub_ne_zero.mpr
        exact hv.ne (by simp)
      have htail : v (Fin.last (n + 2)) - v (Fin.succ 0) ≠ 0 := by
        apply sub_ne_zero.mpr
        apply hv.ne
        apply Fin.ne_of_gt
        change 1 < n + 2
        exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 n)
      have hinit : v (Fin.last (n + 1)).castSucc - v 0 ≠ 0 := by
        apply sub_ne_zero.mpr
        exact hv.ne (by simp)
      field_simp
      ring

@[simp]
theorem dividedDifference_one_succ (n : ℕ) (v : Fin (n + 2) → K) :
    dividedDifference (n + 1) v 1 = 0 := by
  induction n with
  | zero => simp [dividedDifference_succ]
  | succ n ih =>
      rw [dividedDifference_succ]
      rw [ih, ih]
      simp

/-- A divided difference whose order is larger than the number of monic linear
factors vanishes. -/
theorem dividedDifference_prod_X_sub_C_eq_zero_of_lt :
    ∀ {k n : ℕ} (ν : Fin k → K) (v : Fin (n + 1) → K),
      Function.Injective v → k < n →
        dividedDifference n v (∏ i, (X - C (ν i))) = 0 := by
  intro k
  induction k with
  | zero =>
      intro n ν v _ hkn
      cases n with
      | zero => simp at hkn
      | succ n => simp
  | succ k ih =>
      intro n ν v hv hkn
      cases n with
      | zero => simp at hkn
      | succ n =>
          have hk_lower : k < n := Nat.lt_of_succ_lt_succ hkn
          have hk_same : k < n + 1 := hk_lower.trans (Nat.lt_succ_self n)
          rw [Fin.prod_univ_castSucc]
          rw [dividedDifference_mul_X_sub_C n v hv]
          rw [ih _ _ hv hk_same, ih _ _ (injective_castSucc hv) hk_lower]
          simp

/-- The top divided difference of a monic product of `n` linear factors is
one. -/
theorem dividedDifference_prod_X_sub_C_eq_one :
    ∀ {n : ℕ} (ν : Fin n → K) (v : Fin (n + 1) → K),
      Function.Injective v →
        dividedDifference n v (∏ i, (X - C (ν i))) = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro ν v hv
      rw [Fin.prod_univ_castSucc]
      rw [dividedDifference_mul_X_sub_C n v hv]
      rw [dividedDifference_prod_X_sub_C_eq_zero_of_lt _ _ hv (Nat.lt_succ_self n)]
      rw [ih _ _ (injective_castSucc hv)]
      simp

private theorem strictMono_castSucc {m : ℕ} {f : Fin (m + 1) → ℝ}
    (hf : StrictMono f) : StrictMono (fun i : Fin m => f i.castSucc) :=
  fun _ _ hij => hf (Fin.castSucc_lt_castSucc_iff.mpr hij)

/-- Positivity of the divided differences used in the finite
Micchelli--Willoughby argument.  The roots are ordered, the nodes are strictly
ordered, and node `i` lies weakly to the right of root `b + i`. -/
theorem dividedDifference_prod_X_sub_C_nonneg :
    ∀ (n b : ℕ) (ν : ℕ → ℝ) (v : Fin (n + 1) → ℝ),
      Monotone ν → StrictMono v →
        (∀ i : Fin (n + 1), ν (b + (i : ℕ)) ≤ v i) →
          0 ≤ dividedDifference n v
            (∏ i ∈ Finset.range (b + n + 1), (X - C (ν i))) := by
  intro n
  induction n with
  | zero =>
      intro b ν v hν _ hdom
      simp only [dividedDifference_zero, eval_prod, eval_sub, eval_X, eval_C]
      apply Finset.prod_nonneg
      intro i hi
      apply sub_nonneg.mpr
      exact (hν (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).trans (by simpa using hdom 0)
  | succ n ihn =>
      intro b
      induction b with
      | zero =>
          intro ν v hν hv hdom
          simp only [Nat.zero_add] at hdom ⊢
          rw [Finset.prod_range_succ]
          rw [dividedDifference_mul_X_sub_C n v hv.injective]
          have htop :
              dividedDifference (n + 1) v
                  (∏ i ∈ Finset.range (n + 1), (X - C (ν i))) = 1 := by
            rw [Finset.prod_range]
            exact dividedDifference_prod_X_sub_C_eq_one
              (fun i : Fin (n + 1) => ν i) v hv.injective
          have hfactor : 0 ≤ v (Fin.last (n + 1)) - ν (n + 1) := by
            exact sub_nonneg.mpr (by simpa using hdom (Fin.last (n + 1)))
          have hlower :
              0 ≤ dividedDifference n (fun i : Fin (n + 1) => v i.castSucc)
                (∏ i ∈ Finset.range (n + 1), (X - C (ν i))) := by
            have H := ihn 0 ν (fun i : Fin (n + 1) => v i.castSucc)
              hν (strictMono_castSucc hv) (by
                intro i
                simpa using hdom i.castSucc)
            simpa only [Nat.zero_add] using H
          rw [htop, one_mul]
          exact add_nonneg hfactor hlower
      | succ b ihb =>
          intro ν v hν hv hdom
          simp only [Nat.succ_add] at hdom ⊢
          rw [Finset.prod_range_succ]
          rw [dividedDifference_mul_X_sub_C n v hv.injective]
          have hupper :
              0 ≤ dividedDifference (n + 1) v
                (∏ i ∈ Finset.range ((b + 1) + (n + 1)), (X - C (ν i))) := by
            have H := ihb ν v hν hv (by
              intro i
              apply (hν ?_).trans (hdom i)
              change b + (i : ℕ) ≤ (b + (i : ℕ)) + 1
              simp)
            have hcount : b + (n + 1) + 1 = (b + 1) + (n + 1) := by lia
            simpa only [hcount] using H
          have hfactor :
              0 ≤ v (Fin.last (n + 1)) - ν ((b + 1) + (n + 1)) := by
            apply sub_nonneg.mpr
            have hidx : (b + (Fin.last (n + 1) : ℕ)).succ =
                (b + 1) + (n + 1) := by
              change (b + (n + 1)).succ = (b + 1) + (n + 1)
              lia
            simpa only [hidx] using hdom (Fin.last (n + 1))
          have hlower :
              0 ≤ dividedDifference n (fun i : Fin (n + 1) => v i.castSucc)
                (∏ i ∈ Finset.range ((b + 1) + (n + 1)), (X - C (ν i))) := by
            have H := ihn (b + 1) ν (fun i : Fin (n + 1) => v i.castSucc)
              hν (strictMono_castSucc hv) (by
                intro i
                have hidx : (b + (i : ℕ)).succ = (b + 1) + (i : ℕ) := by lia
                simpa only [Fin.val_castSucc, hidx] using hdom i.castSucc)
            have hcount : (b + 1) + n + 1 = (b + 1) + (n + 1) := by lia
            simpa only [hcount] using H
          have hcount : (b + 1) + (n + 1) = b + (n + 1) + 1 := by lia
          simpa only [hcount] using add_nonneg (mul_nonneg hupper hfactor) hlower

end Polynomial
