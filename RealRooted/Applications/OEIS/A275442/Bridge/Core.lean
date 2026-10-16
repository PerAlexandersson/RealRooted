module

public import Mathlib

/-!
# The A275442 lag-four bridge family

This is the recurrence-defined family used by the scalar sign certificate.

The complete proof was found in Aristotle project
`03ba9e1b-e21f-4e02-9ce6-d02a00ee9a94`, task
`5bb91360-22c0-484e-8374-6d8fdfb81f27`, and replayed against this project's
Lean 4.31 toolchain. The port keeps only the dependency chain needed by
A275442.
-/

@[expose] public noncomputable section

namespace RealRooted.Applications.OEIS.A275442.Bridge

open Polynomial

/-- The polynomial family `p` of the problem. -/
def p : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | (n + 4) => p (n + 3) + p (n + 2) + X * p n

/-- The bridge polynomials `b n = p (n+2) + X * p n`. -/
def b (n : ℕ) : ℝ[X] := p (n + 2) + X * p n

@[simp] theorem p_zero : p 0 = 1 := rfl
@[simp] theorem p_one : p 1 = 1 := rfl
@[simp] theorem p_two : p 2 = 1 := rfl
@[simp] theorem p_three : p 3 = 2 := rfl

theorem p_rec (n : ℕ) : p (n + 4) = p (n + 3) + p (n + 2) + X * p n := rfl

theorem b_eq_sub (n : ℕ) : b n = p (n + 4) - p (n + 3) := by
  rw [p_rec, b]; ring

theorem p_succ_eq (n : ℕ) : p (n + 4) = p (n + 3) + b n := by
  rw [b_eq_sub]; ring

/-- The bridge family satisfies the same lag-four recurrence. -/
theorem b_rec (n : ℕ) : b (n + 4) = b (n + 3) + b (n + 2) + X * b n := by
  simp only [b, p_rec]
  ring

/-- Evaluation form of the recurrence. -/
theorem eval_p_rec (x : ℝ) (n : ℕ) :
    (p (n + 4)).eval x = (p (n + 3)).eval x + (p (n + 2)).eval x + x * (p n).eval x := by
  rw [p_rec]; simp

theorem eval_b (x : ℝ) (n : ℕ) : (b n).eval x = (p (n + 2)).eval x + x * (p n).eval x := by
  simp [b]

/-! ### All real zeros lie strictly left of `-1` -/

/-- On `[-1, ∞)` the values `p n` are at least `1` and nondecreasing in `n`. -/
theorem one_le_eval_and_mono (x : ℝ) (hx : -1 ≤ x) :
    ∀ n : ℕ, 1 ≤ (p n).eval x ∧ (p n).eval x ≤ (p (n + 1)).eval x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨by simp, by simp⟩
    | 1 => exact ⟨by simp, by simp⟩
    | 2 => exact ⟨by simp, by norm_num⟩
    | 3 =>
      have h4 : (p 4).eval x = (p 3).eval x + (p 2).eval x + x * (p 0).eval x := eval_p_rec x 0
      simp only [p_zero, p_two, p_three, eval_ofNat, eval_one, mul_one] at h4
      refine ⟨by norm_num, ?_⟩
      simp only [p_three, eval_ofNat]
      rw [h4]
      norm_num
      linarith
    | (n + 4) =>
      have hn := ih n (by lia)
      have hn1 := ih (n + 1) (by lia)
      have hn2 := ih (n + 2) (by lia)
      have hn3 := ih (n + 3) (by lia)
      have h4 : (p (n + 4)).eval x
          = (p (n + 3)).eval x + (p (n + 2)).eval x + x * (p n).eval x := eval_p_rec x n
      have h5 : (p (n + 5)).eval x
          = (p (n + 4)).eval x + (p (n + 3)).eval x + x * (p (n + 1)).eval x := eval_p_rec x (n + 1)
      have hmono' : (p (n + 1)).eval x ≤ (p (n + 3)).eval x := le_trans hn1.2 hn2.2
      have hprod : 0 ≤ (p (n + 1)).eval x + x * (p (n + 1)).eval x := by
        nlinarith [hn1.1]
      exact ⟨by linarith [hn3.1, hn3.2], by linarith⟩

theorem one_le_eval (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 ≤ (p n).eval x :=
  (one_le_eval_and_mono x hx n).1

theorem eval_mono (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : (p n).eval x ≤ (p (n + 1)).eval x :=
  (one_le_eval_and_mono x hx n).2

/-- Every real zero of every `p n` is strictly smaller than `-1`. -/
theorem root_lt_neg_one {n : ℕ} {r : ℝ} (hr : (p n).IsRoot r) : r < -1 := by
  by_contra h
  push Not at h
  have h1 := one_le_eval r h n
  rw [IsRoot.def] at hr
  rw [hr] at h1
  linarith

end RealRooted.Applications.OEIS.A275442.Bridge
