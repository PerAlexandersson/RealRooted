import RealRooted.Basic
import RealRooted.Tactic.Named

/-!
# Recurrence base-case evaluation tactic

Generated proof rows use `recurrence_eval` for small polynomial equalities
obtained by unfolding a sequence recurrence and normalizing coefficients.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Normalize coefficient products around one `X` for recurrence base-case checks. -/
theorem recurrenceEval_C_mul_X_mul_C {R : Type _} [CommSemiring R] (a b : R) :
    (C a * X * C b : R[X]) = C (a * b) * X := by
  rw [mul_assoc, Polynomial.X_mul_C, ← mul_assoc, ← Polynomial.C_mul]

/-- Normalize coefficient products around `X ^ n` for recurrence base-case checks. -/
theorem recurrenceEval_C_mul_X_pow_mul_C {R : Type _} [CommSemiring R]
    (a b : R) (n : Nat) :
    (C a * X ^ n * C b : R[X]) = C (a * b) * X ^ n := by
  rw [mul_assoc, Polynomial.X_pow_mul_C, ← mul_assoc, ← Polynomial.C_mul]

/-- Normalize coefficient products before one `X` for recurrence base-case checks. -/
theorem recurrenceEval_C_mul_C_mul_X {R : Type _} [CommSemiring R] (a b : R) :
    (C a * C b * X : R[X]) = C (a * b) * X := by
  rw [← Polynomial.C_mul]

/-- Normalize coefficient products before `X ^ n` for recurrence base-case checks. -/
theorem recurrenceEval_C_mul_C_mul_X_pow {R : Type _} [CommSemiring R]
    (a b : R) (n : Nat) :
    (C a * C b * X ^ n : R[X]) = C (a * b) * X ^ n := by
  rw [← Polynomial.C_mul]

/-- Normalize coefficient products after one `X` for recurrence base-case checks. -/
theorem recurrenceEval_X_mul_C_mul_C {R : Type _} [CommSemiring R] (a b : R) :
    (X * C a * C b : R[X]) = C (a * b) * X := by
  rw [Polynomial.X_mul_C, recurrenceEval_C_mul_X_mul_C]

/-- Normalize coefficient products after `X ^ n` for recurrence base-case checks. -/
theorem recurrenceEval_X_pow_mul_C_mul_C {R : Type _} [CommSemiring R]
    (a b : R) (n : Nat) :
    (X ^ n * C a * C b : R[X]) = C (a * b) * X ^ n := by
  rw [Polynomial.X_pow_mul_C, recurrenceEval_C_mul_X_pow_mul_C]

/-- Merge adjacent constants during recurrence base-case normalization. -/
theorem recurrenceEval_C_add_C_assoc {R : Type _} [CommSemiring R]
    (a b : R) (q : R[X]) :
    C a + (C b + q) = C (a + b) + q := by
  rw [← add_assoc, ← Polynomial.C_add]

/-- Merge adjacent constant multiples during recurrence base-case normalization. -/
theorem recurrenceEval_C_add_C_mul_assoc {R : Type _} [CommSemiring R]
    (a b : R) (p q : R[X]) :
    C a * p + (C b * p + q) = C (a + b) * p + q := by
  rw [← add_assoc, ← add_mul, ← Polynomial.C_add]

/-- Merge adjacent `X ^ n` terms during recurrence base-case normalization. -/
theorem recurrenceEval_X_pow_mul_C_add_C_assoc {R : Type _} [CommSemiring R]
    (a b : R) (n : Nat) (q : R[X]) :
    X ^ n * C a + (X ^ n * C b + q) = X ^ n * C (a + b) + q := by
  rw [← add_assoc, ← mul_add, ← Polynomial.C_add]

/-- Merge adjacent `X` terms during recurrence base-case normalization. -/
theorem recurrenceEval_X_mul_C_add_C_assoc {R : Type _} [CommSemiring R]
    (a b : R) (q : R[X]) :
    X * C a + (X * C b + q) = X * C (a + b) + q := by
  rw [← add_assoc, ← mul_add, ← Polynomial.C_add]

theorem recurrenceEval_neg_C_mul_X_pow (a : ℝ) (n : Nat) :
    (-(C a * X ^ n) : ℝ[X]) = C (-a) * X ^ n := by
  rw [← neg_mul, ← Polynomial.C_neg]

theorem recurrenceEval_neg_C_mul_X (a : ℝ) :
    (-(C a * X) : ℝ[X]) = C (-a) * X := by
  rw [← neg_mul, ← Polynomial.C_neg]

theorem recurrenceEval_neg_C (a : ℝ) :
    (-C a : ℝ[X]) = C (-a) := by
  rw [← Polynomial.C_neg]

theorem recurrenceEval_degree_swap_4_3 (a b : ℝ) :
    (C a * X ^ 4 + C b * X ^ 3 : ℝ[X]) = C b * X ^ 3 + C a * X ^ 4 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_4_3_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 4 + (C b * X ^ 3 + q) : ℝ[X]) =
      C b * X ^ 3 + (C a * X ^ 4 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 4), add_assoc]

theorem recurrenceEval_degree_swap_4_2 (a b : ℝ) :
    (C a * X ^ 4 + C b * X ^ 2 : ℝ[X]) = C b * X ^ 2 + C a * X ^ 4 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_4_2_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 4 + (C b * X ^ 2 + q) : ℝ[X]) =
      C b * X ^ 2 + (C a * X ^ 4 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 4), add_assoc]

theorem recurrenceEval_degree_swap_4_1 (a b : ℝ) :
    (C a * X ^ 4 + C b * X : ℝ[X]) = C b * X + C a * X ^ 4 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_4_1_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 4 + (C b * X + q) : ℝ[X]) =
      C b * X + (C a * X ^ 4 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 4), add_assoc]

theorem recurrenceEval_degree_swap_4_0 (a b : ℝ) :
    (C a * X ^ 4 + C b : ℝ[X]) = C b + C a * X ^ 4 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_4_0_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 4 + (C b + q) : ℝ[X]) =
      C b + (C a * X ^ 4 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 4), add_assoc]

theorem recurrenceEval_degree_swap_3_2 (a b : ℝ) :
    (C a * X ^ 3 + C b * X ^ 2 : ℝ[X]) = C b * X ^ 2 + C a * X ^ 3 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_3_2_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 3 + (C b * X ^ 2 + q) : ℝ[X]) =
      C b * X ^ 2 + (C a * X ^ 3 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 3), add_assoc]

theorem recurrenceEval_degree_swap_3_1 (a b : ℝ) :
    (C a * X ^ 3 + C b * X : ℝ[X]) = C b * X + C a * X ^ 3 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_3_1_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 3 + (C b * X + q) : ℝ[X]) =
      C b * X + (C a * X ^ 3 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 3), add_assoc]

theorem recurrenceEval_degree_swap_3_0 (a b : ℝ) :
    (C a * X ^ 3 + C b : ℝ[X]) = C b + C a * X ^ 3 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_3_0_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 3 + (C b + q) : ℝ[X]) =
      C b + (C a * X ^ 3 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 3), add_assoc]

theorem recurrenceEval_degree_swap_2_1 (a b : ℝ) :
    (C a * X ^ 2 + C b * X : ℝ[X]) = C b * X + C a * X ^ 2 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_2_1_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 2 + (C b * X + q) : ℝ[X]) =
      C b * X + (C a * X ^ 2 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 2), add_assoc]

theorem recurrenceEval_degree_swap_2_0 (a b : ℝ) :
    (C a * X ^ 2 + C b : ℝ[X]) = C b + C a * X ^ 2 := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_2_0_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X ^ 2 + (C b + q) : ℝ[X]) =
      C b + (C a * X ^ 2 + q) := by
  rw [← add_assoc, add_comm (C a * X ^ 2), add_assoc]

theorem recurrenceEval_degree_swap_1_0 (a b : ℝ) :
    (C a * X + C b : ℝ[X]) = C b + C a * X := by
  rw [add_comm]

theorem recurrenceEval_degree_swap_1_0_assoc (a b : ℝ) (q : ℝ[X]) :
    (C a * X + (C b + q) : ℝ[X]) = C b + (C a * X + q) := by
  rw [← add_assoc, add_comm (C a * X), add_assoc]

theorem recurrenceEval_merge_pow (a b : ℝ) (n : Nat) (q : ℝ[X]) :
    (C a * X ^ n + (C b * X ^ n + q) : ℝ[X]) = C (a + b) * X ^ n + q := by
  rw [← add_assoc, ← add_mul, ← Polynomial.C_add]

theorem recurrenceEval_merge_pow_end (a b : ℝ) (n : Nat) :
    (C a * X ^ n + C b * X ^ n : ℝ[X]) = C (a + b) * X ^ n := by
  rw [← add_mul, ← Polynomial.C_add]

theorem recurrenceEval_merge_X (a b : ℝ) (q : ℝ[X]) :
    (C a * X + (C b * X + q) : ℝ[X]) = C (a + b) * X + q := by
  rw [← add_assoc, ← add_mul, ← Polynomial.C_add]

theorem recurrenceEval_merge_X_end (a b : ℝ) :
    (C a * X + C b * X : ℝ[X]) = C (a + b) * X := by
  rw [← add_mul, ← Polynomial.C_add]

theorem recurrenceEval_merge_C (a b : ℝ) (q : ℝ[X]) :
    (C a + (C b + q) : ℝ[X]) = C (a + b) + q := by
  rw [← add_assoc, ← Polynomial.C_add]

theorem recurrenceEval_merge_C_end (a b : ℝ) :
    (C a + C b : ℝ[X]) = C (a + b) := by
  rw [← Polynomial.C_add]

open Lean
open Lean.Meta
open Lean.Elab.Tactic

private def evalAndClose? (stx : TSyntax `tactic) : TacticM Bool := do
  evalTactic stx
  return (← getGoals).isEmpty

private def evalAndCloseSafely? (stx : TSyntax `tactic) : TacticM Bool := do
  let result? ← observing? do
    evalAndClose? stx
  return result?.getD false

elab "recurrence_eval" : tactic => do
  withOptions (fun o => Lean.maxRecDepth.set o 200000) do
    withMainContext do
      let target ← getMainTarget
      let some (cName, _) ← findNamedPolynomialConstantApp? target
        | throwError
            "recurrence_eval failed: could not find named polynomial recurrence in target: {target}"
      let cIdent := mkIdent cName
      if ← evalAndClose? (← `(tactic| dsimp [$cIdent:ident])) then return
      if ← evalAndCloseSafely? (← `(tactic| (
        simp (config := { failIfUnchanged := false }) only [
          Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
          Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_zero,
          mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero
        ]; ring))) then return
      if ← evalAndCloseSafely? (← `(tactic| (
        simp (config := { failIfUnchanged := false }) only [
          Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
          Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_zero,
          mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero
        ]; ring_nf))) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
        Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_zero,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero
      ])) then return
      if ← evalAndCloseSafely? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
        Polynomial.derivative_X, Polynomial.derivative_pow, Polynomial.derivative_sub,
        Polynomial.derivative_neg, Polynomial.derivative_one, Polynomial.derivative_zero,
        Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_add, Nat.cast_mul,
        Nat.cast_pow, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
        sub_zero, mul_pow
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        add_mul, mul_add, sub_mul, mul_sub, mul_one, one_mul
      ])) then return
      if ← evalAndClose? (← `(tactic| norm_num)) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← map_ofNat Polynomial.C, Polynomial.X_mul_C, Polynomial.X_pow_mul_C
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        add_assoc
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← Polynomial.C_add, ← Polynomial.C_mul, ← Polynomial.C_sub,
        ← Polynomial.C_neg, ← Polynomial.C_pow,
        recurrenceEval_C_mul_X_mul_C, recurrenceEval_C_mul_X_pow_mul_C,
        recurrenceEval_C_mul_C_mul_X, recurrenceEval_C_mul_C_mul_X_pow,
        recurrenceEval_C_add_C_assoc, recurrenceEval_C_add_C_mul_assoc,
        Polynomial.X_mul_C, Polynomial.X_pow_mul_C,
        ← add_mul, ← mul_add, ← sub_mul, ← mul_sub,
        ← mul_assoc, ← pow_two, ← neg_mul
      ])) then return
      if ← evalAndClose? (← `(tactic| norm_num)) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← Polynomial.X_mul_C, ← Polynomial.X_pow_mul_C
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← map_ofNat Polynomial.C, ← Polynomial.C_eq_natCast,
        ← Polynomial.C_eq_intCast, ← Polynomial.C_pow, sub_eq_add_neg
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← Polynomial.C_neg, ← mul_neg, mul_assoc
      ])) then return
      if ← evalAndClose? (← `(tactic| ring_nf)) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← map_ofNat Polynomial.C, ← Polynomial.C_eq_natCast,
        ← Polynomial.C_eq_intCast, ← Polynomial.C_pow, sub_eq_add_neg
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        recurrenceEval_C_mul_X_pow_mul_C, recurrenceEval_C_mul_X_mul_C,
        recurrenceEval_X_pow_mul_C_mul_C, recurrenceEval_X_mul_C_mul_C
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        ← Polynomial.X_mul_C, ← Polynomial.X_pow_mul_C,
        ← Polynomial.C_neg, ← mul_neg, mul_assoc
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        add_assoc, recurrenceEval_X_mul_C_add_C_assoc,
        recurrenceEval_X_pow_mul_C_add_C_assoc, recurrenceEval_C_add_C_assoc,
        ← Polynomial.C_add, ← mul_add
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        add_comm, add_assoc, add_left_comm
      ])) then return
      if ← evalAndClose? (← `(tactic| simp (config := { failIfUnchanged := false }) only [
        add_assoc, recurrenceEval_X_mul_C_add_C_assoc,
        recurrenceEval_X_pow_mul_C_add_C_assoc, recurrenceEval_C_add_C_assoc,
        ← Polynomial.C_add, ← mul_add
      ])) then return
      if ← evalAndCloseSafely? (← `(tactic| norm_num)) then return
      if ← evalAndCloseSafely? (← `(tactic| ring)) then return
      throwError "recurrence_eval failed to close target after normalization"

end Tactic
end RealRooted
