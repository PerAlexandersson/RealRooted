module

public import RealRooted.DerivativeRecurrence.General
import RealRooted.Recurrence.Uniqueness

/-!
# Evaluation of differential recurrences

Evaluating a finite-lag differential recurrence at a point where every positive-order
derivative multiplier vanishes produces a scalar recurrence.  Matching initial values
then identify all polynomial evaluations with a prescribed scalar solution.
-/

public section

open Polynomial

namespace RealRooted

namespace LinRec

/-- At a point where all positive-order derivative multipliers vanish, only the
undifferentiated terms contribute to the evaluation of a linear-recurrence right side. -/
theorem eval_rhs_eq_sum_zero_order {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    {P : ℕ → ℝ[X]} {n : ℕ} {xi : ℝ}
    (hzero : ∀ t ∈ terms, t.2.1 ≠ 0 → (t.2.2 n).eval xi = 0) :
    (rhs terms P n).eval xi =
      (terms.map fun t =>
        if t.2.1 = 0 then (t.2.2 n).eval xi * (P (n + t.1)).eval xi else 0).sum := by
  simp only [rhs, eval_listSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  by_cases ht0 : t.2.1 = 0
  · simp [ht0]
  · simp [ht0, hzero t ht ht0]

end LinRec

/-- A polynomial differential recurrence and a scalar recurrence with the same initial
values have matching evaluations when positive-order derivative multipliers vanish at the
evaluation point. -/
theorem eval_eq_of_differential_recurrence
    {k : ℕ} {P : ℕ → ℝ[X]} {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    {R s : ℕ → ℝ} {xi : ℝ}
    (hrec : ∀ n, C (R n) * P (n + k) = LinRec.rhs terms P n)
    (hlag : ∀ t ∈ terms, t.1 < k) (hR : ∀ n, R n ≠ 0)
    (hzero : ∀ n, ∀ t ∈ terms, t.2.1 ≠ 0 → (t.2.2 n).eval xi = 0)
    (hscalar : ∀ n, R n * s (n + k) =
      (terms.map fun t =>
        if t.2.1 = 0 then (t.2.2 n).eval xi * s (n + t.1) else 0).sum)
    (hbase : ∀ i < k, (P i).eval xi = s i) (n : ℕ) :
    (P n).eval xi = s n := by
  let op : ℕ → (Fin k → ℝ) → ℝ := fun m x =>
    (R m)⁻¹ * (terms.map fun t =>
      if ht : t.1 < k then
        if t.2.1 = 0 then (t.2.2 m).eval xi * x ⟨t.1, ht⟩ else 0
      else 0).sum
  refine sequence_eq_of_same_finite_recurrence (op := op) hbase ?_ ?_ n
  · intro m
    dsimp only [op]
    apply mul_left_cancel₀ (hR m)
    have heval := congrArg (Polynomial.eval xi) (hrec m)
    rw [eval_mul, eval_C, LinRec.eval_rhs_eq_sum_zero_order (hzero m)] at heval
    rw [heval]
    rw [← mul_assoc, mul_inv_cancel₀ (hR m), one_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    rw [dite_eq_left (hlag t ht)]
  · intro m
    dsimp only [op]
    apply mul_left_cancel₀ (hR m)
    rw [hscalar m]
    rw [← mul_assoc, mul_inv_cancel₀ (hR m), one_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    rw [dite_eq_left (hlag t ht)]

/-- Under the evaluation theorem's hypotheses, a nonzero scalar value certifies that the
corresponding polynomial row is nonzero. -/
theorem ne_zero_of_differential_recurrence_of_scalar_ne_zero
    {k : ℕ} {P : ℕ → ℝ[X]} {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    {R s : ℕ → ℝ} {xi : ℝ}
    (hrec : ∀ n, C (R n) * P (n + k) = LinRec.rhs terms P n)
    (hlag : ∀ t ∈ terms, t.1 < k) (hR : ∀ n, R n ≠ 0)
    (hzero : ∀ n, ∀ t ∈ terms, t.2.1 ≠ 0 → (t.2.2 n).eval xi = 0)
    (hscalar : ∀ n, R n * s (n + k) =
      (terms.map fun t =>
        if t.2.1 = 0 then (t.2.2 n).eval xi * s (n + t.1) else 0).sum)
    (hbase : ∀ i < k, (P i).eval xi = s i) {n : ℕ} (hs : s n ≠ 0) :
    P n ≠ 0 := by
  intro hP
  have h := eval_eq_of_differential_recurrence hrec hlag hR hzero hscalar hbase n
  rw [hP, eval_zero] at h
  exact hs h.symm

/-- If the zero-order multiplier evaluations sum to the nonzero left multiplier and the
initial evaluations are one, then every polynomial row evaluates to one. -/
theorem eval_eq_one_of_differential_recurrence
    {k : ℕ} {P : ℕ → ℝ[X]} {terms : List (ℕ × ℕ × (ℕ → ℝ[X]))}
    {R : ℕ → ℝ} {xi : ℝ}
    (hrec : ∀ n, C (R n) * P (n + k) = LinRec.rhs terms P n)
    (hlag : ∀ t ∈ terms, t.1 < k) (hR : ∀ n, R n ≠ 0)
    (hzero : ∀ n, ∀ t ∈ terms, t.2.1 ≠ 0 → (t.2.2 n).eval xi = 0)
    (hsum : ∀ n,
      (terms.map fun t => if t.2.1 = 0 then (t.2.2 n).eval xi else 0).sum = R n)
    (hbase : ∀ i < k, (P i).eval xi = 1) (n : ℕ) :
    (P n).eval xi = 1 := by
  apply eval_eq_of_differential_recurrence hrec hlag hR hzero
    (s := fun _ => 1) _ hbase n
  intro m
  simpa only [mul_one] using (hsum m).symm

end RealRooted
