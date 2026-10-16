module

public import RealRooted.DerivativeRecurrence.General

/-!
# Invariant cones for scalar recurrences

A scalar recurrence of order `k` acts on the window
`(c n, c (n + 1), ..., c (n + k - 1))` by its companion step.  This file proves
that a cone cut out by finitely many linear forms is invariant when the companion
step preserves it.  Both closed and open cones are covered.  This gives positivity of top
coefficients of rows whose leading coefficients satisfy a scalar recurrence (issue #1322).
-/

@[expose] public section

namespace RealRooted.ScalarRec

/-- The length-`k` window of a scalar sequence starting at `n`. -/
def window (k : ℕ) (c : ℕ → ℝ) (n : ℕ) : Fin k → ℝ :=
  fun i => c (n + i)

/-- The companion step of the order-`k` recurrence with multipliers `m` at time `n`.
It shifts the first `k - 1` entries and fills the last entry with the recurrence sum. -/
noncomputable def companionStep (k : ℕ) (m : ℕ → ℕ → ℝ) (n : ℕ)
    (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if h : i.1 + 1 < k then x ⟨i.1 + 1, h⟩ else ∑ j : Fin k, m n j * x j

/-- The coordinate functional on recurrence windows. -/
def coordinate {k : ℕ} (i : Fin k) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Membership in the closed cone cut out by the finite family `forms`. -/
def FormsNonneg {k q : ℕ} (forms : Fin q → (Fin k → ℝ) →ₗ[ℝ] ℝ)
    (x : Fin k → ℝ) : Prop :=
  ∀ i, 0 ≤ forms i x

/-- Membership in the open cone cut out by the finite family `forms`. -/
def FormsPos {k q : ℕ} (forms : Fin q → (Fin k → ℝ) →ₗ[ℝ] ℝ)
    (x : Fin k → ℝ) : Prop :=
  ∀ i, 0 < forms i x

/-- Windows of a solution evolve by the companion step. -/
theorem window_succ_eq_companionStep {k : ℕ} {m : ℕ → ℕ → ℝ} {c : ℕ → ℝ}
    (hc : IsSolution k m c) (n : ℕ) :
    window k c (n + 1) = companionStep k m n (window k c n) := by
  funext i
  simp only [window, companionStep]
  split_ifs with hi
  · congr 1
    lia
  · have hilast : i.1 + 1 = k := by
      have := i.2
      lia
    have hindex : n + 1 + i.1 = n + k := by lia
    rw [hindex, hc n, Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    simp only [dite_eq_left hj]

/-- A closed cone cut out by finitely many linear forms contains every window of a
scalar recurrence if it contains the initial window and every companion step preserves it. -/
theorem FormsNonneg.window_of_companionStep {k q : ℕ} {m : ℕ → ℕ → ℝ}
    {c : ℕ → ℝ} {forms : Fin q → (Fin k → ℝ) →ₗ[ℝ] ℝ}
    (hc : IsSolution k m c) (hbase : FormsNonneg forms (window k c 0))
    (hstep : ∀ n x, FormsNonneg forms x →
      FormsNonneg forms (companionStep k m n x)) (n : ℕ) :
    FormsNonneg forms (window k c n) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
      rw [window_succ_eq_companionStep hc n]
      exact hstep n _ ih

/-- An open cone cut out by finitely many linear forms contains every window of a
scalar recurrence if it contains the initial window and every companion step preserves it. -/
theorem FormsPos.window_of_companionStep {k q : ℕ} {m : ℕ → ℕ → ℝ}
    {c : ℕ → ℝ} {forms : Fin q → (Fin k → ℝ) →ₗ[ℝ] ℝ}
    (hc : IsSolution k m c) (hbase : FormsPos forms (window k c 0))
    (hstep : ∀ n x, FormsPos forms x → FormsPos forms (companionStep k m n x))
    (n : ℕ) : FormsPos forms (window k c n) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
      rw [window_succ_eq_companionStep hc n]
      exact hstep n _ ih

/-! ### Regression examples from issue #1322 -/

/-- The recurrence with characteristic polynomial `(E - 1) (E - 2) (E - 4)` and
initial values of `(2^(n+1) - 1)^2` is positive. -/
theorem pos_of_one_two_four_rec (c : ℕ → ℝ)
    (hrec : ∀ n, c (n + 3) = 7 * c (n + 2) - 14 * c (n + 1) + 8 * c n)
    (hc0 : c 0 = 1) (hc1 : c 1 = 9) (hc2 : c 2 = 49) (n : ℕ) : 0 < c n := by
  let m : ℕ → ℕ → ℝ := fun _ j => if j = 0 then 8 else if j = 1 then -14 else 7
  let forms : Fin 3 → (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    ![coordinate 0, coordinate 1 - coordinate 0,
      coordinate 2 - 3 • coordinate 1 + 2 • coordinate 0]
  have hsol : IsSolution 3 m c := by
    intro r
    norm_num [m, Finset.sum_range_succ]
    linarith [hrec r]
  have hbase : FormsPos forms (window 3 c 0) := by
    intro i
    fin_cases i <;> norm_num [forms, coordinate, window, hc0, hc1, hc2]
  have hstep : ∀ r x, FormsPos forms x → FormsPos forms (companionStep 3 m r x) := by
    intro r x hx i
    have h0 := hx (0 : Fin 3)
    have h1 := hx (1 : Fin 3)
    have h2 := hx (2 : Fin 3)
    fin_cases i <;>
      norm_num [forms, coordinate, companionStep, m, Finset.sum_fin_eq_sum_range,
        Finset.sum_range_succ] at h0 h1 h2 ⊢ <;>
      linarith
  have hinv := FormsPos.window_of_companionStep (m := m) (c := c) (forms := forms)
    hsol hbase hstep n
  have h := hinv (0 : Fin 3)
  simpa [forms, coordinate, window] using h

/-- The closed form `(2^(n+1) - 1)^2` passes the order-three cone regression. -/
example (n : ℕ) : 0 < (((2 : ℝ) ^ (n + 1) - 1) ^ 2) := by
  apply pos_of_one_two_four_rec (n := n)
  · intro r
    simp only [pow_succ]
    ring
  · norm_num
  · norm_num
  · norm_num

/-- The order-four recurrence and initial values of `F(n+5) - n - 4` give a positive
sequence.  The invariant forms are the value, its first difference, and two consecutive
second differences. -/
theorem pos_of_fib_sub_linear_rec (c : ℕ → ℝ)
    (hrec : ∀ n,
      c (n + 4) = 3 * c (n + 3) - 2 * c (n + 2) - c (n + 1) + c n)
    (hc0 : c 0 = 1) (hc1 : c 1 = 3) (hc2 : c 2 = 7) (hc3 : c 3 = 14)
    (n : ℕ) : 0 < c n := by
  let m : ℕ → ℕ → ℝ := fun _ j =>
    if j = 0 then 1 else if j = 1 then -1 else if j = 2 then -2 else 3
  let forms : Fin 4 → (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
    ![coordinate 0, coordinate 1 - coordinate 0,
      coordinate 2 - 2 • coordinate 1 + coordinate 0,
      coordinate 3 - 2 • coordinate 2 + coordinate 1]
  have hsol : IsSolution 4 m c := by
    intro r
    norm_num [m, Finset.sum_range_succ]
    linarith [hrec r]
  have hbase : FormsPos forms (window 4 c 0) := by
    intro i
    fin_cases i <;> norm_num [forms, coordinate, window, hc0, hc1, hc2, hc3]
  have hstep : ∀ r x, FormsPos forms x → FormsPos forms (companionStep 4 m r x) := by
    intro r x hx i
    have h0 := hx (0 : Fin 4)
    have h1 := hx (1 : Fin 4)
    have h2 := hx (2 : Fin 4)
    have h3 := hx (3 : Fin 4)
    fin_cases i <;>
      norm_num [forms, coordinate, companionStep, m, Finset.sum_fin_eq_sum_range,
        Finset.sum_range_succ] at h0 h1 h2 h3 ⊢ <;>
      linarith
  have hinv := FormsPos.window_of_companionStep (m := m) (c := c) (forms := forms)
    hsol hbase hstep n
  have h := hinv (0 : Fin 4)
  simpa [forms, coordinate, window] using h

/-- The closed form `F(n+5) - n - 4` passes the order-four cone regression. -/
example (n : ℕ) : 0 < (Nat.fib (n + 5) : ℝ) - n - 4 := by
  apply pos_of_fib_sub_linear_rec (n := n)
  · intro r
    norm_num [Nat.fib_add_two]
    ring
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end RealRooted.ScalarRec
