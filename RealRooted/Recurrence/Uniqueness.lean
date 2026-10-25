module

public import Mathlib.Tactic

/-!
# Uniqueness for finite-order recurrences

The update receives the preceding `k` rows in increasing-lag order.  Since the
row type is arbitrary, the statement covers polynomial recurrences with any
mixture of derivatives as well as pure-lag recurrences.
-/

@[expose] public section

namespace RealRooted

/-- A sequence satisfies an order-`k` recurrence with the specified window
update. -/
def SatisfiesFiniteRecurrence {α : Sort*} (k : ℕ)
    (op : ℕ → (Fin k → α) → α) (P : ℕ → α) : Prop :=
  ∀ n : ℕ, P (n + k) = op n (fun i => P (n + i))

/-- Two solutions of the same finite-order recurrence that agree on the
initial window agree everywhere. -/
theorem sequence_eq_of_same_finite_recurrence
    {α : Sort*} {k : ℕ} {op : ℕ → (Fin k → α) → α}
    {P Q : ℕ → α}
    (hinit : ∀ i < k, P i = Q i)
    (hP : SatisfiesFiniteRecurrence k op P)
    (hQ : SatisfiesFiniteRecurrence k op Q) :
    ∀ n : ℕ, P n = Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < k
      · exact hinit n hn
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by lia⟩
        rw [hP m, hQ m]
        congr 1
        funext i
        exact ih (m + i) (by have := i.isLt; lia)

/-- Two sequences with the same initial value and lag-one recurrence agree. -/
theorem sequence_eq_of_same_lag_one_recurrence
    {α : Sort*} {P Q : Nat → α} (update : Nat → α → α)
    (hzero : P 0 = Q 0)
    (hP : ∀ n : Nat, P (n + 1) = update n (P n))
    (hQ : ∀ n : Nat, Q (n + 1) = update n (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      rw [hP n, hQ n, ih]

/-- Two sequences with the same first two values and lag-two recurrence agree. -/
theorem sequence_eq_of_same_lag_two_recurrence
    {α : Sort*} {P Q : Nat → α} (update : Nat → α → α → α)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (hP : ∀ n : Nat, P (n + 2) = update n (P (n + 1)) (P n))
    (hQ : ∀ n : Nat, Q (n + 2) = update n (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact hzero
  | one => exact hone
  | more n ih ih_succ =>
      rw [hP n, hQ n, ih_succ, ih]

/-- Two sequences with the same first three values and lag-three recurrence agree. -/
theorem sequence_eq_of_same_lag_three_recurrence
    {α : Sort*} {P Q : Nat → α} (update : Nat → α → α → α → α)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (htwo : P 2 = Q 2)
    (hP : ∀ n : Nat,
      P (n + 3) = update n (P (n + 2)) (P (n + 1)) (P n))
    (hQ : ∀ n : Nat,
      Q (n + 3) = update n (Q (n + 2)) (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · exact hzero
      · exact hone
      · exact htwo
      · rw [hP n, hQ n, ih (n + 2) (by lia), ih (n + 1) (by lia),
          ih n (by lia)]

/-- Two sequences with the same first four values and lag-four recurrence agree. -/
theorem sequence_eq_of_same_lag_four_recurrence
    {α : Sort*} {P Q : Nat → α}
    (update : Nat → α → α → α → α → α)
    (hzero : P 0 = Q 0)
    (hone : P 1 = Q 1)
    (htwo : P 2 = Q 2)
    (hthree : P 3 = Q 3)
    (hP : ∀ n : Nat,
      P (n + 4) = update n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    (hQ : ∀ n : Nat,
      Q (n + 4) = update n (Q (n + 3)) (Q (n + 2)) (Q (n + 1)) (Q n)) :
    ∀ n : Nat, P n = Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · exact hzero
      · exact hone
      · exact htwo
      · exact hthree
      · rw [hP n, hQ n, ih (n + 3) (by lia), ih (n + 2) (by lia),
          ih (n + 1) (by lia), ih n (by lia)]

end RealRooted
