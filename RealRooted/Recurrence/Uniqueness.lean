import Mathlib.Tactic

/-!
# Uniqueness for finite-order recurrences

The update receives the preceding `k` rows in increasing-lag order.  Since the
row type is arbitrary, the statement covers polynomial recurrences with any
mixture of derivatives as well as pure-lag recurrences.
-/

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

end RealRooted
