import RealRooted.Interlacing.Euclid

/-!
# Parity products of two three-term sequences

Let `s` and `t` solve the same recurrence `x (m + 2) = β x (m + 1) - μ ^ 2 x m`.  The sequence
alternating between `s m * t m` and `s (m + 1) * t m` satisfies the order-three recurrence with
characteristic polynomial `(z - μ) (z ^ 2 - β z + μ ^ 2)`, provided one compatibility condition
holds at the start (`eq_parityProduct_of_rec3`): the Casoratians
`W m = s (m + 1) t m - s m t (m + 1)` and `V m = s (m + 1) t (m + 1) - s (m + 2) t m` both grow by
the factor `μ ^ 2`, so `V 0 = μ W 0` gives `V m = μ W m` for all `m`, which is what the
recurrence needs.

Consecutive rows of a parity product share a factor, so interlacing and splitting come from
those of `s` and `t` (`interlaces_of_parityProduct`, `splits_of_parityProduct`).  Examples
are the OEIS rows A158909, A143858 and A092879, whose order-three recurrences have no
three-term reduction.
-/

open Polynomial

namespace RealRooted

variable {P s t : ℕ → ℝ[X]} {β μ : ℝ[X]}

/-- The Casoratian relation `V m = μ W m` of two solutions of
`x (m + 2) = β x (m + 1) - μ ^ 2 x m`, from its first instance. -/
theorem parityProduct_casoratian
    (hs : ∀ m, s (m + 2) = β * s (m + 1) - μ ^ 2 * s m)
    (ht : ∀ m, t (m + 2) = β * t (m + 1) - μ ^ 2 * t m)
    (hc : s 1 * t 1 - s 2 * t 0 = μ * (s 1 * t 0 - s 0 * t 1)) (m : ℕ) :
    s (m + 1) * t (m + 1) - s (m + 2) * t m = μ * (s (m + 1) * t m - s m * t (m + 1)) := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    change s (m + 2) * t (m + 2) - s (m + 3) * t (m + 1) =
      μ * (s (m + 2) * t (m + 1) - s (m + 1) * t (m + 2))
    have e1 : s (m + 3) = β * s (m + 2) - μ ^ 2 * s (m + 1) := hs (m + 1)
    rw [e1, ht m]
    rw [hs m] at ih ⊢
    linear_combination μ ^ 2 * ih

/-- Rows given by an order-three recurrence with characteristic polynomial
`(z - μ) (z ^ 2 - β z + μ ^ 2)` are the parity products of two solutions `s`, `t` of
`x (m + 2) = β x (m + 1) - μ ^ 2 x m`, given the first three rows and the compatibility
`V 0 = μ W 0` of the Casoratians. -/
theorem eq_parityProduct_of_rec3
    (hP : ∀ n, P (n + 3) =
      (β + μ) * P (n + 2) - (μ ^ 2 + μ * β) * P (n + 1) + μ ^ 3 * P n)
    (hs : ∀ m, s (m + 2) = β * s (m + 1) - μ ^ 2 * s m)
    (ht : ∀ m, t (m + 2) = β * t (m + 1) - μ ^ 2 * t m)
    (h0 : P 0 = s 0 * t 0) (h1 : P 1 = s 1 * t 0) (h2 : P 2 = s 1 * t 1)
    (hc : s 1 * t 1 - s 2 * t 0 = μ * (s 1 * t 0 - s 0 * t 1)) :
    ∀ m, P (2 * m) = s m * t m ∧ P (2 * m + 1) = s (m + 1) * t m := by
  have hE := parityProduct_casoratian hs ht hc
  have key : ∀ m, P (2 * m) = s m * t m ∧ P (2 * m + 1) = s (m + 1) * t m ∧
      P (2 * m + 2) = s (m + 1) * t (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using h0, by simpa using h1, by simpa using h2⟩
    | succ m ih =>
      obtain ⟨e0, e1, e2⟩ := ih
      have hm := hE m
      rw [hs m] at hm
      have e3 : P (2 * m + 3) = s (m + 2) * t (m + 1) := by
        rw [hP (2 * m), e2, e1, e0, hs m]
        linear_combination μ * hm
      change P (2 * m + 2) = s (m + 1) * t (m + 1) ∧ P (2 * m + 3) = s (m + 2) * t (m + 1) ∧
        P (2 * m + 4) = s (m + 2) * t (m + 2)
      refine ⟨e2, e3, ?_⟩
      have h4 : P (2 * m + 4) = (β + μ) * P (2 * m + 3) - (μ ^ 2 + μ * β) * P (2 * m + 2) +
          μ ^ 3 * P (2 * m + 1) := hP (2 * m + 1)
      rw [h4, e3, e2, e1, ht m, hs m]
      linear_combination (-μ ^ 2) * hm
  exact fun m => ⟨(key m).1, (key m).2.1⟩

/-- Consecutive parity products interlace when consecutive rows of `s` and of `t` do. -/
theorem interlaces_of_parityProduct
    (hPst : ∀ m, P (2 * m) = s m * t m ∧ P (2 * m + 1) = s (m + 1) * t m)
    (hs : ∀ m, Interlaces (s m) (s (m + 1))) (ht : ∀ m, Interlaces (t m) (t (m + 1)))
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [(hPst m).1, (hPst m).2, mul_comm (s m), mul_comm (s (m + 1))]
    exact (hs m).mul_both_of_splits (ht m).2.1.2 (ht m).2.1.1
  · rw [(hPst m).2, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, (hPst (m + 1)).1]
    exact (ht m).mul_both_of_splits (hs m).1.2 (hs m).1.1

/-- Parity products split when the rows of `s` and `t` do. -/
theorem splits_of_parityProduct
    (hPst : ∀ m, P (2 * m) = s m * t m ∧ P (2 * m + 1) = s (m + 1) * t m)
    (hs : ∀ m, (s m).Splits) (ht : ∀ m, (t m).Splits) (n : ℕ) : (P n).Splits := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [(hPst m).1]
    exact (hs m).mul (ht m)
  · rw [(hPst m).2]
    exact (hs (m + 1)).mul (ht m)

end RealRooted
