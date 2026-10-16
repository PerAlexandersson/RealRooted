module

public import RealRooted.Basic

/-!
# Split polynomial sequences from parity factorizations

We package a common final step for polynomial sequences whose even and odd
subsequences factor through two already split families.
-/

public section

open Polynomial

namespace RealRooted

/-- A sequence is split when its even and odd rows have factorizations into powers of a
fixed split polynomial and split residual rows. -/
theorem splits_of_parity_factorization
    {P E O : ℕ → ℝ[X]} {a b c : ℝ[X]}
    (heven : ∀ k, P (2 * k) = a ^ k * E k)
    (hodd : ∀ k, P (2 * k + 1) = c * b ^ (k + 1) * O k)
    (ha : a.Splits) (hb : b.Splits) (hc : c.Splits)
    (hE : ∀ k, (E k).Splits) (hO : ∀ k, (O k).Splits) :
    ∀ n, (P n).Splits := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have h : n = 2 * (n / 2) := by lia
    rw [h, heven]
    exact (ha.pow _).mul (hE _)
  · have h : n = 2 * (n / 2) + 1 := by lia
    rw [h, hodd]
    exact (hc.mul (hb.pow _)).mul (hO _)

end RealRooted
