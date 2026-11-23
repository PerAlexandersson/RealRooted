/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.EulerGauss

/-!
# Paired Euler–Gauss families
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Two alternating Euler–Gauss families represent a formal Stieltjes fraction.
The numerator sequence is explicitly identified at every even and odd index. -/
theorem exists_stieltjesTail_of_paired {E O : ℕ → R⟦X⟧} {u v : ℕ → R}
    (hbase : E 0 - 1 = C (u 0) * X * O 0)
    (hodd : ∀ n, O n - E n = C (v n) * X * E (n + 1))
    (heven : ∀ n, E (n + 1) - O n = C (u (n + 1)) * X * O (n + 1)) :
    ∃ a : ℕ → R, (∀ n, a (2 * n) = u n ∧ a (2 * n + 1) = v n) ∧
      E 0 = stieltjesTail a 0 := by
  let a : ℕ → R := fun k => Sum.elim u v (Equiv.natSumNatEquivNat.symm k)
  let H : ℕ → R⟦X⟧ := fun k => Sum.elim E O (Equiv.natSumNatEquivNat.symm k)
  have haeven (n : ℕ) : a (2 * n) = u n := by
    rw [show 2 * n = Equiv.natSumNatEquivNat (Sum.inl n) by simp]
    simp only [a, Equiv.symm_apply_apply, Sum.elim_inl]
  have haodd (n : ℕ) : a (2 * n + 1) = v n := by
    rw [show 2 * n + 1 = Equiv.natSumNatEquivNat (Sum.inr n) by simp]
    simp only [a, Equiv.symm_apply_apply, Sum.elim_inr]
  have hHeven (n : ℕ) : H (2 * n) = E n := by
    rw [show 2 * n = Equiv.natSumNatEquivNat (Sum.inl n) by simp]
    simp only [H, Equiv.symm_apply_apply, Sum.elim_inl]
  have hHodd (n : ℕ) : H (2 * n + 1) = O n := by
    rw [show 2 * n + 1 = Equiv.natSumNatEquivNat (Sum.inr n) by simp]
    simp only [H, Equiv.symm_apply_apply, Sum.elim_inr]
  have ha0 : a 0 = u 0 := by simpa only [Nat.mul_zero] using haeven 0
  have hH0 : H 0 = E 0 := by simpa only [Nat.mul_zero] using hHeven 0
  have hH1 : H 1 = O 0 := by
    simpa only [Nat.mul_zero, Nat.zero_add] using hHodd 0
  let G : ℕ → R⟦X⟧
    | 0 => 1
    | k + 1 => H k
  have hrec (k : ℕ) : G (k + 1) - G k = C (a k) * X * G (k + 2) := by
    cases k with
    | zero => simpa only [G, hH0, hH1, ha0] using hbase
    | succ k =>
        obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
        · change H (2 * n + 1) - H (2 * n) = C (a (2 * n + 1)) * X * H (2 * n + 2)
          rw [show 2 * n + 2 = 2 * (n + 1) by ring, hHeven, hHodd, haodd, hHeven]
          exact hodd n
        · change H (2 * n + 2) - H (2 * n + 1) =
            C (a (2 * n + 2)) * X * H (2 * n + 3)
          rw [show 2 * n + 2 = 2 * (n + 1) by ring,
            show 2 * n + 3 = 2 * (n + 1) + 1 by ring, hHeven, hHodd, haeven, hHodd]
          exact heven n
  refine ⟨a, fun n => ⟨haeven n, haodd n⟩, ?_⟩
  simpa only [G, hH0] using eq_stieltjesTail_of_eulerGauss (a := a) (G := G) rfl hrec

end PowerSeries
