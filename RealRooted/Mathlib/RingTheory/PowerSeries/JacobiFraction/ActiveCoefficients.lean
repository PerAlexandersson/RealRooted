/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Coefficients

import Mathlib.Tactic.TypeStar

/-!
# Jacobi coefficients on the active prefix

Equal formal Jacobi fractions determine both coefficient sequences only as far
as the first zero outgoing numerator. Later diagonals and numerators need not
agree. This is the precise coefficient comparison required in a terminating
version of Sokal's proof of Wall's criterion, arXiv:1903.12455v2, equation (11).
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]
variable {b c b' c' : ℕ → R} {F G : ℕ → R⟦X⟧}

/-- Equal normalized Jacobi tails recover their current diagonal and numerator. -/
theorem jacobiCoefficients_eq_of_tail_eq
    (hF : ∀ n, F n = jacobiStep (b n) (c n) (F (n + 1)))
    (hG : ∀ n, G n = jacobiStep (b' n) (c' n) (G (n + 1)))
    {n : ℕ} (h : F n = G n) : b n = b' n ∧ c n = c' n := by
  have hFn : constantCoeff (F (n + 1)) = 1 := by rw [hF]; simp
  have hGn : constantCoeff (G (n + 1)) = 1 := by rw [hG]; simp
  have hb : b n = b' n := by
    have h1 := congrArg (coeff 1) h
    simpa only [hF n, hG n, coeff_one_jacobiStep] using h1
  refine ⟨hb, ?_⟩
  have h2 := congrArg (coeff 2) h
  simp only [hF n, hG n, coeff_two_jacobiStep, hFn, hGn, mul_one, hb] at h2
  exact add_left_cancel h2

variable [IsDomain R]

/-- A nonzero outgoing numerator lets equality of Jacobi tails pass to the next level. -/
theorem jacobiTail_succ_eq_of_ne_zero
    (hF : ∀ n, F n = jacobiStep (b n) (c n) (F (n + 1)))
    (hG : ∀ n, G n = jacobiStep (b' n) (c' n) (G (n + 1)))
    {n : ℕ} (h : F n = G n) (hc : c n ≠ 0) : F (n + 1) = G (n + 1) := by
  obtain ⟨hb, hc'⟩ := jacobiCoefficients_eq_of_tail_eq hF hG h
  apply jacobiStep_injective (b n) hc
  calc
    jacobiStep (b n) (c n) (F (n + 1)) = F n := (hF n).symm
    _ = G n := h
    _ = jacobiStep (b n) (c n) (G (n + 1)) := by rw [hG n, hb, hc']

/-- Equality propagates to any level preceded only by nonzero outgoing numerators. -/
theorem jacobiTail_eq_of_prefix_ne_zero
    (hF : ∀ n, F n = jacobiStep (b n) (c n) (F (n + 1)))
    (hG : ∀ n, G n = jacobiStep (b' n) (c' n) (G (n + 1)))
    (h : F 0 = G 0) (n : ℕ) (hc : ∀ k < n, c k ≠ 0) : F n = G n := by
  revert hc
  induction n with
  | zero => intro _; exact h
  | succ n ih =>
      intro hc
      have hn := ih (fun k hk => hc k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      exact jacobiTail_succ_eq_of_ne_zero hF hG hn (hc n (Nat.lt_succ_self n))

/-- Both Jacobi coefficients are determined through the first zero outgoing
numerator, including that numerator and its diagonal. -/
theorem jacobiCoefficients_eq_of_prefix_ne_zero
    (hF : ∀ n, F n = jacobiStep (b n) (c n) (F (n + 1)))
    (hG : ∀ n, G n = jacobiStep (b' n) (c' n) (G (n + 1)))
    (h : F 0 = G 0) (n : ℕ) (hc : ∀ k < n, c k ≠ 0) :
    b n = b' n ∧ c n = c' n :=
  jacobiCoefficients_eq_of_tail_eq hF hG (jacobiTail_eq_of_prefix_ne_zero hF hG h n hc)

end PowerSeries
