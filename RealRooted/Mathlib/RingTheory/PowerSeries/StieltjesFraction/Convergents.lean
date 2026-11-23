/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Step

/-!
# Finite formal Stieltjes fractions

Depth `n` uses the first `n` numerator coefficients starting at an offset `s`.
Further depth changes no coefficient below degree `n`. A zero numerator
terminates the effective fraction regardless of all subsequent coefficients.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A finite Stieltjes continued fraction with bottom tail one. The numerator
`a 0` corresponds to the coefficient called `α₁` in the classical notation. -/
@[expose] noncomputable def stieltjesConvergent (a : ℕ → R) : ℕ → ℕ → R⟦X⟧
  | 0, _ => 1
  | n + 1, s => stieltjesStep (a s) (stieltjesConvergent a n (s + 1))

/-- Every finite formal Stieltjes fraction is normalized at the constant term. -/
@[simp] theorem constantCoeff_stieltjesConvergent (a : ℕ → R) (n s : ℕ) :
    constantCoeff (stieltjesConvergent a n s) = 1 := by
  cases n <;> simp [stieltjesConvergent]

/-- Extra depth changes the finite fraction by a multiple of `X^n`. -/
theorem X_pow_dvd_stieltjesConvergent_sub (a : ℕ → R) (n k s : ℕ) :
    X ^ n ∣ stieltjesConvergent a (n + k) s - stieltjesConvergent a n s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      simpa only [Nat.succ_add, stieltjesConvergent] using
        X_pow_dvd_stieltjesStep_sub (a s) (ih (s + 1))

/-- Formal coefficients stabilize once the convergent depth exceeds the degree. -/
theorem coeff_stieltjesConvergent_eq (a : ℕ → R) {n m k : ℕ}
    (hnm : n ≤ m) (hk : k < n) (s : ℕ) :
    coeff k (stieltjesConvergent a m s) = coeff k (stieltjesConvergent a n s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have h := X_pow_dvd_iff.mp (X_pow_dvd_stieltjesConvergent_sub a n d s) k hk
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

/-- Only the first `n` numerator coefficients affect a depth-`n` convergent. -/
theorem stieltjesConvergent_eq_of_prefix {a b : ℕ → R} (n s t : ℕ)
    (h : ∀ i < n, a (s + i) = b (t + i)) :
    stieltjesConvergent a n s = stieltjesConvergent b n t := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
      have h0 : a s = b t := by simpa only [Nat.add_zero] using h 0 (by lia)
      have htail : ∀ i < n, a (s + 1 + i) = b (t + 1 + i) := by
        intro i hi
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by lia)
      rw [stieltjesConvergent, stieltjesConvergent, h0, ih (s + 1) (t + 1) htail]

/-- A zero active numerator makes every deeper convergent equal to the one
ending immediately before it. Later coefficients may have arbitrary signs. -/
theorem stieltjesConvergent_eq_of_zero (a : ℕ → R) (n k s : ℕ)
    (h : a (s + n) = 0) :
    stieltjesConvergent a (n + k) s = stieltjesConvergent a n s := by
  induction n generalizing s with
  | zero =>
      have hs : a s = 0 := by simpa only [Nat.add_zero] using h
      cases k <;> simp [stieltjesConvergent, hs]
  | succ n ih =>
      have ht : a (s + 1 + n) = 0 := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 n] using h
      simpa only [Nat.succ_add, stieltjesConvergent] using
        congrArg (stieltjesStep (a s)) (ih (s + 1) ht)

end PowerSeries
