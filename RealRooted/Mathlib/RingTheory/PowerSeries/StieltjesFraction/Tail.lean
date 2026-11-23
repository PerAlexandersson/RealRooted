/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Convergents

/-!
# Infinite formal Stieltjes fractions

Each coefficient is defined by a sufficiently deep finite convergent. The
stabilization theorem proves that this is independent of every subsequent
coefficient and yields the infinite tail equation. Thus these objects denote
formal series, with no numerical convergence requirement.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The formal Stieltjes fraction starting at numerator index `s`. Its constant
term is one; a separate outer scalar supplies the total mass. -/
@[expose] noncomputable def stieltjesTail (a : ℕ → R) (s : ℕ) : R⟦X⟧ :=
  mk fun n ↦ coeff n (stieltjesConvergent a (n + 1) s)

/-- Each coefficient is the coefficient of a finite convergent deep enough
to stabilize it. -/
theorem coeff_stieltjesTail (a : ℕ → R) (s n : ℕ) :
    coeff n (stieltjesTail a s) = coeff n (stieltjesConvergent a (n + 1) s) := by
  simp only [stieltjesTail, coeff_mk]

/-- The formal tail has constant coefficient one. -/
@[simp] theorem constantCoeff_stieltjesTail (a : ℕ → R) (s : ℕ) :
    constantCoeff (stieltjesTail a s) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_stieltjesTail,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_stieltjesConvergent]

/-- A depth-`n` convergent agrees with the full formal tail below degree `n`. -/
theorem X_pow_dvd_stieltjesTail_sub_convergent (a : ℕ → R) (n s : ℕ) :
    X ^ n ∣ stieltjesTail a s - stieltjesConvergent a n s := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  rw [map_sub, coeff_stieltjesTail]
  apply sub_eq_zero.mpr
  exact (coeff_stieltjesConvergent_eq a (by lia : k + 1 ≤ n)
    (Nat.lt_succ_self k) s).symm

/-- The infinite formal Stieltjes fraction satisfies its tail equation. -/
theorem stieltjesTail_eq_step (a : ℕ → R) (s : ℕ) :
    stieltjesTail a s = stieltjesStep (a s) (stieltjesTail a (s + 1)) := by
  ext k
  rw [coeff_stieltjesTail]
  have h := X_pow_dvd_iff.mp (X_pow_dvd_stieltjesStep_sub (a s)
    (X_pow_dvd_stieltjesTail_sub_convergent a k (s + 1))) k (Nat.lt_succ_self k)
  exact (sub_eq_zero.mp (by simpa only [map_sub, stieltjesConvergent] using h)).symm

/-- The constructed tails are the unique family satisfying the formal
Stieltjes equations. -/
theorem eq_stieltjesTail_of_step_eq {a : ℕ → R} {F : ℕ → R⟦X⟧}
    (hF : ∀ s, F s = stieltjesStep (a s) (F (s + 1))) : F = stieltjesTail a :=
  eq_of_stieltjesStep_eq hF (stieltjesTail_eq_step a)

/-- A zero numerator terminates the entire formal fraction at that position. -/
theorem stieltjesTail_eq_convergent_of_zero (a : ℕ → R) (n s : ℕ)
    (h : a (s + n) = 0) : stieltjesTail a s = stieltjesConvergent a n s := by
  ext k
  rw [coeff_stieltjesTail]
  calc
    coeff k (stieltjesConvergent a (k + 1) s) =
        coeff k (stieltjesConvergent a (n + (k + 1)) s) :=
      (coeff_stieltjesConvergent_eq a (by lia : k + 1 ≤ n + (k + 1))
        (Nat.lt_succ_self k) s).symm
    _ = coeff k (stieltjesConvergent a n s) :=
      congrArg (coeff k) (stieltjesConvergent_eq_of_zero a n (k + 1) s h)

/-- In particular, a zero first numerator gives the constant formal series one. -/
theorem stieltjesTail_eq_one_of_zero {a : ℕ → R} {s : ℕ} (h : a s = 0) :
    stieltjesTail a s = 1 := by
  rw [stieltjesTail_eq_step, h, stieltjesStep_zero]

/-- A formal coefficient depends only on a finite prefix of numerator data. -/
theorem coeff_stieltjesTail_eq_of_prefix {a b : ℕ → R} (s t n : ℕ)
    (h : ∀ i < n + 1, a (s + i) = b (t + i)) :
    coeff n (stieltjesTail a s) = coeff n (stieltjesTail b t) := by
  rw [coeff_stieltjesTail, coeff_stieltjesTail,
    stieltjesConvergent_eq_of_prefix (n + 1) s t h]

end PowerSeries
