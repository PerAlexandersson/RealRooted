/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.Separable
import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential
import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Indicial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.SecondOrder
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic

/-!
# Exact multiplicities for generalized Laguerre polynomials

These results apply to all parameters over a characteristic-zero field, including
parameters outside the real-rooted range. Squarefreeness is proved after passing
to an algebraic closure, so it also excludes repeated nonreal roots.
Source: unpublished proof notes, RealRooted issue #2341, Corollary 4.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- Zero is a root exactly at the negative integers from `-1` through `-n`. -/
theorem isRoot_zero_generalizedLaguerre_iff (n : ℕ) (α : K) :
    (generalizedLaguerre n α).IsRoot 0 ↔
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ α = -(m : K) := by
  rw [IsRoot.def, generalizedLaguerre_eval_zero, ascPochhammer_eval_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, hα⟩
    refine ⟨k + 1, by lia, by lia, ?_⟩
    push_cast
    linear_combination hα
  · rintro ⟨m, hm, hmn, rfl⟩
    refine ⟨m - 1, by lia, ?_⟩
    rw [Nat.cast_sub hm]
    ring

variable [CharZero K]

/-- At a zero root the Laguerre equation determines the parameter from the multiplicity. -/
theorem rootMultiplicity_zero_add_generalizedLaguerre
    (n : ℕ) (α : K) (hr : (generalizedLaguerre n α).IsRoot 0) :
    ((generalizedLaguerre n α).rootMultiplicity 0 : K) + α = 0 := by
  have hode := generalizedLaguerre_ode n α
  have h := rootMultiplicity_sub_one_mul_eval_derivative_add_eq_zero
    (monic_generalizedLaguerre n α).ne_zero
    (A := X) (B := C (α + 1) + X) (C₀ := -C (n : K))
    (by simpa [laguerreDifferentialOperator, sub_eq_add_neg] using sub_eq_zero.mpr hode)
    (by simp) hr
  simpa using h

/-- Exact multiplicity at zero, throughout the full parameter range. -/
theorem rootMultiplicity_zero_generalizedLaguerre_eq_iff
    (n m : ℕ) (α : K) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (generalizedLaguerre n α).rootMultiplicity 0 = m ↔ α = -(m : K) := by
  constructor
  · intro h
    have hr := (rootMultiplicity_pos (monic_generalizedLaguerre n α).ne_zero).mp
      (by rw [h]; lia)
    have := rootMultiplicity_zero_add_generalizedLaguerre n α hr
    rw [h] at this
    exact eq_neg_of_add_eq_zero_right this
  · intro h
    have hr := (isRoot_zero_generalizedLaguerre_iff n α).mpr ⟨m, hm, hmn, h⟩
    have heq := rootMultiplicity_zero_add_generalizedLaguerre n α hr
    exact Nat.cast_injective (R := K) (by linear_combination heq - h)

omit [CharZero K] in
/-- Outside the negative integer endpoint parameters, the multiplicity at zero is zero. -/
theorem rootMultiplicity_zero_generalizedLaguerre_eq_zero_iff (n : ℕ) (α : K) :
    (generalizedLaguerre n α).rootMultiplicity 0 = 0 ↔
      ∀ m : ℕ, 1 ≤ m → m ≤ n → α ≠ -(m : K) := by
  rw [rootMultiplicity_eq_zero_iff]
  have hne := (monic_generalizedLaguerre n α).ne_zero
  simp only [isRoot_zero_generalizedLaguerre_iff, hne, imp_false]
  push Not
  rfl

/-- Every nonzero root is simple, over any characteristic-zero field. -/
theorem rootMultiplicity_generalizedLaguerre_le_one
    (n : ℕ) (α r : K) (hr : r ≠ 0) :
    (generalizedLaguerre n α).rootMultiplicity r ≤ 1 := by
  by_cases hroot : (generalizedLaguerre n α).IsRoot r
  · have hder := eval_derivative_ne_zero_of_second_order_ode
      (monic_generalizedLaguerre n α).ne_zero
      (A := X) (B := C (α + 1) + X) (C₀ := -C (n : K))
      (by simpa [laguerreDifferentialOperator, sub_eq_add_neg] using
        sub_eq_zero.mpr (generalizedLaguerre_ode n α)) hroot (by simpa using hr)
    have h := one_lt_rootMultiplicity_iff_isRoot
      (monic_generalizedLaguerre n α).ne_zero (t := r)
    by_contra hmult
    exact hder ((h.mp (by lia)).2)
  · simp [rootMultiplicity_eq_zero hroot]

/-- Laguerre polynomials are separable exactly when their parameter avoids
`-2, …, -n`. This statement concerns all algebraic roots. -/
theorem separable_generalizedLaguerre_iff (n : ℕ) (α : K) :
    (generalizedLaguerre n α).Separable ↔
      ∀ m : ℕ, 2 ≤ m → m ≤ n → α ≠ -(m : K) := by
  classical
  constructor
  · intro h m hm hmn hα
    have hmult := rootMultiplicity_le_one_of_separable h (0 : K)
    rw [(rootMultiplicity_zero_generalizedLaguerre_eq_iff n m α (by lia) hmn).mpr hα]
      at hmult
    lia
  · intro hα
    let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    rw [← separable_map f, map_generalizedLaguerre]
    apply (nodup_roots_iff_of_splits (monic_generalizedLaguerre n (f α)).ne_zero
      (IsAlgClosed.splits _)).mp
    apply Multiset.nodup_iff_count_le_one.mpr
    intro r
    rw [count_roots]
    by_cases hr : r = 0
    · subst r
      by_contra hm
      let m := (generalizedLaguerre n (f α)).rootMultiplicity 0
      have hm2 : 2 ≤ m := by dsimp [m]; lia
      have hmn : m ≤ n := by
        simpa [m] using (natDegree_le_of_dvd
          (pow_rootMultiplicity_dvd (generalizedLaguerre n (f α)) 0)
          (monic_generalizedLaguerre n (f α)).ne_zero)
      have hroot := (rootMultiplicity_pos (monic_generalizedLaguerre n (f α)).ne_zero).mp
        (show 0 < m by lia)
      have heq := rootMultiplicity_zero_add_generalizedLaguerre n (f α) hroot
      have hf : f α = f (-(m : K)) := by
        simp only [map_neg, map_natCast]
        change f α = -(m : AlgebraicClosure K)
        linear_combination heq
      exact hα m hm2 hmn (f.injective hf)
    · exact rootMultiplicity_generalizedLaguerre_le_one n (f α) r hr

/-- Squarefreeness at arbitrary parameters, including nonreal roots. -/
theorem squarefree_generalizedLaguerre_iff (n : ℕ) (α : K) :
    Squarefree (generalizedLaguerre n α) ↔
      ∀ m : ℕ, 2 ≤ m → m ≤ n → α ≠ -(m : K) := by
  rw [← PerfectField.separable_iff_squarefree, separable_generalizedLaguerre_iff]

end Polynomial
