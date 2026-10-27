/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ordered-ring lemmas

`biaffine_mul_nonneg_iff` is a sign-rigidity result for biaffine forms with
nonnegative coefficients (RealRooted issue #1897). The proof was found by
Aristotle (Harmonic).
-/

public section

private lemma affine_mul_nonneg_det (a b c d : ℝ)
    (h : ∀ y : ℝ, 0 ≤ (a + b * y) * (c + d * y)) :
    a * d = b * c := by
  have hd := discrim_le_zero (a := b * d) (b := a * d + b * c) (c := a * c) (fun y => by
    have hy := h y
    nlinarith)
  unfold discrim at hd
  nlinarith [sq_nonneg (a * d - b * c)]

/-- If two nonzero biaffine forms have nonnegative coefficients, their product is
nonnegative on `ℝ²` exactly when they are positive scalar multiples of one another. -/
theorem biaffine_mul_nonneg_iff (g h : Fin 4 → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hh : ∀ k, 0 ≤ h k) (hg0 : g ≠ 0) (hh0 : h ≠ 0) :
    (∀ y v : ℝ, 0 ≤ (g 0 + g 1 * y + g 2 * v + g 3 * y * v) *
        (h 0 + h 1 * y + h 2 * v + h 3 * y * v)) ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ k, g k = ρ * h k := by
  constructor
  · intro hprod
    have e1 : ∀ v : ℝ,
        (g 0 + g 2 * v) * (h 1 + h 3 * v) =
          (g 1 + g 3 * v) * (h 0 + h 2 * v) :=
      fun v => affine_mul_nonneg_det _ _ _ _ (fun y => by
        have hy := hprod y v
        ring_nf at hy ⊢
        linarith)
    have e2 : ∀ y : ℝ,
        (g 0 + g 1 * y) * (h 2 + h 3 * y) =
          (g 2 + g 3 * y) * (h 0 + h 1 * y) :=
      fun y => affine_mul_nonneg_det _ _ _ _ (fun v => by
        have hv := hprod y v
        ring_nf at hv ⊢
        linarith)
    have a0 := e1 0
    have a1 := e1 1
    have a2 := e1 (-1)
    have b0 := e2 0
    have b1 := e2 1
    have b2 := e2 (-1)
    ring_nf at a0 a1 a2 b0 b1 b2
    have hminor : ∀ i j, g i * h j = g j * h i := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;> linarith
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hh0
    have hkpos : 0 < h k := lt_of_le_of_ne (hh k) (Ne.symm hk)
    have hgk : 0 < g k := by
      rcases lt_or_eq_of_le (hg k) with hgk | hgk
      · exact hgk
      · exfalso
        apply hg0
        funext i
        have hki := hminor i k
        rw [← hgk, zero_mul] at hki
        simpa [hkpos.ne'] using hki
    refine ⟨g k / h k, div_pos hgk hkpos, fun i => ?_⟩
    field_simp
    linarith [hminor i k]
  · rintro ⟨ρ, hρ, hk⟩ y v
    simp only [hk]
    have heq :
        (ρ * h 0 + ρ * h 1 * y + ρ * h 2 * v + ρ * h 3 * y * v) *
            (h 0 + h 1 * y + h 2 * v + h 3 * y * v) =
          ρ * (h 0 + h 1 * y + h 2 * v + h 3 * y * v) ^ 2 := by
      ring
    rw [heq]
    positivity
