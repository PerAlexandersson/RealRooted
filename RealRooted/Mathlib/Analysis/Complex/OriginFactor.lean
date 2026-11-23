/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.MulPow
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Separation.Regular

/-!
# Reality and Taylor signs after removing monomial factors

Conjugation symmetry descends through a power of a real linear factor
by cancellation off its center and continuity at the center. Removing
a power at zero preserves nonnegative real Taylor derivatives, since
the shifted derivative differs by a positive binomial-factorial factor.
-/

public section

open scoped ComplexConjugate

namespace Complex

/-- Conjugation symmetry descends through a real monomial factor. -/
theorem conj_of_real_pow_mul {f g : ℂ → ℂ} {r : ℝ} {m : ℕ}
    (hg : Continuous g) (hf : ∀ z, f (conj z) = conj (f z))
    (hfactor : ∀ z, f z = (z - r) ^ m * g z) :
    ∀ z, g (conj z) = conj (g z) := by
  have heq : (fun z ↦ g (conj z)) = fun z ↦ conj (g z) := by
    apply Continuous.ext_on (dense_compl_singleton (r : ℂ))
      (hg.comp continuous_conj) (continuous_conj.comp hg)
    intro z hz
    have hzr : z ≠ (r : ℂ) := by simpa using hz
    have hconjne : conj z - (r : ℂ) ≠ 0 := by
      intro hzero
      have h := congrArg conj (sub_eq_zero.mp hzero)
      exact hzr (by simpa using h)
    have h := hf z
    rw [hfactor, hfactor] at h
    simp only [map_mul, map_pow, map_sub, conj_ofReal] at h
    exact mul_left_cancel₀ (pow_ne_zero _ hconjne) h
  exact fun z ↦ congrFun heq z

/-- Dividing an entire function by an origin monomial preserves
nonnegativity of its real Taylor derivatives. -/
theorem re_iteratedDeriv_nonneg_of_pow_mul {f g : ℂ → ℂ} {m : ℕ}
    (hg : Differentiable ℂ g) (hfactor : ∀ z : ℂ, f z = z ^ m * g z)
    (hpos : ∀ n : ℕ, 0 ≤ (iteratedDeriv n f 0).re) (n : ℕ) :
    0 ≤ (iteratedDeriv n g 0).re := by
  have heq : f = fun z : ℂ ↦ z ^ m * g z := funext hfactor
  have hcoeff : (iteratedDeriv (m + n) f 0).re =
      ((m + n).choose m : ℝ) * (m.factorial : ℝ) * (iteratedDeriv n g 0).re := by
    rw [heq, iteratedDeriv_pow_mul_zero hg.contDiff.contDiffAt]
    simp only [Nat.add_sub_cancel_left, mul_re, mul_im, natCast_re, natCast_im,
      zero_mul, mul_zero, zero_add, sub_zero]
  have hc : 0 < ((m + n).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right m n)
  have h := hpos (m + n)
  rw [hcoeff] at h
  exact nonneg_of_mul_nonneg_right h (mul_pos hc (by positivity))

end Complex
