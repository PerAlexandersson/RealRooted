/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.Mathlib.Analysis.CompletelyMonotone.ReciprocalHierarchy
public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Logarithmic derivatives after inserting an origin zero

Multiplication by `z^r` adds `r/x` to the real logarithmic derivative
on the positive axis. The signed derivative and two-index Rodrigues
formulas record this contribution with its exact factorial and domain.
-/

public section

open Filter Topology
open scoped ContDiff

namespace Complex

/-- A power at the origin contributes its multiplicity divided by the
positive argument to the real logarithmic derivative. -/
theorem re_logDeriv_pow_mul {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (r : ℕ) {x : ℝ} (hx : x ≠ 0) (hgz : g (x : ℂ) ≠ 0) :
    (logDeriv (fun z : ℂ ↦ z ^ r * g z) (x : ℂ)).re =
      (r : ℝ) / x + (logDeriv g (x : ℂ)).re := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hp : DifferentiableAt ℂ (fun z : ℂ ↦ z ^ r) (x : ℂ) :=
    differentiableAt_id.pow r
  rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z ^ r) (g := g) (x : ℂ)
    (pow_ne_zero r hxc) hgz hp (hg _), logDeriv_pow, add_re]
  simp only [div_ofReal_re, natCast_re]

/-- Ordinary real logarithmic derivatives after inserting an origin zero
have the expected factorial reciprocal correction. -/
theorem signed_iteratedDeriv_re_logDeriv_pow_mul {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hn : ∀ x : ℝ, 0 < x → g (x : ℂ) ≠ 0)
    (hL : ContDiffOn ℝ ∞ (fun y : ℝ ↦ (logDeriv g (y : ℂ)).re) (Set.Ioi 0))
    (r m : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ m * iteratedDeriv m
      (fun y : ℝ ↦ (logDeriv (fun z : ℂ ↦ z ^ r * g z) (y : ℂ)).re) x =
      (r : ℝ) * (m.factorial : ℝ) / x ^ (m + 1) +
        (-1 : ℝ) ^ m * iteratedDeriv m (fun y : ℝ ↦ (logDeriv g (y : ℂ)).re) x := by
  have heq : (fun y : ℝ ↦ (logDeriv (fun z : ℂ ↦ z ^ r * g z) (y : ℂ)).re)
      =ᶠ[𝓝 x] (fun y : ℝ ↦ (r : ℝ) / y + (logDeriv g (y : ℂ)).re) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact re_logDeriv_pow_mul hg r hy.ne' (hn y hy)
  rw [heq.iteratedDeriv_eq m]
  exact Real.signed_iteratedDeriv_const_div_add hL r m hx

/-- Inserting a zero at the origin changes only row zero of the signed
Rodrigues hierarchy whenever the original logarithmic derivative is CM. -/
theorem weighted_iteratedDeriv_re_logDeriv_pow_mul {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hn : ∀ x : ℝ, 0 < x → g (x : ℂ) ≠ 0)
    (hL : TauCeti.IsCompletelyMonotoneOnIoi (fun y : ℝ ↦ (logDeriv g (y : ℂ)).re))
    (r m k : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
      iteratedDeriv m (fun v : ℝ ↦
        (logDeriv (fun z : ℂ ↦ z ^ r * g z) (v : ℂ)).re) y) x =
      (if k = 0 then (r : ℝ) * (m.factorial : ℝ) / x ^ (m + 1) else 0) +
        (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
          iteratedDeriv m (fun v : ℝ ↦ (logDeriv g (v : ℂ)).re) y) x := by
  have heq : (fun y : ℝ ↦ (logDeriv (fun z : ℂ ↦ z ^ r * g z) (y : ℂ)).re)
      =ᶠ[𝓝 x] (fun y : ℝ ↦ (r : ℝ) / y + (logDeriv g (y : ℂ)).re) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact re_logDeriv_pow_mul hg r hy.ne' (hn y hy)
  have hmul : (fun y : ℝ ↦ y ^ (k + m) * iteratedDeriv m
      (fun v : ℝ ↦ (logDeriv (fun z : ℂ ↦ z ^ r * g z) (v : ℂ)).re) y)
      =ᶠ[𝓝 x] (fun y : ℝ ↦ y ^ (k + m) * iteratedDeriv m
        (fun v : ℝ ↦ (r : ℝ) / v + (logDeriv g (v : ℂ)).re) y) :=
    (heq.iteratedDeriv m).mono fun y hy ↦ congrArg (y ^ (k + m) * ·) hy
  rw [hmul.iteratedDeriv_eq k]
  exact Real.weighted_iteratedDeriv_const_div_add hL r m k hx

end Complex
