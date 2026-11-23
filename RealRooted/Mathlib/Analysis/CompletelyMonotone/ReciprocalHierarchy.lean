/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.EulerRodrigues
public import TauCeti.Analysis.CompletelyMonotone.Basic
import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventRodrigues
import TauCeti.Analysis.CompletelyMonotone.OpenClosure
import TauCeti.Analysis.CompletelyMonotone.Power
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The reciprocal contribution to Rodrigues hierarchies

Adding `c / x` to a logarithmic derivative adds `c m! / x^(m+1)`
to row zero of its signed Rodrigues hierarchy and adds zero to every
positive row. This is the contribution of a zero at the origin.
All analytic conclusions concern the open positive half-line.
-/

public section

open Filter Topology
open scoped ContDiff

namespace Real

/-- Rodrigues differentiation respects local equality of the input. -/
theorem eulerRodrigues_eq_of_eventuallyEq {g h : ℝ → ℝ} {x : ℝ}
    (heq : g =ᶠ[𝓝 x] h) (m k : ℕ) :
    eulerRodrigues g m k x = eulerRodrigues h m k x := by
  have hmul : (fun y ↦ y ^ (m + k) * g y) =ᶠ[𝓝 x]
      (fun y ↦ y ^ (m + k) * h y) := heq.mono fun _ hy ↦ congrArg (_ * ·) hy
  rw [eulerRodrigues, eulerRodrigues, hmul.iteratedDeriv_eq k]

/-- Rodrigues differentiation is additive under finite local smoothness. -/
theorem eulerRodrigues_add {g h : ℝ → ℝ} {x : ℝ} (m k : ℕ)
    (hg : ContDiffAt ℝ k g x) (hh : ContDiffAt ℝ k h x) :
    eulerRodrigues (g + h) m k x =
      eulerRodrigues g m k x + eulerRodrigues h m k x := by
  have heq : (fun y ↦ y ^ (m + k) * (g + h) y) =
      (fun y ↦ y ^ (m + k) * g y) + (fun y ↦ y ^ (m + k) * h y) := by
    funext y
    simp only [Pi.add_apply, mul_add]
  simp only [eulerRodrigues, heq]
  have hg' : ContDiffAt ℝ k (fun y ↦ y ^ (m + k) * g y) x :=
    (contDiffAt_id.pow (m + k)).mul hg
  have hh' : ContDiffAt ℝ k (fun y ↦ y ^ (m + k) * h y) x :=
    (contDiffAt_id.pow (m + k)).mul hh
  rw [iteratedDeriv_add hg' hh', add_div]

/-- The reciprocal power matched to the normalization survives only in
row zero of the Rodrigues hierarchy. -/
theorem eulerRodrigues_const_div_pow (c : ℝ) (m k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    eulerRodrigues (fun y : ℝ ↦ c / y ^ (m + 1)) m k x =
      if k = 0 then c / x ^ (m + 1) else 0 := by
  cases k with
  | zero => simp only [eulerRodrigues_zero _ _ hx, ite_true]
  | succ k =>
      have heq : (fun y : ℝ ↦ y ^ (m + (k + 1)) * (c / y ^ (m + 1))) =ᶠ[𝓝 x]
          (fun y ↦ c * y ^ k) := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        have he : m + (k + 1) = (m + 1) + k := by lia
        rw [he, pow_add]
        field_simp [hy]
      rw [eulerRodrigues, heq.iteratedDeriv_eq (k + 1), iteratedDeriv_const_mul_field,
        iteratedDeriv_pow, Nat.descFactorial_eq_zero_iff_lt.mpr k.lt_succ_self]
      simp

/-- A reciprocal power with nonnegative numerator is completely monotone
on the open positive half-line. -/
theorem isCompletelyMonotoneOnIoi_const_div_pow {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦ c / x ^ m) := by
  apply ((TauCeti.isCompletelyMonotoneOnIoi_rpow_neg
    (show 0 ≤ (m : ℝ) by positivity)).smul hc).congr
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul, Real.rpow_neg hx.le, Real.rpow_natCast,
    div_eq_mul_inv]

/-- Alternating differentiation of `c / x` produces the positive
factorial reciprocal power. -/
theorem signed_iteratedDeriv_const_div (c : ℝ) (m : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ m * iteratedDeriv m (fun y : ℝ ↦ c / y) x =
      c * (m.factorial : ℝ) / x ^ (m + 1) := by
  rw [TauCeti.iteratedDeriv_const_div]
  have hs : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
        (c * (m.factorial : ℝ) / x ^ (m + 1)) := by ring
    _ = _ := by rw [hs, one_mul]

/-- Adding a reciprocal kernel has an explicit effect on every signed
derivative of a smooth function on the positive half-line. -/
theorem signed_iteratedDeriv_const_div_add {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) (c : ℝ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ m * iteratedDeriv m (fun y : ℝ ↦ c / y + g y) x =
      c * (m.factorial : ℝ) / x ^ (m + 1) + (-1 : ℝ) ^ m * iteratedDeriv m g x := by
  have hc : ContDiffAt ℝ m (fun y : ℝ ↦ c / y) x :=
    contDiffAt_const.div contDiffAt_id hx.ne'
  have hgm : ContDiffAt ℝ m g x :=
    (hg.contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by simp)
  change (-1 : ℝ) ^ m * iteratedDeriv m ((fun y : ℝ ↦ c / y) + g) x = _
  rw [iteratedDeriv_add hc hgm, mul_add, signed_iteratedDeriv_const_div]

/-- A reciprocal addition to a completely monotone function contributes
only to row zero of the full signed Rodrigues hierarchy. -/
theorem weighted_iteratedDeriv_const_div_add {g : ℝ → ℝ}
    (hg : TauCeti.IsCompletelyMonotoneOnIoi g) (c : ℝ) (m k : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
      iteratedDeriv m (fun z : ℝ ↦ c / z + g z) y) x =
      (if k = 0 then c * (m.factorial : ℝ) / x ^ (m + 1) else 0) +
        (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
          y ^ (k + m) * iteratedDeriv m g y) x := by
  let K : ℝ → ℝ := fun y ↦ c * (m.factorial : ℝ) / y ^ (m + 1)
  let G : ℝ → ℝ := fun y ↦ (-1 : ℝ) ^ m * iteratedDeriv m g y
  have heq : (fun y : ℝ ↦ (-1 : ℝ) ^ m *
      iteratedDeriv m (fun z : ℝ ↦ c / z + g z) y) =ᶠ[𝓝 x] K + G := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact signed_iteratedDeriv_const_div_add hg.contDiffOn c m hy
  have hK : ContDiffAt ℝ k K x :=
    contDiffAt_const.div (contDiffAt_id.pow _) (pow_ne_zero _ hx.ne')
  have hG : ContDiffAt ℝ k G x :=
    ((hg.neg_one_pow_mul_iteratedDeriv m).contDiffOn.contDiffAt
      (isOpen_Ioi.mem_nhds hx)).of_le (by simp)
  rw [← eulerRodrigues_signed_iteratedDeriv, eulerRodrigues_eq_of_eventuallyEq heq,
    eulerRodrigues_add m k hK hG]
  rw [show eulerRodrigues K m k x =
    if k = 0 then c * (m.factorial : ℝ) / x ^ (m + 1) else 0 from
      eulerRodrigues_const_div_pow _ m k hx.ne']
  rw [show G = fun y : ℝ ↦ (-1 : ℝ) ^ m * iteratedDeriv m g y from rfl,
    eulerRodrigues_signed_iteratedDeriv]

end Real
