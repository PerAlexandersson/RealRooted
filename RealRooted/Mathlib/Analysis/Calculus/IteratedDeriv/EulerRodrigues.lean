/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# An Euler recurrence for Rodrigues derivatives

Differentiating a monomial times a function gives an Euler recurrence for
`x⁻ᵐ Dᵏ(xᵐ⁺ᵏ g)`. The pointwise recurrence only needs finite differentiability
near a nonzero point. A smooth positive-half-line specialization is included.
-/

public section

open scoped ContDiff

/-- Finite smoothness implies differentiability of every lower iterated derivative. -/
theorem ContDiffAt.differentiableAt_iteratedDeriv {𝕜 F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {n : ℕ∞ω} {k : ℕ} {x : 𝕜}
    (hf : ContDiffAt 𝕜 n f x) (hk : (k : ℕ∞ω) < n) :
    DifferentiableAt 𝕜 (iteratedDeriv k f) x := by
  simpa only [iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableAt_iff] using
    hf.differentiableAt_iteratedFDeriv hk

/-- Multiplication by the variable has only two terms in the iterated product rule. -/
theorem iteratedDeriv_succ_id_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {k : ℕ} {x : 𝕜} (hf : ContDiffAt 𝕜 (k + 1 : ℕ) f x) :
    iteratedDeriv (k + 1) (fun y => y * f y) x =
      x * iteratedDeriv (k + 1) f x + (k + 1 : 𝕜) * iteratedDeriv k f x := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  have hsum := Finset.sum_eq_add_of_mem
    (s := Finset.range (k + 1 + 1))
    (f := fun i : ℕ => ((k + 1).choose i : 𝕜) *
      iteratedDeriv i (fun y : 𝕜 => y) x * iteratedDeriv (k + 1 - i) f x)
    0 1 (by simp) (by simp) (by decide)
    (fun i _ hi => by simp [iteratedDeriv_fun_id, hi.1, hi.2])
  rw [hsum]
  simp [iteratedDeriv_fun_id]

namespace Real

/-- The monomial-normalized iterated derivative used in Euler recurrences. -/
@[expose] noncomputable def eulerRodrigues (g : ℝ → ℝ) (m k : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv k (fun y => y ^ (m + k) * g y) x / x ^ m

/-- At order zero the normalized Rodrigues derivative is the original function. -/
theorem eulerRodrigues_zero (g : ℝ → ℝ) (m : ℕ) {x : ℝ} (hx : x ≠ 0) :
    eulerRodrigues g m 0 x = g x := by
  simp [eulerRodrigues, mul_div_cancel_left₀, pow_ne_zero m hx]

/-- The quotient rule, after multiplication by the independent variable. -/
private theorem quotient_euler_identity (a b x : ℝ) (m k : ℕ) (hx : x ≠ 0) :
    (x * b + (k + 1 : ℝ) * a) / x ^ m =
      (m + k + 1 : ℝ) * (a / x ^ m) +
        x * ((b * x ^ m - a * ((m : ℝ) * x ^ (m - 1))) / (x ^ m) ^ 2) := by
  cases m with
  | zero => simp; ring
  | succ m =>
    simp only [Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, pow_succ]
    field_simp [hx]
    ring

/-- Finite local smoothness gives the Euler recurrence at every nonzero point. -/
theorem eulerRodrigues_succ_of_contDiffAt {g : ℝ → ℝ} {m k : ℕ} {x : ℝ}
    (hg : ContDiffAt ℝ (k + 1 : ℕ) g x) (hx : x ≠ 0) :
    eulerRodrigues g m (k + 1) x =
      (m + k + 1 : ℝ) * eulerRodrigues g m k x +
        x * deriv (eulerRodrigues g m k) x := by
  let F : ℝ → ℝ := fun y => y ^ (m + k) * g y
  have hF : ContDiffAt ℝ (k + 1 : ℕ) F x :=
    (contDiffAt_id.pow (m + k)).mul hg
  have hA : DifferentiableAt ℝ (iteratedDeriv k F) x :=
    hF.differentiableAt_iteratedDeriv (Nat.cast_lt.mpr k.lt_succ_self)
  have hfun : (fun y : ℝ => y ^ (m + (k + 1)) * g y) = fun y => y * F y := by
    funext y
    dsimp [F]
    rw [← Nat.add_assoc, pow_succ]
    ring
  have hrec : eulerRodrigues g m (k + 1) x =
      (x * iteratedDeriv (k + 1) F x + (k + 1 : ℝ) * iteratedDeriv k F x) / x ^ m := by
    rw [eulerRodrigues, hfun, iteratedDeriv_succ_id_mul hF]
  have hderiv : deriv (eulerRodrigues g m k) x =
      (iteratedDeriv (k + 1) F x * x ^ m -
        iteratedDeriv k F x * ((m : ℝ) * x ^ (m - 1))) / (x ^ m) ^ 2 := by
    change deriv (fun y => iteratedDeriv k F y / y ^ m) x = _
    simpa only [Pi.div_def, ← iteratedDeriv_succ] using
      (hA.hasDerivAt.div (hasDerivAt_pow m x) (pow_ne_zero m hx)).deriv
  rw [hrec, hderiv]
  exact quotient_euler_identity (iteratedDeriv k F x) (iteratedDeriv (k + 1) F x) x m k hx

/-- A smooth function on the positive half-line satisfies the Euler recurrence there. -/
theorem eulerRodrigues_succ {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) (m k : ℕ) {x : ℝ} (hx : 0 < x) :
    eulerRodrigues g m (k + 1) x =
      (m + k + 1 : ℝ) * eulerRodrigues g m k x +
        x * deriv (eulerRodrigues g m k) x := by
  apply eulerRodrigues_succ_of_contDiffAt
  · exact (hg.contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by simp)
  · exact ne_of_gt hx

end Real
