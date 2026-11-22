/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.TimeDerivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import Mathlib.Analysis.Analytic.Order

/-!
# Nonvanishing of entire heat images

Iterating the time heat equation identifies every time derivative with an even
spatial derivative. An identically zero time slice would therefore make all
time jets vanish. Entire dependence on time, together with the initial value,
excludes this for every nonzero entire input of order below two.
-/

public section

namespace Complex

/-- Iterated time differentiation of the heat sum is a signed even spatial
 derivative of its input followed by the same heat operator. -/
theorem iteratedDeriv_heatOperator_time {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun t => heatOperator t f z) =
      fun t => (-1 : ℂ) ^ k * heatOperator t (iteratedDeriv (2 * k) f) z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      ext t
      rw [iteratedDeriv_one.symm, iteratedDeriv_const_mul_field, iteratedDeriv_one]
      have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv (2 * k)
        (WithTop.coe_lt_top _)
      have ho := horder.iteratedDeriv hf (2 * k)
      rw [(hasDerivAt_heatOperator_time hdf ho hρ t z).deriv,
        iteratedDeriv_heatOperator hdf ho hρ]
      have heq : iteratedDeriv 2 (iteratedDeriv (2 * k) f) =
          iteratedDeriv (2 * (k + 1)) f := by
        simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
          Nat.mul_add, Nat.mul_one, Nat.add_comm 2]
      rw [heq, pow_succ]
      ring

/-- A complex-time heat image of a nonzero entire function of order below two
cannot vanish identically. -/
theorem heatOperator_ne_zero {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    (hne : f ≠ 0) (t : ℂ) : heatOperator t f ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
  have ha : AnalyticOnNhd ℂ (fun s => heatOperator s f z) Set.univ :=
    fun s _ => (differentiable_heatOperator_time hf horder hρ z).analyticAt s
  have hall (k : ℕ) : iteratedDeriv k (fun s => heatOperator s f z) t = 0 := by
    rw [iteratedDeriv_heatOperator_time hf horder hρ]
    dsimp only
    rw [← congrFun (iteratedDeriv_heatOperator hf horder hρ t (2 * k)) z, hzero]
    simp
  have htop : analyticOrderAt (fun s => heatOperator s f z) t = ⊤ := by
    apply ENat.eq_top_iff_forall_ge.mpr
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha t trivial)).mpr
      (fun j _ => hall j)
  have hstart : heatOperator 0 f z ≠ 0 := by simpa using hz
  have hbase : analyticOrderAt (fun s => heatOperator s f z) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hstart)
  have hfinite := ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) (Set.mem_univ t) (by simp [hbase])
  exact hfinite htop

/-- The entire heat operator vanishes identically exactly for the zero input
on the class of entire functions of order below two. -/
theorem heatOperator_eq_zero_iff {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t : ℂ) :
    heatOperator t f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf0
    exact heatOperator_ne_zero hf horder hρ hf0 t h
  · intro h
    simp [h]

end Complex
