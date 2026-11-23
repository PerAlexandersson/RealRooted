/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import TauCeti.Analysis.Complex.InfiniteProd
import TauCeti.Analysis.Meromorphic.Divisor
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Native divisor multiplicities of convergent linear products

At each point, the analytic order of a product of summable real linear
factors is exactly the number of factors vanishing there. That fiber is
finite. Thus repeated slopes retain their full native-divisor multiplicity;
zero slopes never contribute a zero. No sign hypothesis is needed here.
-/

public section

open Set

namespace Complex

/-- A nonconstant affine factor has a simple zero; otherwise its order is
zero. The constant factor obtained from slope zero is included. -/
theorem analyticOrderAt_one_add_mul (a z : ℂ) :
    analyticOrderAt (fun w : ℂ ↦ 1 + a * w) z = if 1 + a * z = 0 then 1 else 0 := by
  classical
  have hf : AnalyticAt ℂ (fun w : ℂ ↦ 1 + a * w) z := by fun_prop
  by_cases hz : 1 + a * z = 0
  · rw [ite_eq_left hz]
    have ha : a ≠ 0 := by
      intro h
      simp only [h, zero_mul, add_zero] at hz
      exact one_ne_zero hz
    apply hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
    simpa only [deriv_const_add, deriv_const_mul_id] using ha
  · rw [ite_eq_right hz]
    exact hf.analyticOrderAt_eq_zero.mpr hz

/-- Summability of the real slopes makes every vanishing-factor fiber
finite, including when the same nonzero slope occurs repeatedly. -/
theorem finite_linearProduct_zero_fiber {ι : Type*} {a : ι → ℝ}
    (hs : Summable a) (z : ℂ) : {i | 1 + (a i : ℂ) * z = 0}.Finite := by
  have hfin := TauCeti.finite_analyticOrderAt_one_add_ne_zero
    (u := fun i (w : ℂ) ↦ (a i : ℂ) * w) isOpen_univ (fun _ ↦ by fun_prop)
    (fun _ _ hK ↦ summableUniformlyOn_norm_ofReal_mul hs hK) (Set.mem_univ z)
  apply hfin.subset
  intro i hi
  change 1 + (a i : ℂ) * z = 0 at hi
  change analyticOrderAt (fun w : ℂ ↦ 1 + (a i : ℂ) * w) z ≠ 0
  rw [analyticOrderAt_one_add_mul, ite_eq_left hi]
  exact one_ne_zero

/-- The natural analytic order of a convergent linear product is exactly
the finite cardinality of its vanishing-factor fiber. -/
theorem analyticOrderNatAt_tprod_one_add_ofReal_mul {ι : Type*} {a : ι → ℝ}
    (hs : Summable a) (z : ℂ) :
    analyticOrderNatAt (fun w : ℂ ↦ ∏' i, (1 + (a i : ℂ) * w)) z =
      Nat.card {i // 1 + (a i : ℂ) * z = 0} := by
  classical
  have htop (i : ι) : analyticOrderAt (fun w : ℂ ↦ 1 + (a i : ℂ) * w) z ≠ ⊤ := by
    rw [analyticOrderAt_one_add_mul]
    split <;> simp
  rw [TauCeti.analyticOrderNatAt_tprod_one_add isOpen_univ (fun _ ↦ by fun_prop)
    (fun _ _ hK ↦ summableUniformlyOn_norm_ofReal_mul hs hK) (Set.mem_univ z) htop]
  have hfactor (i : ι) : analyticOrderNatAt (fun w : ℂ ↦ 1 + (a i : ℂ) * w) z =
      if 1 + (a i : ℂ) * z = 0 then 1 else 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_one_add_mul]
    split <;> simp
  simp_rw [hfactor]
  have hfin := finite_linearProduct_zero_fiber hs z
  let : Fintype {i // 1 + (a i : ℂ) * z = 0} := hfin.fintype
  calc (∑' i, if 1 + (a i : ℂ) * z = 0 then (1 : ℕ) else 0)
      = ∑' i : {i // 1 + (a i : ℂ) * z = 0}, (1 : ℕ) := by
        rw [← tsum_subtype_eq_of_support_subset
          (f := fun i ↦ if 1 + (a i : ℂ) * z = 0 then (1 : ℕ) else 0)
          (s := {i | 1 + (a i : ℂ) * z = 0}) (by
            intro i hi
            by_contra hn
            exact hi (ite_eq_right hn))]
        apply tsum_congr
        intro i
        exact ite_eq_left i.property
    _ = _ := by
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
      rfl

/-- The native divisor of a convergent linear product counts its repeated
vanishing factors exactly. -/
theorem divisor_tprod_one_add_ofReal_mul_apply {ι : Type*} {a : ι → ℝ}
    (hs : Summable a) (z : ℂ) :
    MeromorphicOn.divisor (fun w : ℂ ↦ ∏' i, (1 + (a i : ℂ) * w)) Set.univ z =
      (Nat.card {i // 1 + (a i : ℂ) * z = 0} : ℤ) := by
  have hf := differentiable_tprod_one_add_ofReal_mul hs
  have hfa : AnalyticOnNhd ℂ (fun w : ℂ ↦ ∏' i, (1 + (a i : ℂ) * w)) Set.univ :=
    fun w _ ↦ hf.analyticAt w
  rw [hfa.meromorphicOn.divisor_eq_analyticOrderNatAt
    (hf.analyticAt z) (Set.mem_univ z), analyticOrderNatAt_tprod_one_add_ofReal_mul hs z]

/-- Multiplication by a nonzero scalar preserves all native zero
multiplicities of the linear product. -/
theorem divisor_const_mul_tprod_one_add_ofReal_mul_apply {ι : Type*} {a : ι → ℝ}
    {c : ℂ} (hc : c ≠ 0) (hs : Summable a) (z : ℂ) :
    MeromorphicOn.divisor (fun w : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * w)) Set.univ z =
      (Nat.card {i // 1 + (a i : ℂ) * z = 0} : ℤ) := by
  have hP := differentiable_tprod_one_add_ofReal_mul hs
  have hf : Differentiable ℂ (fun w : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * w)) :=
    (differentiable_const c).mul hP
  have hfa : AnalyticOnNhd ℂ
      (fun w : ℂ ↦ c * ∏' i, (1 + (a i : ℂ) * w)) Set.univ :=
    fun w _ ↦ hf.analyticAt w
  rw [hfa.meromorphicOn.divisor_eq_analyticOrderNatAt
    (hf.analyticAt z) (Set.mem_univ z)]
  rw [analyticOrderNatAt_fun_const_mul (hP.analyticAt z) hc,
    analyticOrderNatAt_tprod_one_add_ofReal_mul hs z]

end Complex
