/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.Mathlib.Analysis.Complex.LinearProduct
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalMixtures
import TauCeti.Analysis.Calculus.LogDerivUniformlyOn
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Logarithmic derivatives of positive linear products on the positive axis

The logarithmic derivative of a convergent product of nonnegative linear
factors is its sum of positive resolvent kernels. The equality holds at every
nonnegative real point, including zero, with repeated slopes counted.
-/

public section

open Filter Topology

namespace Complex

/-- A nonnegative linear slope cannot give a zero factor at a nonnegative
real argument. -/
theorem one_add_ofReal_mul_ne_zero {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    1 + (a : ℂ) * (x : ℂ) ≠ 0 := by
  have h : 0 < 1 + a * x := by positivity
  exact_mod_cast h.ne'

/-- A convergent product of nonnegative linear factors has no zeros on the
nonnegative real axis. -/
theorem tprod_one_add_ofReal_mul_ne_zero {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {x : ℝ} (hx : 0 ≤ x) :
    (∏' i, (1 + (a i : ℂ) * (x : ℂ))) ≠ 0 := by
  have hsum : Summable (fun i ↦ ‖(a i : ℂ) * (x : ℂ)‖) := by
    simpa only [norm_mul, norm_real] using hs.norm.mul_right ‖(x : ℂ)‖
  intro hz
  obtain ⟨i, hi⟩ := (TauCeti.tprod_one_add_eq_zero_iff hsum).mp hz
  exact one_add_ofReal_mul_ne_zero (ha i) hx hi

/-- The real logarithmic derivative of a positive linear product is the
convergent sum of its resolvent kernels at every nonnegative argument. -/
theorem re_logDeriv_tprod_one_add {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {x : ℝ} (hx : 0 ≤ x) :
    (logDeriv (fun z : ℂ ↦ ∏' i, (1 + (a i : ℂ) * z)) (x : ℂ)).re =
      ∑' i, a i / (1 + a i * x) := by
  have hprod := (tendstoLocallyUniformly_prod_one_add a hs).tendstoLocallyUniformlyOn
    (s := Set.univ)
  have hlog := hprod.sum_logDeriv (V := {(x : ℂ)}) isOpen_univ
    (fun i ↦ by fun_prop) (Set.subset_univ _)
    (fun i z hz ↦ by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact one_add_ofReal_mul_ne_zero (ha i) hx)
    (fun z hz ↦ by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact tprod_one_add_ofReal_mul_ne_zero ha hs hx)
  have hpoint := hlog.tendsto_at (Set.mem_singleton (x : ℂ))
  have hterms (i : ℕ) :
      logDeriv (fun z : ℂ ↦ 1 + (a i : ℂ) * z) (x : ℂ) =
        ((a i / (1 + a i * x) : ℝ) : ℂ) := by
    simp only [logDeriv_apply, deriv_const_add, deriv_const_mul_id]
    norm_cast
  simp_rw [hterms] at hpoint
  have hsum := TauCeti.summable_const_div_one_add_mul_pow ha ha hs 1 hx
  simp only [pow_one] at hsum
  have hreal := continuous_ofReal.continuousAt.tendsto.comp hsum.hasSum.tendsto_sum_nat
  have hcomplex : Tendsto
      (fun n : ℕ ↦ ∑ i ∈ Finset.range n, ((a i / (1 + a i * x) : ℝ) : ℂ))
      atTop (𝓝 ((∑' i, a i / (1 + a i * x) : ℝ) : ℂ)) := by
    convert hreal using 1
    funext n
    norm_cast
  have h := congrArg Complex.re (tendsto_nhds_unique hpoint hcomplex)
  simpa only [ofReal_re] using h

end Complex
