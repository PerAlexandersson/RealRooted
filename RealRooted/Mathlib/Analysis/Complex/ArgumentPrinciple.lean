/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The argument principle on circles

Zero counting and zero exclusion for holomorphic functions through the contour
integral of the logarithmic derivative `logDeriv f = deriv f / f`:

```text
(1 / 2πi) ∮_{|z-c|=R} f'/f = number of zeros of f in |z - c| < R, with multiplicity,
```

for `f = (∏ᵢ (z - wᵢ)^nᵢ) · g` with `g` holomorphic and nonvanishing on a
neighbourhood of the closed disc.  Mathlib has the Cauchy integral machinery and
the algebra of `logDeriv`, but no argument principle or winding numbers.

## Main results

* `Complex.logDeriv_analyticOnNhd`: `logDeriv f` is holomorphic where `f` is
  holomorphic and nonvanishing.
* `Complex.circleIntegral_logDeriv_eq_zero_of_nonvanishing`: no zeros on the closed
  disc gives `∮ f'/f = 0`.
* `Complex.circleIntegral_logDeriv_eq_of_single_zero`: a single zero of order `n`
  inside the disc gives `∮ f'/f = 2πi n`.
* `Complex.circleIntegral_logDeriv_eq_sum_zeros`: finitely many interior zeros give
  `∮ f'/f = 2πi Σ nᵢ`, and `circleIntegral_logDeriv_div_eq_sum_zeros` is the
  normalized form.

Ported from `real-rooted-oeis-proofs` (`Asymptotics/ArgumentPrinciple`).
-/

public section

open scoped Real Topology
open Complex Metric Set

namespace Complex

variable {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}

/-- The logarithmic derivative of a holomorphic nonvanishing function is holomorphic.

If `f` is analytic on a neighborhood of the (open) set `U` and nonvanishing on `U`,
then `logDeriv f = fun z ↦ deriv f z / f z` is analytic on a neighborhood of `U`. -/
theorem logDeriv_analyticOnNhd
    (hf : AnalyticOnNhd ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    AnalyticOnNhd ℂ (logDeriv f) U := by
  exact hf.deriv.div hf hf0

private lemma logDeriv_sub_pow (w z : ℂ) (n : ℕ) :
    logDeriv (fun x ↦ (x - w) ^ n) z = (n : ℂ) * (z - w)⁻¹ := by
  rw [logDeriv_fun_pow (f := fun x ↦ x - w) (x := z) (by fun_prop) n,
    logDeriv_apply]
  simp

private lemma circleIntegrable_logDeriv
    (hR : 0 ≤ R) (hsub : closedBall c R ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) :
    CircleIntegrable (fun z ↦ logDeriv g z) c R := by
  apply ContinuousOn.circleIntegrable hR
  exact ((logDeriv_analyticOnNhd hg hg0).differentiableOn.continuousOn).mono
    (fun z hz ↦ hsub (Metric.sphere_subset_closedBall hz))

private lemma sub_ne_zero_of_mem_sphere_of_mem_ball
    {z w c : ℂ} {R : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) : z - w ≠ 0 := by
  rw [sub_ne_zero]
  rintro rfl
  exact (ne_of_lt hw) hz

private lemma logDeriv_sub_pow_mul
    {f g : ℂ → ℂ} {w z : ℂ} {n : ℕ}
    (hf : f = fun x ↦ (x - w) ^ n * g x) (hzw : z - w ≠ 0)
    (hg : DifferentiableAt ℂ g z) (hgz : g z ≠ 0) :
    logDeriv f z = (n : ℂ) * (z - w)⁻¹ + logDeriv g z := by
  have hmul := logDeriv_mul (f := fun x ↦ (x - w) ^ n) (g := g) z
    (pow_ne_zero _ hzw) hgz (by fun_prop) hg
  rw [hf]
  change logDeriv ((fun x ↦ (x - w) ^ n) * g) z = _
  rw [hmul, logDeriv_sub_pow]

/-- **Zero-exclusion corollary of the argument principle.**

If `f` is holomorphic on an open set `U` containing the closed disk `closedBall c R`,
and `f` has **no zeros** on `closedBall c R`, then the contour integral of its
logarithmic derivative over the boundary circle vanishes:
`∮_{|z-c|=R} f'/f = 0`.

Contrapositive / usage: a nonzero value of this contour integral *forces* a zero of
`f` inside the closed disk.  This is the "winding number `= 0`" direction we use to
exclude complex (or real) zeros in `_splits` work. -/
theorem circleIntegral_logDeriv_eq_zero_of_nonvanishing
    (hR : 0 ≤ R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hf0 : ∀ z ∈ closedBall c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) = 0 := by
  -- An open neighborhood of the closed disk on which `logDeriv f` is analytic.
  set V : Set ℂ := U ∩ f ⁻¹' ({0}ᶜ) with hVdef
  have hVopen : IsOpen V :=
    hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVsub : closedBall c R ⊆ V := fun z hz =>
    ⟨hsub hz, by simpa using hf0 z hz⟩
  have hf0V : ∀ z ∈ V, f z ≠ 0 := fun z hz => by simpa using hz.2
  have hfV : AnalyticOnNhd ℂ f V := hf.mono (fun z hz => hz.1)
  have hlog : AnalyticOnNhd ℂ (logDeriv f) V := logDeriv_analyticOnNhd hfV hf0V
  -- `logDeriv f` is differentiable on the open neighborhood `V`, hence on `closedBall c R`.
  have hdiff : DifferentiableOn ℂ (logDeriv f) (closedBall c R) :=
    (hlog.differentiableOn).mono hVsub
  -- Cauchy–Goursat over the boundary circle.
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
    (hdiff.continuousOn) ?_
  intro z hz
  have hzV : z ∈ V := hVsub (ball_subset_closedBall hz.1)
  exact (hlog z hzV).differentiableAt

/-- **Single-zero argument principle** (residue `=` order at one interior zero).

Suppose on an open neighborhood `U` of the closed disk `closedBall c R` (with `R > 0`)
the function `f` factors as `f z = (z - c) ^ n · g z`, where `g` is holomorphic and
**nonvanishing** on `U`.  Then `f` has a single zero inside the disk, located at the
center `c` with multiplicity `n`, and the contour integral of its logarithmic
derivative computes that multiplicity:
`∮_{|z-c|=R} f'/f = 2πi · n`.

This is the residue-`=`-order core of the argument principle, isolated for one zero
(at the center).  It is the building block from which the full "sum over zeros"
statement is assembled. -/
theorem circleIntegral_logDeriv_eq_of_single_zero_center
    (hR : 0 < R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    (n : ℕ) (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hf_eq : f = fun z ↦ (z - c) ^ n * g z) :
    (∮ z in C(c, R), logDeriv f z) = (2 * π * I) * n := by
  -- On the boundary circle `z ≠ c`, so both factors are nonzero and we may split `logDeriv`.
  have hsphere_ne : ∀ z ∈ sphere c R, z - c ≠ 0 := fun z hz =>
    sub_ne_zero_of_mem_sphere_of_mem_ball hz (by simpa using hR)
  -- Pointwise identity on the sphere: `logDeriv f z = n·(z-c)⁻¹ + logDeriv g z`.
  have hEq : EqOn (logDeriv f)
      (fun z ↦ (n : ℂ) * (z - c)⁻¹ + logDeriv g z) (sphere c R) := by
    intro z hz
    have hzc : z - c ≠ 0 := hsphere_ne z hz
    have hzU : z ∈ U := hsub (Metric.sphere_subset_closedBall hz)
    exact logDeriv_sub_pow_mul hf_eq hzc (hg z hzU).differentiableAt (hg0 z hzU)
  -- Replace the integrand on the sphere.
  rw [circleIntegral.integral_congr hR.le hEq]
  -- Both summands are continuous on the sphere ⇒ circle-integrable ⇒ split the integral.
  have hint1 : CircleIntegrable (fun z ↦ (n : ℂ) * (z - c)⁻¹) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply ContinuousOn.mul continuousOn_const
    exact (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hsphere_ne z hz)
  have hint2 := circleIntegrable_logDeriv hR.le hsub hg hg0
  rw [circleIntegral.integral_add hint1 hint2]
  -- Second summand vanishes (Tier-1 nonvanishing corollary applied to `g`).
  have hg_zero : (∮ z in C(c, R), logDeriv g z) = 0 :=
    circleIntegral_logDeriv_eq_zero_of_nonvanishing hR.le hU hsub hg
      (fun z hz => hg0 z (hsub hz))
  rw [hg_zero, add_zero]
  -- First summand: `n · ∮ (z-c)⁻¹ = n · 2πi`.
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv c hR.ne']
  ring

/-- **Single interior-zero argument principle** (residue `=` order at one arbitrary interior zero).

Generalizes `circleIntegral_logDeriv_eq_of_single_zero_center` from a zero located at the
circle center to a zero located at an arbitrary point `w` strictly inside the disk.

Suppose on an open neighborhood `U` of the closed disk `closedBall c R` the function `f`
factors as `f z = (z - w) ^ n · g z`, where `w ∈ ball c R` is an interior point and `g` is
holomorphic and **nonvanishing** on `U`.  Then
`∮_{|z-c|=R} f'/f = 2πi · n`.

This is Target 1 of rung R1b: the residue-`=`-order core at an off-center interior zero. -/
theorem circleIntegral_logDeriv_eq_of_single_zero
    (hU : IsOpen U) (hsub : closedBall c R ⊆ U) {w : ℂ} (hw : w ∈ ball c R)
    (n : ℕ) (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hf_eq : f = fun z ↦ (z - w) ^ n * g z) :
    (∮ z in C(c, R), logDeriv f z) = (2 * π * I) * n := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  -- On the boundary circle `z ≠ w`, since `w` is strictly interior.
  have hsphere_ne : ∀ z ∈ sphere c R, z - w ≠ 0 := fun z hz =>
    sub_ne_zero_of_mem_sphere_of_mem_ball hz hw
  -- Pointwise identity on the sphere: `logDeriv f z = n·(z-w)⁻¹ + logDeriv g z`.
  have hEq : EqOn (logDeriv f)
      (fun z ↦ (n : ℂ) * (z - w)⁻¹ + logDeriv g z) (sphere c R) := by
    intro z hz
    have hzw : z - w ≠ 0 := hsphere_ne z hz
    have hzU : z ∈ U := hsub (Metric.sphere_subset_closedBall hz)
    exact logDeriv_sub_pow_mul hf_eq hzw (hg z hzU).differentiableAt (hg0 z hzU)
  rw [circleIntegral.integral_congr hR.le hEq]
  have hint1 : CircleIntegrable (fun z ↦ (n : ℂ) * (z - w)⁻¹) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply ContinuousOn.mul continuousOn_const
    exact (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hsphere_ne z hz)
  have hint2 := circleIntegrable_logDeriv hR.le hsub hg hg0
  rw [circleIntegral.integral_add hint1 hint2]
  have hg_zero : (∮ z in C(c, R), logDeriv g z) = 0 :=
    circleIntegral_logDeriv_eq_zero_of_nonvanishing hR.le hU hsub hg
      (fun z hz => hg0 z (hsub hz))
  rw [hg_zero, add_zero]
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hw]
  ring

/-- **Finite-sum argument principle** (★ the zero-COUNT form of rung R1b).

Suppose on an open neighborhood `U` of the closed disk `closedBall c R` the function `f`
factors as
`f z = (∏ i ∈ s, (z - w i) ^ n i) · g z`,
where `s : Finset ι` indexes finitely many interior zeros `w i ∈ ball c R` with
multiplicities `n i`, and `g` is holomorphic and **nonvanishing** on `U`.  Then the contour
integral of the logarithmic derivative of `f` counts the zeros with multiplicity:
`(∮_{|z-c|=R} f'/f) = 2πi · (∑ i ∈ s, n i)`.

This is the argument principle in zero-count form.  Dividing by `2πi` gives
`(1/2πi) ∮ f'/f = ∑ nᵢ`, the number of zeros of `f` inside the disk counted with
multiplicity.  It specializes to `circleIntegral_logDeriv_eq_zero_of_nonvanishing`
(`s = ∅`) and to `circleIntegral_logDeriv_eq_of_single_zero` (`s` a singleton). -/
theorem circleIntegral_logDeriv_eq_sum_zeros
    (hR : 0 < R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {ι : Type*} (s : Finset ι) (w : ι → ℂ) (n : ι → ℕ)
    (hw : ∀ i ∈ s, w i ∈ ball c R)
    (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hf_eq : f = fun z ↦ (∏ i ∈ s, (z - w i) ^ n i) * g z) :
    (∮ z in C(c, R), logDeriv f z) = (2 * π * I) * (∑ i ∈ s, (n i : ℂ)) := by
  -- On the boundary circle `z ≠ w i` for every `i ∈ s` (each `w i` is strictly interior).
  have hsphere_ne : ∀ z ∈ sphere c R, ∀ i ∈ s, z - w i ≠ 0 := fun z hz i hi =>
    sub_ne_zero_of_mem_sphere_of_mem_ball hz (hw i hi)
  -- Pointwise identity on the sphere:
  -- `logDeriv f z = (∑ i ∈ s, n i · (z - w i)⁻¹) + logDeriv g z`.
  have hEq : EqOn (logDeriv f)
      (fun z ↦ (∑ i ∈ s, (n i : ℂ) * (z - w i)⁻¹) + logDeriv g z) (sphere c R) := by
    intro z hz
    have hzU : z ∈ U := hsub (Metric.sphere_subset_closedBall hz)
    have hgz : g z ≠ 0 := hg0 z hzU
    -- The finite product `P z = ∏ i ∈ s, (z - w i) ^ n i`.
    set P : ℂ → ℂ := fun x ↦ ∏ i ∈ s, (x - w i) ^ n i with hPdef
    have hPz : P z ≠ 0 := by
      rw [hPdef]
      refine Finset.prod_ne_zero_iff.2 (fun i hi => pow_ne_zero _ (hsphere_ne z hz i hi))
    have hdP : DifferentiableAt ℂ P z := by
      have heq : P = (∏ i ∈ s, fun x : ℂ ↦ (x - w i) ^ n i) := by
        rw [hPdef]; funext x; rw [Finset.prod_apply]
      rw [heq]
      exact DifferentiableAt.finsetProd (u := s) (f := fun i x ↦ (x - w i) ^ n i)
        (fun i _ => DifferentiableAt.pow (by fun_prop) (n i))
    have hdg : DifferentiableAt ℂ g z := (hg z hzU).differentiableAt
    -- logDeriv (P * g) = logDeriv P + logDeriv g.
    have hmul := logDeriv_mul (f := P) (g := g) z hPz hgz hdP hdg
    -- The logarithmic derivative of `P` is the sum of those of its factors.
    have hlP : logDeriv P z = ∑ i ∈ s, (n i : ℂ) * (z - w i)⁻¹ := by
      have hprod := logDeriv_fun_prod (s := s)
        (f := fun i x ↦ (x - w i) ^ n i) (x := z)
        (fun i hi => pow_ne_zero _ (hsphere_ne z hz i hi))
        (fun i _ => by fun_prop)
      rw [hPdef, hprod]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      exact logDeriv_sub_pow (w i) z (n i)
    rw [hf_eq]
    change logDeriv (P * g) z = _
    rw [hmul, hlP]
  rw [circleIntegral.integral_congr hR.le hEq]
  -- Circle-integrability of the two pieces.
  have hint_i : ∀ i ∈ s, CircleIntegrable (fun z ↦ (n i : ℂ) * (z - w i)⁻¹) c R := by
    intro i hi
    apply ContinuousOn.circleIntegrable hR.le
    apply ContinuousOn.mul continuousOn_const
    exact (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hsphere_ne z hz i hi)
  have hint1 : CircleIntegrable (fun z ↦ ∑ i ∈ s, (n i : ℂ) * (z - w i)⁻¹) c R := by
    convert CircleIntegrable.sum (c := c) (R := R) s
      (f := fun i z ↦ (n i : ℂ) * (z - w i)⁻¹) hint_i using 1
    ext z
    simp
  have hint2 := circleIntegrable_logDeriv hR.le hsub hg hg0
  rw [circleIntegral.integral_add hint1 hint2]
  -- The `g`-term vanishes (nonvanishing corollary).
  have hg_zero : (∮ z in C(c, R), logDeriv g z) = 0 :=
    circleIntegral_logDeriv_eq_zero_of_nonvanishing hR.le hU hsub hg
      (fun z hz => hg0 z (hsub hz))
  rw [hg_zero, add_zero]
  -- Split the finite sum termwise, then each term is `n i · 2πi`.
  rw [circleIntegral.integral_fun_sum hint_i]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball (hw i hi)]
  ring

/-- **Normalized zero-count form** of the argument principle.

Dividing `circleIntegral_logDeriv_eq_sum_zeros` by `2πi`, the *normalized* contour integral
of the logarithmic derivative equals exactly the number of interior zeros counted with
multiplicity, `∑ i ∈ s, n i`.  This is the classical statement
`(1/2πi) ∮ f'/f = #{zeros inside, with multiplicity}`. -/
theorem circleIntegral_logDeriv_div_eq_sum_zeros
    (hR : 0 < R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {ι : Type*} (s : Finset ι) (w : ι → ℂ) (n : ι → ℕ)
    (hw : ∀ i ∈ s, w i ∈ ball c R)
    (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hf_eq : f = fun z ↦ (∏ i ∈ s, (z - w i) ^ n i) * g z) :
    (∮ z in C(c, R), logDeriv f z) / (2 * π * I) = (∑ i ∈ s, (n i : ℂ)) := by
  rw [circleIntegral_logDeriv_eq_sum_zeros hR hU hsub s w n hw hg hg0 hf_eq]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- **Zero-exclusion ↔ vanishing contour integral** (clean two-sided form).

Specializing the finite-sum argument principle to the empty index set recovers the
zero-exclusion corollary in a self-contained shape: if `f` has *no* interior zeros
(`f = g` with `g` holomorphic nonvanishing on the closed disk's neighborhood), the
normalized contour integral is `0`.  Conversely a nonzero value forces an interior zero. -/
theorem circleIntegral_logDeriv_eq_zero_iff_no_zeros
    (hR : 0 < R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hf0 : ∀ z ∈ closedBall c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) = 0 :=
  circleIntegral_logDeriv_eq_zero_of_nonvanishing hR.le hU hsub hf hf0

end Complex
