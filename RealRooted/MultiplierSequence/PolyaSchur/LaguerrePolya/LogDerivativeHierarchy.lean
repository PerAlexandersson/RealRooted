/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventHierarchy
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeCompletelyMonotone
import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventRodrigues
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Complete monotonicity of the weighted logarithmic-derivative hierarchy

For a Type-I function nonzero at zero, all the weighted derivatives
`(-1 / x)^m D^k[x^(k+m) D^m(f' / f)]` are completely monotone on `(0, ∞)`.
This contains Ruiming Zhang, *Complete monotonicity of special functions*,
arXiv:1506.07012v13, Theorem 1, while also allowing nonnegative exponential
factors, finite products and nonzero constant functions.

The proof identifies the actual derivative expression with positive resolvent
kernels. Complete monotonicity includes smoothness, and is asserted only on
the open positive half-line.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- Every member of the actual weighted logarithmic-derivative hierarchy
of a Type-I function has the positive factorial resolvent representation. -/
theorem IsLaguerrePolyaTypeI.exists_weighted_logDeriv_eq_resolvent
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ), 0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      ∀ (k m : ℕ) (x : ℝ), 0 < x →
        (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
          y ^ (k + m) * iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x =
            Real.weightedResolventSum a gamma k m x := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_re_logDeriv_eq_const_add_tsum h0
  refine ⟨gamma, a, hg, ha, hs, ?_⟩
  intro k m x hx
  let L : ℝ → ℝ := fun y ↦ (logDeriv f (y : ℂ)).re
  let g : ℝ → ℝ := fun y ↦ (-1 : ℝ) ^ m * iteratedDeriv m L y
  have hgc : TauCeti.IsCompletelyMonotoneOnIoi g :=
    hf.isCompletelyMonotoneOnIoi_signed_logDeriv h0 m
  have hbase : Set.EqOn g (Real.weightedResolventSum a gamma 0 m) (Set.Ioi 0) := by
    intro y hy
    have hlocal : L =ᶠ[𝓝 y] (fun z : ℝ ↦ gamma + ∑' i, a i / (1 + a i * z)) :=
      Filter.Eventually.mono (isOpen_Ioi.mem_nhds hy) fun z hz ↦ heq z hz.le
    dsimp only [g]
    rw [hlocal.iteratedDeriv_eq m]
    exact (Real.weightedResolventSum_zero_eq_signed_deriv ha hs gamma m hy).symm
  have h := Real.eulerRodrigues_eq_weightedResolventSum ha hs hgc.contDiffOn hbase k hx
  rw [show g = fun y : ℝ ↦ (-1 : ℝ) ^ m * iteratedDeriv m L y from rfl,
    Real.eulerRodrigues_signed_iteratedDeriv] at h
  exact h

/-- The full two-index weighted logarithmic-derivative hierarchy of a
Type-I entire function is completely monotone on the positive real axis. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
        y ^ (k + m) * iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x) := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_weighted_logDeriv_eq_resolvent h0
  exact (Real.isCompletelyMonotoneOnIoi_weightedResolventSum ha hs hg k m).congr
    fun x hx ↦ heq k m x hx

/-- Nonzero scalar normalization does not change the hierarchy. In
particular, the same-sign coefficient convention in Zhang's theorem may
be normalized to positive coefficients without changing the conclusion. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_logDeriv_const_mul
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {c : ℂ} (hc : c ≠ 0) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
        y ^ (k + m) * iteratedDeriv m
          (fun z : ℝ ↦ (logDeriv (fun w : ℂ ↦ c * f w) (z : ℂ)).re) y) x) := by
  have hlog : logDeriv (fun w : ℂ ↦ c * f w) = logDeriv f :=
    funext fun w ↦ logDeriv_const_mul w c hc
  rw [hlog]
  exact hf.isCompletelyMonotoneOnIoi_weighted_logDeriv h0 k m

end RealRooted
