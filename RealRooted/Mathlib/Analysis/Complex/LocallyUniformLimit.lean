/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Laguerre forms of locally uniform limits

This upstream-shaped shim transports nonnegativity of the real Laguerre form
through locally uniform limits of entire functions.
-/

public section

open Filter Topology

/-- The real Laguerre form is nonnegative for a locally uniform limit of entire functions whose
Laguerre forms are eventually nonnegative on the real axis. -/
theorem TendstoLocallyUniformly.laguerre_form_nonneg
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f l)
    (hdiff : ∀ᶠ n in l, Differentiable ℂ (F n))
    (hineq : ∀ᶠ n in l, ∀ x : ℝ,
      0 ≤ (deriv (F n) (x : ℂ)).re ^ 2 - (F n (x : ℂ)).re *
        (deriv (deriv (F n)) (x : ℂ)).re)
    (x : ℝ) :
    0 ≤ (deriv f (x : ℂ)).re ^ 2 - (f (x : ℂ)).re *
      (deriv (deriv f) (x : ℂ)).re := by
  have h0 : TendstoLocallyUniformlyOn F f l Set.univ := tendstoLocallyUniformlyOn_univ.2 hF
  have h1 : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) l Set.univ :=
    h0.deriv (hdiff.mono fun _ h => h.differentiableOn) isOpen_univ
  have h2 : TendstoLocallyUniformlyOn (deriv ∘ (deriv ∘ F)) (deriv (deriv f)) l Set.univ :=
    h1.deriv (hdiff.mono fun _ h => h.differentiableOn.deriv isOpen_univ) isOpen_univ
  have p0 := h0.tendsto_at (Set.mem_univ (x : ℂ))
  have p1 := h1.tendsto_at (Set.mem_univ (x : ℂ))
  have p2 := h2.tendsto_at (Set.mem_univ (x : ℂ))
  have key : Tendsto (fun n => (deriv (F n) (x : ℂ)).re ^ 2 -
      (F n (x : ℂ)).re * (deriv (deriv (F n)) (x : ℂ)).re) l
      (𝓝 ((deriv f (x : ℂ)).re ^ 2 - (f (x : ℂ)).re * (deriv (deriv f) (x : ℂ)).re)) :=
    (((Complex.continuous_re.tendsto _).comp p1).pow 2).sub
      (((Complex.continuous_re.tendsto _).comp p0).mul
        ((Complex.continuous_re.tendsto _).comp p2))
  exact ge_of_tendsto key (hineq.mono fun _ h => h x)
