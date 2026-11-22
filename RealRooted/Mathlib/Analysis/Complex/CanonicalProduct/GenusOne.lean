/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Complex.CanonicalProduct.Convergence

/-!
# Entire functions of genus one star

Pólya's genus `1*` consists of a nonnegative Gaussian times an entire function of
genus at most one. The canonical-product definition below allows arbitrary
complex zeros and a complex linear exponential; it does not impose real zeros
or membership in the Laguerre--Pólya class. Repeated slopes encode multiplicities,
and zero slopes allow finite products. The origin multiplicity is recorded
separately. As in the classical definition of genus, the zero function is excluded.

This class includes genus-one functions of order strictly between one and two.
-/

public section

open Set
open scoped ComplexConjugate

namespace Complex

/-- A Gaussian times an entire canonical product of genus at most one, with a
nonnegative real Gaussian parameter. This is Pólya's genus `1*`. -/
@[expose] def HasGenusOneStar (f : ℂ → ℂ) : Prop :=
  ∃ (c b : ℂ) (a : ℝ) (m : ℕ) (u : ℕ → ℂ), c ≠ 0 ∧ 0 ≤ a ∧
    Summable (fun n => ‖u n‖ ^ 2) ∧ ∀ z,
      f z = c * z ^ m * exp (-(a : ℂ) * z ^ 2 + b * z) *
        ∏' n, weierstrassFactor 1 (u n * z)

/-- Functions of genus one star are entire. -/
theorem HasGenusOneStar.differentiable {f : ℂ → ℂ} (hf : HasGenusOneStar f) :
    Differentiable ℂ f := by
  obtain ⟨c, b, a, m, u, _, _, hu, heq⟩ := hf
  have hP := differentiable_tprod_weierstrassFactor_one u hu
  rw [show f = _ from funext heq]
  exact ((Differentiable.mul (by fun_prop) (by fun_prop)).mul hP)

/-- A genus-one-star function is not identically zero, even when it vanishes at the origin. -/
theorem HasGenusOneStar.ne_zero {f : ℂ → ℂ} (hf : HasGenusOneStar f) : f ≠ 0 := by
  obtain ⟨c, b, a, m, u, hc, _, hu, heq⟩ := hf
  let g : ℂ → ℂ := fun z => c * exp (-(a : ℂ) * z ^ 2 + b * z) *
    ∏' n, weierstrassFactor 1 (u n * z)
  have hg : Differentiable ℂ g :=
    (Differentiable.mul (by fun_prop) (by fun_prop)).mul
      (differentiable_tprod_weierstrassFactor_one u hu)
  have hp : AnalyticOnNhd ℂ (fun z : ℂ => z ^ m) univ := by fun_prop
  intro hzero
  have hprod (z : ℂ) (_ : z ∈ univ) : z ^ m * g z = 0 := by
    have hz := heq z
    rw [hzero, Pi.zero_apply] at hz
    dsimp only [g]
    linear_combination -hz
  rcases hp.eq_zero_or_eq_zero_of_mul_eq_zero (fun z _ => hg.analyticAt z)
    hprod isPreconnected_univ with hp0 | hg0
  · simpa using hp0 1 (mem_univ _)
  · apply hc
    simpa [g] using hg0 0 (mem_univ _)

/-- Multiplication by a nonnegative Gaussian preserves genus one star. -/
theorem HasGenusOneStar.mul_exp_neg_mul_sq {f : ℂ → ℂ} (hf : HasGenusOneStar f)
    {d : ℝ} (hd : 0 ≤ d) : HasGenusOneStar (fun z => f z * exp (-(d : ℂ) * z ^ 2)) := by
  obtain ⟨c, b, a, m, u, hc, ha, hu, heq⟩ := hf
  refine ⟨c, b, a + d, m, u, hc, add_nonneg ha hd, hu, fun z => ?_⟩
  dsimp only
  rw [heq]
  have hexp : exp (-(a : ℂ) * z ^ 2 + b * z) * exp (-(d : ℂ) * z ^ 2) =
      exp (-(↑(a + d) : ℂ) * z ^ 2 + b * z) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  linear_combination c * z ^ m * (∏' n, weierstrassFactor 1 (u n * z)) * hexp

/-- Conjugation symmetry descends through any power of the variable in a continuous cofactor. -/
theorem conj_of_pow_mul {g : ℂ → ℂ} (hg : Continuous g) (m : ℕ)
    (hc : ∀ z, (conj z) ^ m * g (conj z) = conj (z ^ m * g z)) :
    ∀ z, g (conj z) = conj (g z) := by
  have heq : (fun z => g (conj z)) = fun z => conj (g z) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (hg.comp continuous_conj) (continuous_conj.comp hg)
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hcz : conj z ≠ 0 := by simpa using hz0
    have h := hc z
    rw [map_mul, map_pow] at h
    exact mul_left_cancel₀ (pow_ne_zero m hcz) h
  exact fun z => congrFun heq z

end Complex
