/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Complex.CanonicalProduct.Convergence

/-!
# Infinite zero sets require infinitely many active canonical factors
-/

public section

namespace Complex

/-- For a nonzero scalar prefactor, infinitely many real zeros of a
canonical expression force infinite support of its real slopes. Origin
factors contribute only the single possible zero at the origin. -/
theorem infinite_support_of_canonical_real_zeros {ι : Type*} {a : ι → ℝ}
    (ha : Summable (fun i ↦ a i ^ 2)) {f : ℂ → ℂ} {c b : ℂ} (hc : c ≠ 0)
    (k : ℕ) (α : ℝ)
    (heq : ∀ z, f z = c * z ^ k * exp (-(α : ℂ) * z ^ 2 + b * z) *
      ∏' i, weierstrassFactor 1 ((a i : ℂ) * z))
    (hinf : Set.Infinite {x : ℝ | f x = 0}) : (Function.support a).Infinite := by
  have hs : Summable (fun i ↦ ‖(a i : ℂ)‖ ^ 2) := by
    simpa only [norm_real, Real.norm_eq_abs, sq_abs] using ha
  intro hfin
  apply hinf
  apply ((hfin.image (fun i ↦ (a i)⁻¹)).insert 0).subset
  intro x hx
  by_cases hx0 : x = 0
  · exact Set.mem_insert_iff.mpr (Or.inl hx0)
  · apply Set.mem_insert_of_mem
    have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0
    have hz : (∏' i, weierstrassFactor 1 ((a i : ℂ) * (x : ℂ))) = 0 := by
      have h := (heq x).symm.trans hx
      exact (mul_eq_zero.mp h).resolve_left
        (mul_ne_zero (mul_ne_zero hc (pow_ne_zero k hxC)) (exp_ne_zero _))
    obtain ⟨i, hi⟩ := (tprod_weierstrassFactor_one_eq_zero_iff
      (fun i ↦ (a i : ℂ)) hs (x : ℂ)).mp hz
    have hix : a i * x = 1 := by exact_mod_cast hi
    have hi0 : a i ≠ 0 := by intro h; simp [h] at hix
    refine ⟨i, hi0, ?_⟩
    field_simp [hi0]
    nlinarith

end Complex
