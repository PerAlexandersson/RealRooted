/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Complex.CanonicalProduct.Convergence
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiniteMultiplicityProduct

/-!
# Extracting summable linear factors from genus-one canonical products

Removing `E₁(a z)` as a pure factor `1 - a z` contributes `exp(a z)`
to the cofactor. The quadratic Gaussian coefficient is unchanged.
-/

public section

open Filter Topology

namespace Complex

/-- A summable real genus-one family equals its pure linear product times
the exponential of its slope sum, including points where factors vanish. -/
theorem hasProd_weierstrassFactor_one_of_summable {ι : Type*} {a : ι → ℝ}
    (ha : Summable a) (z : ℂ) :
    HasProd (fun i ↦ weierstrassFactor 1 ((a i : ℂ) * z))
      ((∏' i, (1 - (a i : ℂ) * z)) * exp ((∑' i, a i : ℝ) * z)) := by
  have hlin : HasProd (fun i ↦ 1 - (a i : ℂ) * z)
      (∏' i, (1 - (a i : ℂ) * z)) := by
    simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using
      (hasProdLocallyUniformlyOn_one_add_ofReal_mul ha.neg).hasProd (Set.mem_univ z)
  have hexp := ((Complex.hasSum_ofReal.mpr ha.hasSum).mul_right z).cexp
  simpa only [Function.comp_def, weierstrassFactor_one_left] using hlin.mul hexp

/-- An injectively indexed summable subfamily factors from a square-summable
genus-one product as a pure linear product and an explicit linear exponential. -/
theorem tprod_weierstrassFactor_one_eq_linear_mul_compl {ι : Type*}
    {a : ι → ℝ} (ha : Summable (fun i ↦ a i ^ 2)) (e : ℕ ↪ ι)
    (he : Summable (fun n ↦ a (e n))) (z : ℂ) :
    (∏' i, weierstrassFactor 1 ((a i : ℂ) * z)) =
      ((∏' n, (1 - (a (e n) : ℂ) * z)) * exp ((∑' n, a (e n) : ℝ) * z)) *
        ∏' i : {i // i ∉ Set.range e}, weierstrassFactor 1 ((a i : ℂ) * z) := by
  have hselected := hasProd_weierstrassFactor_one_of_summable he z
  have hselected' : HasProd
      (fun i : Set.range e ↦ weierstrassFactor 1 ((a i : ℂ) * z))
      ((∏' n, (1 - (a (e n) : ℂ) * z)) * exp ((∑' n, a (e n) : ℝ) * z)) :=
    (e.injective.hasProd_range_iff
      (f := fun i ↦ weierstrassFactor 1 ((a i : ℂ) * z))).mpr hselected
  have hs : Summable (fun i : {i // i ∉ Set.range e} ↦ ‖(a i : ℂ)‖ ^ 2) := by
    simpa only [norm_real, Real.norm_eq_abs, sq_abs, Function.comp_def] using ha.subtype
      (fun i ↦ i ∉ Set.range e)
  have hcompl := (hasProdLocallyUniformlyOn_weierstrassFactor_one
    (fun i : {i // i ∉ Set.range e} ↦ (a i : ℂ)) hs).hasProd (Set.mem_univ z)
  exact (hselected'.mul_compl hcompl).tprod_eq

/-- Weighted genus-one products can be indexed by individual copies of
their factors. The equality is valid at zeros as well as nonzero points. -/
theorem tprod_weierstrassFactor_one_pow_eq_fin_copies {ι : Type*}
    (a : ι → ℂ) (m : ι → ℕ)
    (hm : Summable (fun i ↦ (m i : ℝ) * ‖a i‖ ^ 2)) (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z) ^ m i) =
      ∏' j : Σ i, Fin (m i), weierstrassFactor 1 (a j.1 * z) := by
  have hs : Summable (fun j : Σ i, Fin (m i) ↦ ‖a j.1‖ ^ 2) :=
    (TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm
  exact (HasProd.sigma_fin_const
    ((hasProdLocallyUniformlyOn_weierstrassFactor_one
      (fun j : Σ i, Fin (m i) ↦ a j.1) hs).hasProd (Set.mem_univ z))).tprod_eq

end Complex
