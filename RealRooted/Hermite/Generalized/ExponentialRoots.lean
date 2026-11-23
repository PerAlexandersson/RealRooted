module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

public import Mathlib.Basic.Complex.Basic

public import Mathlib.RingTheory.PowerSeries.Exp

public import Mathlib.RingTheory.PowerSeries.Expand

public import RealRooted.Hermite.FormalDifferential.Basic

public import RealRooted.Hermite.Generalized.Basic

import RealRooted.Hermite.Generalized.ComplexScaling
import RealRooted.Hermite.Generalized.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Multiplicities of arbitrary nondegenerate exponential-stride limits
-/

public section

open Polynomial Complex

namespace RealRooted.HermitePoulain

/-- Any nonzero real parameter admits a nonzero complex root scale. -/
private theorem exists_complex_root_scale {p : ℕ} (hp : 0 < p)
    {β : ℝ} (hβ : β ≠ 0) : ∃ r : ℂ, r ≠ 0 ∧ (β : ℂ) = -r ^ p := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (-(β : ℂ)) hp
  refine ⟨r, ?_, ?_⟩
  · intro hr0
    rw [hr0, zero_pow hp.ne'] at hr
    exact (ofReal_ne_zero.mpr hβ) (neg_eq_zero.mp hr.symm)
  · rw [hr, neg_neg]

/-- Every nondegenerate limit root multiset is a rotated and scaled copy
of the generalized Hermite root multiset. -/
theorem exists_roots_formal_exp_stride_eq_map
    {p : ℕ} (hp : 0 < p) (d : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ (β : ℂ) = -r ^ p ∧
      ((formalDifferentialOperator
        (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ)))
        (X ^ d)).map ofRealHom).roots =
        ((generalizedHermite p d).map ofRealHom).roots.map (r * ·) := by
  obtain ⟨r, hr0, hr⟩ := exists_complex_root_scale hp hβ
  exact ⟨r, hr0, hr, roots_formal_exp_stride_eq_map hp d hr hr0⟩

/-- The exact zero multiplicity of a nondegenerate stride limit is the
remainder of the input degree modulo the stride. -/
theorem rootMultiplicity_zero_formal_exp_stride {p s : ℕ}
    (hp : 2 ≤ p) (hs : s < p) (q : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    ((formalDifferentialOperator
      (PowerSeries.expand p (by lia) (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ (s + p * q))).map ofRealHom).rootMultiplicity 0 = s := by
  obtain ⟨r, hr0, hr⟩ := exists_complex_root_scale (by lia : 0 < p) hβ
  have hscale := rootMultiplicity_formal_exp_stride (by lia : 0 < p) (s + p * q) hr hr0 0
  have hmap := eq_rootMultiplicity_map (p := generalizedHermite p (s + p * q))
    ofRealHom.injective 0
  simp only [mul_zero, map_zero] at hscale hmap
  exact hscale.trans (hmap.symm.trans (rootMultiplicity_zero_generalizedHermite hp hs q))

/-- Every nonzero complex root of a nondegenerate stride limit is simple. -/
theorem rootMultiplicity_formal_exp_stride_of_ne_zero {p s : ℕ}
    (hp : 2 ≤ p) (hs : s < p) (q : ℕ) {β : ℝ} (hβ : β ≠ 0) {z : ℂ} (hz : z ≠ 0)
    (hroot : ((formalDifferentialOperator
      (PowerSeries.expand p (by lia) (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ (s + p * q))).map ofRealHom).IsRoot z) :
    ((formalDifferentialOperator
      (PowerSeries.expand p (by lia) (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ (s + p * q))).map ofRealHom).rootMultiplicity z = 1 := by
  obtain ⟨r, hr0, hr⟩ := exists_complex_root_scale (by lia : 0 < p) hβ
  have hzscale : r * (z / r) = z := mul_div_cancel₀ z hr0
  have hscaled := hroot
  rw [map_formal_exp_stride_eq_scaleRoots (by lia : 0 < p) _ hr, IsRoot.def,
    ← hzscale, scaleRoots_eval_mul] at hscaled
  have hbase : ((generalizedHermite p (s + p * q)).map ofRealHom).IsRoot (z / r) :=
    (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero _ hr0)
  rw [← hzscale, rootMultiplicity_formal_exp_stride (by lia : 0 < p) _ hr hr0]
  exact rootMultiplicity_generalizedHermite_of_ne_zero hp hs q (div_ne_zero hz hr0) hbase

end RealRooted.HermitePoulain
