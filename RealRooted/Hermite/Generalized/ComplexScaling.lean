module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

public import Mathlib.RingTheory.PowerSeries.Exp

public import Mathlib.RingTheory.PowerSeries.Expand

public import RealRooted.Hermite.FormalDifferential.Basic

public import RealRooted.Hermite.Generalized.Basic

import RealRooted.Hermite.Generalized.DifferentialIdentity
import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Basic.Complex.Basic
import RealRooted.Hermite.Generalized.Monic

/-!
# Complex scaling of generalized Hermite limits

If `r^p=-beta`, multiplication of every root by `r` takes the normalized
generalized Hermite polynomial to the limiting polynomial `exp(beta D^p) X^d`.
The polynomial equality includes `r=0`; root multiplicity transfer requires `r!=0`.
-/

public section

open Polynomial Complex

namespace RealRooted.HermitePoulain

/-- Every real exponential-stride limit is a complex root scaling of the
normalized generalized Hermite polynomial, with no simplicity assumption. -/
theorem map_formal_exp_stride_eq_scaleRoots
    {p : ℕ} (hp : 0 < p) (d : ℕ) {β : ℝ} {r : ℂ} (hr : (β : ℂ) = -r ^ p) :
    (formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ d)).map ofRealHom = ((generalizedHermite p d).map ofRealHom).scaleRoots r := by
  ext j
  rw [coeff_scaleRoots, natDegree_map,
    (generalizedHermite_isMonicOfDegree p d).natDegree_eq]
  simp only [coeff_map, formalDifferentialOperator_exp_stride_eq_sum _ hp, natDegree_X_pow,
    generalizedHermite, finsetSum_coeff, iterate_derivative_X_pow_eq_C_mul,
    coeff_C_mul, map_sum, map_mul, map_div₀, map_pow, map_neg,
    map_one, map_natCast, ofRealHom_eq_coe]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hpk : p * k ≤ d := (Nat.mul_le_mul_left p
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans (Nat.mul_div_le d p)
  by_cases hj : j = d - p * k
  · have hexp : d - j = p * k := by lia
    have hrpow : (β : ℂ) ^ k = (-1 : ℂ) ^ k * r ^ (p * k) := by
      rw [hr, neg_pow, pow_mul]
    simp only [hexp, hrpow]
    ring
  · simp [coeff_natCast_mul, coeff_X_pow, hj]

/-- The full root multiset of a nondegenerate exponential-stride limit is
obtained by multiplying the generalized Hermite roots by a chosen complex scale. -/
theorem roots_formal_exp_stride_eq_map
    {p : ℕ} (hp : 0 < p) (d : ℕ) {β : ℝ} {r : ℂ}
    (hr : (β : ℂ) = -r ^ p) (hr0 : r ≠ 0) :
    ((formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ d)).map ofRealHom).roots =
      ((generalizedHermite p d).map ofRealHom).roots.map (r * ·) := by
  rw [map_formal_exp_stride_eq_scaleRoots hp d hr,
    roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hr0)]

/-- Nonzero complex root scaling preserves each generalized Hermite multiplicity. -/
theorem rootMultiplicity_formal_exp_stride
    {p : ℕ} (hp : 0 < p) (d : ℕ) {β : ℝ} {r : ℂ}
    (hr : (β : ℂ) = -r ^ p) (hr0 : r ≠ 0) (z : ℂ) :
    ((formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ d)).map ofRealHom).rootMultiplicity (r * z) =
      ((generalizedHermite p d).map ofRealHom).rootMultiplicity z := by
  rw [map_formal_exp_stride_eq_scaleRoots hp d hr,
    rootMultiplicity_scaleRoots _ (isUnit_iff_ne_zero.mpr hr0).isRegular.left]

end RealRooted.HermitePoulain
