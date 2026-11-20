module

public import RealRooted.TuranHurwitz.FormalFlow
import Mathlib.Tactic.Ring

/-!
# Formal parity of the tanh flow

Rescaling the formal variable by minus one realizes evaluation at `-t`.
The rescaling lemmas also justify its interaction with normalized binomial powers.
-/

public section

namespace RealRooted.TuranHurwitz

/-- Rescaling fixes constant series. -/
theorem rescale_constantSeries {A : Type*} [CommSemiring A] (a r : A) :
    PowerSeries.rescale a (PowerSeries.C r) = PowerSeries.C r := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C]

/-- Rescaling fixes the constant coefficient over an arbitrary semiring. -/
theorem constantCoeff_rescale_series {A : Type*} [CommSemiring A] (a : A) (f : PowerSeries A) :
    PowerSeries.constantCoeff (PowerSeries.rescale a f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
  simp

/-- Rescaling commutes with inversion of a series with nonzero constant coefficient. -/
theorem rescale_inv_series {A : Type*} [Field A] (a : A) (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.rescale a f⁻¹ = (PowerSeries.rescale a f)⁻¹ := by
  have hg : PowerSeries.constantCoeff (PowerSeries.rescale a f) ≠ 0 := by
    rwa [constantCoeff_rescale_series a f]
  have hne : PowerSeries.rescale a f ≠ 0 := by
    intro heq
    exact hg (by rw [heq, map_zero])
  apply mul_left_cancel₀ hne
  rw [← map_mul, PowerSeries.mul_inv_cancel f hf, map_one,
    PowerSeries.mul_inv_cancel _ hg]

/-- Rescaling commutes with scalar formal substitution. -/
theorem rescale_subst_scalar {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (a : A) (f : PowerSeries R) (g : PowerSeries A) (hg : PowerSeries.HasSubst g) :
    PowerSeries.rescale a (f.subst g) = f.subst (PowerSeries.rescale a g) := by
  rw [PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply hg (PowerSeries.HasSubst.smul_X' a),
    ← PowerSeries.rescale_eq_subst]

/-- Formal sinh is odd. -/
theorem rescale_neg_sinhSeries : PowerSeries.rescale (-1) sinhSeries = -sinhSeries := by
  simp only [sinhSeries, map_mul, rescale_constantSeries, map_sub,
    PowerSeries.rescale_rescale, neg_mul_neg, one_mul, PowerSeries.rescale_one,
    RingHom.id_apply]
  ring

/-- Formal cosh is even. -/
theorem rescale_neg_coshSeries : PowerSeries.rescale (-1) coshSeries = coshSeries := by
  simp only [coshSeries, map_mul, rescale_constantSeries, map_add,
    PowerSeries.rescale_rescale, neg_mul_neg, one_mul, PowerSeries.rescale_one,
    RingHom.id_apply]
  ring

/-- Formal tanh is odd. -/
theorem rescale_neg_tanhSeries : PowerSeries.rescale (-1) tanhSeries = -tanhSeries := by
  rw [tanhSeries, map_mul, rescale_neg_sinhSeries,
    rescale_inv_series _ _ (by simp), rescale_neg_coshSeries]
  ring

/-- Complex formal tanh is odd. -/
theorem rescale_neg_complexTanhSeries :
    PowerSeries.rescale (-1) complexTanhSeries = -complexTanhSeries := by
  rw [complexTanhSeries, show (-1 : ℂ) = algebraMap ℝ ℂ (-1) by simp,
    PowerSeries.rescale_map, rescale_neg_tanhSeries, map_neg]

/-- Reversing formal time changes the sign of tanh in the flow. -/
theorem rescale_neg_formalFlow (u : ℂ) :
    PowerSeries.rescale (-1) (formalFlow u) =
      (PowerSeries.C u + complexTanhSeries) *
        (1 + PowerSeries.C u * complexTanhSeries)⁻¹ := by
  rw [formalFlow, map_mul,
    rescale_inv_series _ _ (by simp)]
  simp only [flowDenominator, map_sub, map_one, map_mul, rescale_constantSeries,
    rescale_neg_complexTanhSeries, mul_neg, sub_neg_eq_add]

/-- Reversing formal time changes the sign of tanh in every binomial factor of the weight. -/
theorem rescale_neg_flowWeight (d h : ℝ) (u : ℂ) :
    PowerSeries.rescale (-1) (flowWeight d h u) =
      (PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst (-complexTanhSeries) *
        (PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst complexTanhSeries *
        (PowerSeries.binomialSeries ℝ (-d)).subst
          (PowerSeries.C u * complexTanhSeries) := by
  rw [flowWeight, map_mul, map_mul]
  rw [rescale_subst_scalar _ _ _
      (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)),
    rescale_subst_scalar _ _ _
      (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)),
    rescale_subst_scalar _ _ _
      (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp))]
  simp only [map_neg, map_mul, rescale_constantSeries,
    rescale_neg_complexTanhSeries, neg_neg, neg_mul_neg]

end RealRooted.TuranHurwitz
