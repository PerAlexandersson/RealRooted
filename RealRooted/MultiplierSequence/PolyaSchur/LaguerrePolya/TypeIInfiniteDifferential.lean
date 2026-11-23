module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeICriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIGrowth
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Infinite differential operators on positive Type-I functions

Pólya's Zusatz I, page 242 of *Algebraische Untersuchungen über ganze
Funktionen vom Geschlechte Null und Eins* (1915), says that positive Type-I
symbols and targets give a Type-I output. Their exponential growth ensures
absolute convergence everywhere. The derivative-series coefficients remain
nonnegative, so the Type-II preservation theorem strengthens to Type I.
Zero functions and zeros at the origin are included.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- The differential series of two positive Type-I inputs converges
absolutely at every complex point, without an additional growth hypothesis. -/
theorem IsLaguerrePolyaTypeI.summable_norm_infiniteDifferentialApply {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolyaTypeI φ) (hf : IsLaguerrePolyaTypeI f) (z : ℂ) :
    Summable (fun n => ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖) :=
  Complex.summable_norm_infiniteDifferentialApply hφ.toLaguerrePolya.differentiable
    hφ.orderLE_one (by norm_num) hf.toLaguerrePolya.differentiable hf.orderLE_one (by norm_num) z

/-- An actual infinite differential operator with positive Type-I symbol
and target has positive Type-I output. This is Pólya's Zusatz I; convergence
follows from the inputs and is not a premise. -/
theorem IsLaguerrePolyaTypeI.infiniteDifferentialApply {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolyaTypeI φ) (hf : IsLaguerrePolyaTypeI f) :
    IsLaguerrePolyaTypeI (Complex.infiniteDifferentialApply φ f) := by
  have hLP := hφ.toLaguerrePolya.infiniteDifferentialApply hf.toLaguerrePolya
    hφ.orderLE_one (by norm_num) hf.orderLE_one (by norm_num)
  apply hLP.isLaguerrePolyaTypeI_of_nonneg
  intro k
  rw [iteratedDeriv_infiniteDifferentialApply hφ.toLaguerrePolya.differentiable
    hφ.orderLE_one (by norm_num) hf.toLaguerrePolya.differentiable hf.orderLE_one (by norm_num)]
  have hcd := hf.toLaguerrePolya.differentiable.contDiff (n := ⊤)
  have hdf := hcd.differentiable_iteratedDeriv k (WithTop.coe_lt_top _)
  have hsum := Complex.summable_norm_infiniteDifferentialApply
    hφ.toLaguerrePolya.differentiable hφ.orderLE_one (by norm_num)
    hdf (hf.orderLE_one.iteratedDeriv hf.toLaguerrePolya.differentiable k) (by norm_num) 0
  have hs := hsum.of_norm.hasSum
  apply (Complex.hasSum_re hs).nonneg
  intro n
  have hφim : (iteratedDeriv n φ 0).im = 0 := by
    rw [← ofReal_re_iteratedDeriv_zero hφ.toLaguerrePolya.conj n]
    simp
  have hφpos := (isLaguerrePolyaTypeI_iff_isLaguerrePolya_nonneg.mp hφ).2 n
  have hfpos : 0 ≤ (iteratedDeriv n (iteratedDeriv k f) 0).re := by
    simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply] using
      (isLaguerrePolyaTypeI_iff_isLaguerrePolya_nonneg.mp hf).2 (n + k)
  simp only [div_natCast_re, mul_re, hφim, zero_mul, sub_zero]
  exact div_nonneg (mul_nonneg hφpos hfpos) (Nat.cast_nonneg _)

end RealRooted
