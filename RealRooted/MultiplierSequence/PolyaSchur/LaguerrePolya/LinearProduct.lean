module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.Mathlib.Algebra.Polynomial.LinearProductDegree

/-!
# Signed real linear products in the Laguerre--Pólya class

Unlike the positive Type-I statement, this closure theorem allows slopes of
both signs. Zero slopes and finite or empty effective products are included.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- A real linear factor with arbitrary signed slope is Laguerre--Pólya. -/
theorem isLaguerrePolya_one_add_mul (a : ℝ) :
    IsLaguerrePolya (fun z : ℂ => 1 + (a : ℂ) * z) := by
  simpa using isLaguerrePolya_eval_map (splits_one_add_C_mul_X a)

/-- A summable family of signed real slopes defines a Laguerre--Pólya product. -/
theorem isLaguerrePolya_tprod_one_add_mul {ι : Type*} {a : ι → ℝ} (ha : Summable a) :
    IsLaguerrePolya (fun z : ℂ => ∏' i, (1 + (a i : ℂ) * z)) :=
  IsLaguerrePolya.of_hasProdLocallyUniformly
    (fun i => isLaguerrePolya_one_add_mul (a i))
    (hasProdLocallyUniformlyOn_one_add_ofReal_mul ha)

end RealRooted
