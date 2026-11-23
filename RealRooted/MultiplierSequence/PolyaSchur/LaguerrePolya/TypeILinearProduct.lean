module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIIndexedProduct
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIClosure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalProduct

/-!
# Positive Type-I linear products with arbitrary indices

Nonnegative summable real slopes define a positive Type-I entire function.
Multiplying by a nonnegative real exponential preserves this conclusion.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- A linear factor with nonnegative slope belongs to the positive Type-I class. -/
theorem isLaguerrePolyaTypeI_one_add_mul {a : ℝ} (ha : 0 ≤ a) :
    IsLaguerrePolyaTypeI (fun z : ℂ ↦ 1 + (a : ℂ) * z) := by
  have hp : IsPFPolynomial (1 + C a * X) :=
    IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_one.add ((hasNonnegCoeffs_C ha).mul hasNonnegCoeffs_X))
      (Splits.of_natDegree_le_one ((natDegree_add_le _ _).trans
        (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))))
  simpa using hp.isLaguerrePolyaTypeI

/-- A summable family of nonnegative linear slopes gives a positive Type-I
function. This includes arbitrary finite and empty index sets. -/
theorem isLaguerrePolyaTypeI_tprod_one_add_mul {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    IsLaguerrePolyaTypeI (fun z : ℂ ↦ ∏' i, (1 + (a i : ℂ) * z)) := by
  exact IsLaguerrePolyaTypeI.of_hasProdLocallyUniformly
    (fun i ↦ isLaguerrePolyaTypeI_one_add_mul (ha i))
    (hasProdLocallyUniformlyOn_one_add_ofReal_mul hs)

/-- A nonnegative real exponential belongs to the positive Type-I class. -/
theorem isLaguerrePolyaTypeI_exp_mul {σ : ℝ} (hσ : 0 ≤ σ) :
    IsLaguerrePolyaTypeI (fun z : ℂ ↦ exp ((σ : ℂ) * z)) := by
  simpa only [ofReal_one, pow_zero, mul_one, one_mul, ofReal_zero, zero_mul,
    add_zero, tprod_one] using
    isLaguerrePolyaTypeI_product (c := 1) zero_le_one 0 hσ
      (y := fun _ : ℕ ↦ 0) (fun _ ↦ le_rfl) summable_zero

/-- The genus-zero product with nonnegative exponential coefficient and
summable nonnegative slopes belongs to the positive Type-I class. -/
theorem isLaguerrePolyaTypeI_exp_mul_tprod {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {σ : ℝ} (hσ : 0 ≤ σ) :
    IsLaguerrePolyaTypeI (fun z : ℂ ↦
      exp ((σ : ℂ) * z) * ∏' i, (1 + (a i : ℂ) * z)) := by
  exact (isLaguerrePolyaTypeI_exp_mul hσ).mul
    (isLaguerrePolyaTypeI_tprod_one_add_mul ha hs)

end RealRooted
