module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import RealRooted.Mathlib.Analysis.Normed.Group.SparseSubfamily
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GenusOneSplit
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.CanonicalSupport
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GaussianProductBound
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples

/-!
# Sparse genus-zero factors with LP cofactors of the same Gaussian type

The selected slopes have strictly decreasing nonzero absolute values. The
complementary canonical factors and the linear exponential correction give
an explicit LP cofactor without changing its quadratic Gaussian coefficient.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- Real canonical factors with a nonpositive quadratic exponent are LP. -/
private theorem isLaguerrePolya_real_canonical {ι : Type*} (a : ι → ℝ)
    (ha : Summable (fun i ↦ a i ^ 2)) (c b : ℝ) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    IsLaguerrePolya (fun z : ℂ ↦ (c : ℂ) * z ^ k *
      exp (-(α : ℂ) * z ^ 2 + (b : ℂ) * z) *
        ∏' i, weierstrassFactor 1 ((a i : ℂ) * z)) := by
  have hpow : IsLaguerrePolya (fun z : ℂ ↦ z ^ k) := by
    simpa using isLaguerrePolya_eval_map (p := X ^ k) (Splits.X.pow k)
  have hlin : IsLaguerrePolya (fun z : ℂ ↦ exp ((b : ℂ) * z)) := by
    simpa using isLaguerrePolya_exp.comp_affine_real b 0
  have hexp : IsLaguerrePolya
      (fun z : ℂ ↦ exp (-(α : ℂ) * z ^ 2 + (b : ℂ) * z)) := by
    simpa only [exp_add, Pi.mul_def] using (isLaguerrePolya_exp_neg_mul_sq hα).mul hlin
  have hprod : IsLaguerrePolya
      (fun z : ℂ ↦ ∏' i, weierstrassFactor 1 ((a i : ℂ) * z)) := by
    simpa only [Nat.cast_one, one_mul, pow_one] using
      isLaguerrePolya_tprod_weierstrassFactor_one_pow a (fun _ ↦ 1)
        (by simpa only [Nat.cast_one, one_mul] using ha)
  simpa only [Pi.mul_def, mul_assoc] using ((hpow.mul hexp).const_mul_real c).mul hprod

/-- Infinitely many real zeros of a nonzero real canonical expression give
a summable pure genus-zero factor and an LP cofactor of the same Gaussian
type. The extracted slopes are distinct and nonzero. -/
theorem exists_genusZero_factor_of_canonical {ι : Type*} {a : ι → ℝ}
    (ha : Summable (fun i ↦ a i ^ 2)) {φ : ℂ → ℂ} {c : ℝ} (hc : c ≠ 0)
    (b : ℝ) (k : ℕ) {α : ℝ} (hα : 0 ≤ α)
    (heq : ∀ z, φ z = (c : ℂ) * z ^ k * exp (-(α : ℂ) * z ^ 2 + (b : ℂ) * z) *
      ∏' i, weierstrassFactor 1 ((a i : ℂ) * z))
    (hinf : Set.Infinite {x : ℝ | φ x = 0}) :
    ∃ (s : ℕ → ℝ) (g : ℂ → ℂ), Summable s ∧ Function.Injective s ∧
      (∀ n, s n ≠ 0) ∧ IsLaguerrePolya g ∧
      (∀ ε > 0, ∃ C > 0, ∀ z, ‖g z‖ ≤ C * Real.exp ((α + ε) * ‖z‖ ^ 2)) ∧
      ∀ z, φ z = (∏' n, (1 + (s n : ℂ) * z)) * g z := by
  have hi := infinite_support_of_canonical_real_zeros ha
    (ofReal_ne_zero.mpr hc) k α heq hinf
  obtain ⟨e, he0, heinj, _, hesum⟩ := Real.exists_summable_subfamily_of_summable_sq ha hi
  let s : ℕ → ℝ := fun n ↦ -a (e n)
  let b' : ℝ := b + ∑' n, a (e n)
  let g : ℂ → ℂ := fun z ↦ (c : ℂ) * z ^ k *
    exp (-(α : ℂ) * z ^ 2 + (b' : ℂ) * z) *
      ∏' i : {i // i ∉ Set.range e}, weierstrassFactor 1 ((a i : ℂ) * z)
  have hs : Summable (fun i : {i // i ∉ Set.range e} ↦ a i ^ 2) :=
    ha.subtype (fun i ↦ i ∉ Set.range e)
  refine ⟨s, g, hesum.neg, fun n m h ↦ heinj (neg_injective h),
    fun n ↦ neg_ne_zero.mpr (he0 n),
    isLaguerrePolya_real_canonical (fun i : {i // i ∉ Set.range e} ↦ a i)
      hs c b' k hα, ?_, ?_⟩
  · intro ε hε
    have hsC : Summable (fun i : {i // i ∉ Set.range e} ↦
        (1 : ℝ) * ‖(a i : ℂ)‖ ^ 2) := by
      simpa only [one_mul, norm_real, Real.norm_eq_abs, sq_abs] using hs
    obtain ⟨C, hC, hbound⟩ := exists_norm_canonicalProduct_le_exp_sq
      (fun i : {i // i ∉ Set.range e} ↦ (a i : ℂ)) (fun _ ↦ 1)
      (by simpa only [Nat.cast_one] using hsC) c b' k hα hε
    exact ⟨C, hC, fun z ↦ by simpa only [g, pow_one] using hbound z⟩
  · intro z
    rw [heq z, tprod_weierstrassFactor_one_eq_linear_mul_compl ha e hesum z]
    dsimp only [s, g, b']
    simp only [ofReal_neg, neg_mul, sub_eq_add_neg, ofReal_add, add_mul, exp_add]
    ring

end RealRooted
