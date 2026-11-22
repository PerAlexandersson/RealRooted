module

public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.LaguerreInequalities.CanonicalRepresentation
import RealRooted.LaguerreInequalities.Translation
import RealRooted.Mathlib.Analysis.Analytic.CountableZeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality

/-!
# The unrestricted generalized Laguerre criterion

For a real entire function, nonnegativity of every generalized Laguerre
coefficient at every real point is equivalent to membership in the
Laguerre--Pólya class. No growth, order, or genus hypothesis is imposed, and the
identically zero function is included.

This is the zero-aware form of Csordas--Vishnyakova (2013), Theorem 2.3. The
converse uses a finite Nevanlinna measure and its atomic canonical product.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- All generalized Laguerre inequalities characterize the Laguerre--Pólya
class among real entire functions, including the identically zero function.
This is the converse in Csordas--Vishnyakova (2013), Theorem 2.3, without a
growth or genus assumption. -/
theorem isLaguerrePolya_of_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) : IsLaguerrePolya f := by
  by_cases hne : f = 0
  · rw [hne]
    exact IsLaguerrePolya.zero
  have hpoint : ∃ a : ℝ, f a ≠ 0 := by
    by_contra! hzero
    have heq : {x : ℝ | f x = 0} = Set.univ := Set.eq_univ_of_forall hzero
    exact Set.not_countable_univ (heq ▸ hf.countable_real_zeroSet hne)
  obtain ⟨a, ha⟩ := hpoint
  have hshift : IsLaguerrePolya (fun z : ℂ => f (z + a)) := by
    apply isLaguerrePolya_of_laguerreCoefficient_nonneg_of_ne_zero
      (f := fun z => f (z + a)) (hf.comp (by fun_prop))
    · intro z
      simpa only [map_add, conj_ofReal] using hc (z + a)
    · simpa only [zero_add] using ha
    · intro x n
      rw [laguerreCoefficient_comp_add_real]
      exact h (x + a) n
  simpa only [ofReal_one, one_mul, ofReal_neg, neg_add_cancel_right] using
    hshift.comp_affine_real 1 (-a)

/-- A real entire function is Laguerre--Pólya if and only if every generalized
Laguerre coefficient is nonnegative, with no order or genus restriction. -/
theorem isLaguerrePolya_iff_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) :
    IsLaguerrePolya f ↔ ∀ x n, 0 ≤ laguerreCoefficient f x n :=
  ⟨fun h => h.laguerreCoefficient_nonneg, isLaguerrePolya_of_laguerreCoefficient_nonneg hf hc⟩

end RealRooted
