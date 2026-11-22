module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FiniteZeros
import RealRooted.LaguerreInequalities.ZeroFree
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Finite-zero LP functions are polynomial–Gaussian products

Removing all finitely many zeros leaves a zero-free LP function. Its
Nevanlinna representation has zero measure, hence it is a real exponential
times a Gaussian. The real nonzero scalar is absorbed into the polynomial.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Every LP function nonzero at zero with finitely many distinct real
zeros is a split polynomial times a real exponential and a Gaussian. -/
theorem IsLaguerrePolya.exists_polynomial_gaussian_of_finite_zeros {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hfin : Set.Finite {r : ℝ | f r = 0}) :
    ∃ (q : ℝ[X]) (a b : ℝ), q.Splits ∧ q.coeff 0 ≠ 0 ∧ 0 ≤ b ∧ ∀ z,
      f z = (q.map ofRealHom).eval z * exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2) := by
  obtain ⟨q, g, hq, hq0, hg, hgnz, hfactor⟩ :=
    hf.exists_polynomial_factor_of_finite_zeros hf0 hfin
  obtain ⟨a, b, hb, hgexp⟩ := hg.exists_exp_quadratic_of_forall_ne_zero hgnz
  have hreal : ((g 0).re : ℂ) = g 0 := by
    simpa only [iteratedDeriv_zero] using ofReal_re_iteratedDeriv_zero hg.conj 0
  have hgre : (g 0).re ≠ 0 := by
    intro hz
    apply hgnz 0
    rw [← hreal, hz, ofReal_zero]
  refine ⟨C (g 0).re * q, a, b, hq.C_mul _, ?_, hb, ?_⟩
  · rw [coeff_C_mul]
    exact mul_ne_zero hgre hq0
  · intro z
    rw [hfactor, hgexp]
    simp only [Polynomial.map_mul, map_C, eval_mul, eval_C, ofRealHom_eq_coe, hreal]
    ring

end RealRooted
