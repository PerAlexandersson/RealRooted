module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivityConverse
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Product representation of nonvanishing-at-zero Type-I functions

The Edrei representation of the ordinary Taylor coefficients has no denominator
factors for an entire function. This recovers the classical Type-I product with
nonnegative exponential parameter and summable nonnegative linear slopes.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- A Type-I function nonzero at zero is its initial value times a nonnegative
real exponential and a convergent product of nonnegative linear factors. -/
theorem IsLaguerrePolyaTypeI.exists_eq_exp_mul_prod {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃ (γ : ℝ) (α : ℕ → ℝ), 0 ≤ γ ∧ (∀ i, 0 ≤ α i) ∧ Summable α ∧
      f = fun z => f 0 * Complex.exp (γ * z) * ∏' i, (1 + (α i : ℂ) * z) := by
  have hreal (k : ℕ) : ((iteratedDeriv k f 0).re : ℂ) = iteratedDeriv k f 0 :=
    ofReal_re_iteratedDeriv_zero hf.toLaguerrePolya.conj k
  have hreal0 : ((f 0).re : ℂ) = f 0 := by simpa using hreal 0
  have h0re : (f 0).re ≠ 0 := by
    intro hz
    have h := hreal 0
    simp only [iteratedDeriv_zero, hz, ofReal_zero] at h
    exact h0 h.symm
  have hpos : 0 < (f 0).re := lt_of_le_of_ne
    (by simpa using hf.isPolyaFreqSeq.nonneg 0) (Ne.symm h0re)
  have hsum : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum
      (fun k => (((iteratedDeriv k f 0).re / k.factorial : ℝ) : ℂ) * z ^ k) (f z) := by
    apply Eventually.of_forall
    intro z
    convert hasSum_taylorSeries_of_entire hf.toLaguerrePolya.differentiable 0 z using 1
    funext k
    rw [ofReal_div, ofReal_natCast, hreal]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
  obtain ⟨γ, α, hγ, hα, hs, heq⟩ := hf.isPolyaFreqSeq.exists_eq_const_mul_exp_mul_prod
    (by simpa using hpos) hf.toLaguerrePolya.differentiable hsum
  refine ⟨γ, α, hγ, hα, hs, ?_⟩
  simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, hreal0] using heq

end RealRooted
