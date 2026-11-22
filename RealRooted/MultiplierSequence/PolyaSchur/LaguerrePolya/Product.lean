module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hadamard
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Laguerre--Pólya tests using auxiliary products

Multiplication by a nonzero Laguerre--Pólya function detects membership for a
real entire function of order at most one which does not vanish at zero.
The auxiliary function may vanish at zero. Its exclusion as the identically
zero function is essential because the library uses a zero-aware class.

This is the order-at-most-one case of the product argument in O'Sullivan,
*Zeros of Jensen polynomials and asymptotics for the Riemann xi function*,
Theorem 3.5, https://arxiv.org/abs/2007.13582.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- A nonzero Laguerre--Pólya auxiliary detects membership for a real entire
function of order at most one which is nonzero at the origin. -/
theorem isLaguerrePolya_mul_iff_of_orderLE_one {f g : ℂ → ℂ}
    (horder : TauCeti.OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hconj : ∀ z, f (conj z) = conj (f z)) (hg : IsLaguerrePolya g) (hg0 : g ≠ 0) :
    IsLaguerrePolya (f * g) ↔ IsLaguerrePolya f := by
  constructor
  · intro hfg
    have hfg0 : f * g ≠ 0 := by
      intro hzero
      have hfana : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
      rcases hfana.eq_zero_or_eq_zero_of_mul_eq_zero hg.analyticOnNhd
        (fun z _ => congrFun hzero z) isPreconnected_univ with h | h
      · exact hf0 (h 0 (Set.mem_univ _))
      · exact hg0 (funext fun z => h z (Set.mem_univ _))
    exact isLaguerrePolya_of_orderLE_one horder hf hf0 hconj fun z hz =>
      hfg.im_eq_zero_of_eq_zero hfg0 (by simp [Pi.mul_apply, hz])
  · exact fun h => h.mul hg

end RealRooted
