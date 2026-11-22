module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.LaguerreInequalities.Analytic
import RealRooted.LaguerreInequalities.GeneratingPolynomial
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import RealRooted.PFPolynomial.Closure
import Mathlib.Algebra.Polynomial.Expand

/-!
# Total positivity of the generalized Laguerre coefficients

For a Laguerre--Pólya function `f` and real `x`, the sequence of generalized
Laguerre coefficients is Pólya-frequency. This strengthens the generalized
Laguerre inequalities to nonnegativity of every Toeplitz minor.
-/

public section

open Complex Filter Polynomial Topology

namespace RealRooted

/-- At each real point, the generalized Laguerre coefficients of a
Laguerre--Pólya function form a Pólya-frequency sequence. -/
theorem IsLaguerrePolya.isPolyaFreqSeq_laguerreCoefficient {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (x : ℝ) : IsPolyaFreqSeq (laguerreCoefficient f x) := by
  have hc := hf.differentiable.continuous
  obtain ⟨p, hp, hlim⟩ := hf
  have hs (n : ℕ) : (p n).Splits := (hp n).elim (fun h => h ▸ Splits.zero) id
  have hplus := hlim.comp (fun z : ℂ => (x : ℂ) + z * I) (by fun_prop)
  have hminus := hlim.comp (fun z : ℂ => (x : ℂ) - z * I) (by fun_prop)
  have hprod := hplus.mul₀ hminus (hc.comp (by fun_prop)) (hc.comp (by fun_prop))
  have hexpand : TendstoLocallyUniformly
      (fun n z => ((expand ℝ 2 (laguerreGeneratingPolynomial (p n) x)).map ofRealHom).eval z)
      (laguerreProduct f x) atTop := by
    convert hprod using 1
    · ext n z
      simp only [Pi.mul_apply, Function.comp_apply, expand_eq_comp_X_pow,
        Polynomial.map_comp, Polynomial.map_pow, map_X, eval_comp, eval_pow, eval_X,
        eval_laguerreGeneratingPolynomial (hs n)]
    · rfl
  apply IsPolyaFreqSeq.of_tendsto
    (fun n => (isPFPolynomial_laguerreGeneratingPolynomial (p n) x).to_sequence)
  intro k
  simpa only [coeff_expand_mul' (by norm_num : 0 < 2), Complex.div_natCast_re,
    laguerreCoefficient] using
    Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hexpand (2 * k)

/-- Every generalized Laguerre coefficient of a Laguerre--Pólya function is
nonnegative on the real axis. -/
theorem IsLaguerrePolya.laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (x : ℝ) (n : ℕ) : 0 ≤ laguerreCoefficient f x n :=
  (hf.isPolyaFreqSeq_laguerreCoefficient x).nonneg n

end RealRooted
