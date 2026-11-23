module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AppellMoments
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Analytic.TaylorSeries
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Hankel positivity of analytic logarithmic-derivative coefficients

The signed Taylor coefficients of `f'/f` have positive semidefinite shifted
Hankel matrices when `f` is Type-I Laguerre--Pólya and nonzero at zero. This is
the matrix positivity assertion in the forward direction of Sokal's
logarithmic-derivative criterion, Proposition 6,
https://doi.org/10.1016/j.jmaa.2022.126432.
-/

public section

open Complex

namespace RealRooted

/-- Every shifted Hankel matrix of the signed analytic logarithmic-derivative
Taylor coefficients of a Type-I function is positive semidefinite. -/
theorem IsLaguerrePolyaTypeI.posSemidef_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      let k := i.val + j.val + r
      (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv f) 0).re / k.factorial) := by
  have hreal (k : ℕ) : Complex.ofReal (iteratedDeriv k f 0).re = iteratedDeriv k f 0 :=
    ofReal_re_iteratedDeriv_zero hf.toLaguerrePolya.conj k
  have h0re : (f 0).re ≠ 0 := by
    intro hz
    have h := hreal 0
    simp only [iteratedDeriv_zero, hz, ofReal_zero] at h
    exact h0 h.symm
  have hm := hf.posSemidef_signed_coeff_logOf h0re n r
  convert hm using 1
  apply Iff.of_eq
  apply congrArg Matrix.PosSemidef
  funext i j
  dsimp only
  let k := i.val + j.val + r
  have heq := AnalyticAt.re_iteratedDeriv_logDeriv_eq_coeff_logOf
    (hf.toLaguerrePolya.differentiable.analyticAt 0) h0 hreal k
  change (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv f) 0).re / k.factorial =
    (-1 : ℝ) ^ (k + 1 + 1) * ((k + 1 : ℕ) : ℝ) * PowerSeries.coeff (k + 1)
      (PowerSeries.logOf (PowerSeries.mk
        (fun j => (iteratedDeriv j f 0).re / (j.factorial * (f 0).re))))
  rw [Nat.cast_add, Nat.cast_one, mul_div_assoc, heq,
    show k + 1 + 1 = k + 2 by lia, pow_add]
  ring

end RealRooted
