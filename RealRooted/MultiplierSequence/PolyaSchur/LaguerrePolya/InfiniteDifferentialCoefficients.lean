module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FormalJensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DifferentialApply
import RealRooted.MultiplierSequence.JensenLimit
import RealRooted.MultiplierSequence.JensenDifferential
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialAlgebra
import RealRooted.Mathlib.Analysis.SpecificLimits.DescFactorialWeights

/-!
# Infinite differential operators with convergent coefficient series

Pólya's 1915 Zusatz III states that applying a Laguerre--Pólya differential
symbol to a Laguerre--Pólya target defines an entire function in the same class
whenever each resulting Taylor coefficient series converges. The convergence
here is that of ordinary partial sums and may be conditional. This does not
replace the separate local-disk convergence hypothesis in Zusatz II.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

private theorem iteratedDeriv_rescaledJensen_differential (a : ℕ → ℝ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n k : ℕ) :
    (iteratedDeriv k ((rescaledJensenPolynomial n a).map ofRealHom |>.differentialApply f) 0).re =
      ∑ j ∈ Finset.range (n + 1),
        ((n.descFactorial j : ℝ) / (n : ℝ) ^ j) *
          (a j * (iteratedDeriv (k + j) f 0).re / j.factorial) := by
  rw [Polynomial.iteratedDeriv_differentialApply _ hf k,
    differentialApply_rescaledJensenPolynomial, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    div_natCast_re, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
    Nat.add_comm j k]

/-- Pólya's coefficientwise infinite differential-operator theorem
(1915, Zusatz III, p. 243). Ordinary convergence of every resulting Taylor
coefficient series suffices, including a zero result or an initial zero prefix. -/
theorem IsLaguerrePolya.infinite_differential_coefficients {φ ψ : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hψ : IsLaguerrePolya ψ) {c : ℕ → ℝ}
    (hc : ∀ k, Tendsto
      (fun n => ∑ j ∈ Finset.range n,
        (iteratedDeriv j φ 0).re * (iteratedDeriv (k + j) ψ 0).re / j.factorial)
      atTop (𝓝 (c k))) :
    IsLaguerrePolya (complexExpGeneratingFunction c) := by
  let a : ℕ → ℝ := fun j => (iteratedDeriv j φ 0).re
  let F : ℕ → ℂ → ℂ := fun n =>
    (rescaledJensenPolynomial n a).map ofRealHom |>.differentialApply ψ
  have hF (n : ℕ) : IsLaguerrePolya (F n) := by
    apply hψ.differentialApply
    rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
    exact (hφ.jensenPolynomial_splits n).comp_of_natDegree_le_one
      ((natDegree_C_mul_le _ _).trans (by simp))
  have hcoeff (k : ℕ) :
      Tendsto (fun n => (iteratedDeriv k (F n) 0).re) atTop (𝓝 (c k)) := by
    have ht := Nat.tendsto_sum_descFactorial_smul (hc k)
    simpa only [F, iteratedDeriv_rescaledJensen_differential a hψ.differentiable,
      smul_eq_mul, a] using ht
  apply isLaguerrePolya_of_jensenPolynomial_splits
  intro d
  exact jensenPolynomial_splits_of_tendsto d
    (fun n => (hF n).jensenPolynomial_splits d) hcoeff

end RealRooted
