module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.Deriv.Basic
import RealRooted.BorceaBranden.Transcendental.RealCoefficientBounds
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Uniform Gaussian bounds from normalized derivatives

Normalized Laguerre--Pólya functions with bounded first and second derivatives
share a Gaussian majorant on the whole complex plane. Rescaled Jensen
polynomials transfer the degree-independent polynomial estimate to entire
functions.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

/-- Normalized Laguerre--Pólya functions with bounded first two derivatives
have a common Gaussian bound throughout the complex plane. -/
theorem exists_uniform_norm_bound_of_deriv_bounds {K : ℝ} (hK : 0 ≤ K) :
    ∃ B > 0, ∃ C ≥ 0, ∀ f : ℂ → ℂ, IsLaguerrePolya f → f 0 = 1 →
      ‖deriv f 0‖ ≤ K → ‖deriv (deriv f) 0‖ ≤ K → ∀ z : ℂ,
      ‖f z‖ ≤ B * Real.exp (C * ‖z‖ ^ 2) := by
  obtain ⟨B, hB, C, hC, hbound⟩ := exists_norm_eval_le_exp_of_coeff_bounds hK
  refine ⟨B, hB, C, hC, ?_⟩
  intro f hf hf0 hf1 hf2 z
  let γ : ℕ → ℝ := fun k => (iteratedDeriv k f 0).re
  have hγ (k : ℕ) : iteratedDeriv k f 0 = (γ k : ℂ) :=
    (ofReal_re_iteratedDeriv_zero hf.conj k).symm
  have hγ1 : ‖γ 1‖ ≤ K := by
    simpa [γ, iteratedDeriv_succ] using (abs_re_le_norm (deriv f 0)).trans hf1
  have hγ2 : ‖γ 2‖ ≤ K := by
    simpa [γ, iteratedDeriv_succ] using (abs_re_le_norm (deriv (deriv f) 0)).trans hf2
  have hsum (R : ℝ) (hR : 0 ≤ R) :
      Summable (fun k => ‖γ k‖ * R ^ k / k.factorial) := by
    simpa only [hγ, norm_real] using
      summable_norm_iteratedDeriv_div_factorial hf.differentiable R hR
  have hlim := tendstoLocallyUniformly_eval_complex_rescaledJensenPolynomial_of_summable γ hsum
  have heq := eq_complexExpGeneratingFunction_of_iteratedDeriv hf.differentiable hγ
  rw [complexExpGeneratingFunction_eq_tsum] at heq
  have hpoint : Tendsto (fun n => ((rescaledJensenPolynomial n γ).map ofRealHom).eval z)
      atTop (𝓝 (f z)) := by
    rw [congrFun heq z]
    exact hlim.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)
  apply le_of_tendsto hpoint.norm
  apply Eventually.of_forall
  intro n
  apply hbound (rescaledJensenPolynomial n γ)
  · rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
    exact (hf.jensenPolynomial_splits n).comp_of_natDegree_le_one
      ((natDegree_C_mul_le _ _).trans (by simp))
  · simp [coeff_rescaledJensenPolynomial, γ, hf0]
  · have hc := norm_coeff_rescaledJensenPolynomial_le n 1 γ
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_ofNat, one_mul, mul_one, div_one] at hc
    exact hc.trans hγ1
  · have hc := norm_coeff_rescaledJensenPolynomial_le n 2 γ
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_ofNat, one_mul, mul_one, div_one] at hc
    exact hc.trans ((div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans hγ2)

/-- Bounds on the value, its inverse, and the first two derivatives control
an unnormalized Laguerre--Pólya function uniformly on the whole plane. -/
theorem exists_uniform_norm_bound_of_jet_bounds {K : ℝ} (hK : 0 ≤ K) :
    ∃ B > 0, ∃ C ≥ 0, ∀ f : ℂ → ℂ, IsLaguerrePolya f → f 0 ≠ 0 →
      ‖f 0‖ ≤ K → ‖(f 0)⁻¹‖ ≤ K → ‖deriv f 0‖ ≤ K →
      ‖deriv (deriv f) 0‖ ≤ K → ∀ z : ℂ,
      ‖f z‖ ≤ B * Real.exp (C * ‖z‖ ^ 2) := by
  obtain ⟨B, hB, C, hC, hbound⟩ := exists_uniform_norm_bound_of_deriv_bounds (sq_nonneg K)
  refine ⟨(K + 1) * B, mul_pos (by linarith) hB, C, hC, ?_⟩
  intro f hf hne hf0 hfi hf1 hf2 z
  have hreal : ((f 0).re : ℂ) = f 0 := by
    simpa using ofReal_re_iteratedDeriv_zero hf.conj 0
  let c : ℝ := (f 0).re⁻¹
  have hc : (c : ℂ) = (f 0)⁻¹ := by simp only [c, ofReal_inv, hreal]
  let G : ℂ → ℂ := fun w => (c : ℂ) * f w
  have hG : IsLaguerrePolya G := hf.const_mul_real c
  have hG0 : G 0 = 1 := by dsimp [G]; rw [hc, inv_mul_cancel₀ hne]
  have hD : deriv G = fun w => (c : ℂ) * deriv f w := by
    funext w
    exact ((hf.differentiable w).hasDerivAt.const_mul (c : ℂ)).deriv
  have hDD : deriv (deriv G) = fun w => (c : ℂ) * deriv (deriv f) w := by
    rw [hD]
    funext w
    exact ((hf.deriv.differentiable w).hasDerivAt.const_mul (c : ℂ)).deriv
  have hG1 : ‖deriv G 0‖ ≤ K ^ 2 := by
    rw [hD, hc, norm_mul, pow_two]
    exact mul_le_mul hfi hf1 (norm_nonneg _) hK
  have hG2 : ‖deriv (deriv G) 0‖ ≤ K ^ 2 := by
    rw [hDD, hc, norm_mul, pow_two]
    exact mul_le_mul hfi hf2 (norm_nonneg _) hK
  have heval : f z = f 0 * G z := by
    dsimp [G]
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [heval, norm_mul]
  calc
    _ ≤ (K + 1) * (B * Real.exp (C * ‖z‖ ^ 2)) :=
      mul_le_mul (hf0.trans (by linarith)) (hbound G hG hG0 hG1 hG2 z)
        (norm_nonneg _) (by linarith)
    _ = _ := by ring

end RealRooted
