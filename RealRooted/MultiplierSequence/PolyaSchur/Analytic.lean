import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import RealRooted.MultiplierSequence

/-!
# Fixed-coefficient rescaled Jensen limits

This explicitly analytic leaf proves only coefficientwise convergence for
rescaled Jensen polynomials. It does not assert locally uniform convergence,
an entire-function classification, or a Laguerre--Pólya limit theorem.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The degree-`n` Jensen polynomial after the variable rescaling `X ↦ X / n`.
The convention at `n = 0` uses Lean's zero inverse. -/
def rescaledJensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k ((n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k)

@[simp]
theorem coeff_rescaledJensenPolynomial (n k : ℕ) (gamma : ℕ → ℝ) :
    (rescaledJensenPolynomial n gamma).coeff k =
      if k ≤ n then (n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k else 0 := by
  classical
  unfold rescaledJensenPolynomial
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := by simp_all
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · simp [hk]
    · intro b hb hbk
      simp [Polynomial.coeff_monomial, hbk]
    · simp_all
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hb_le : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hne : k ≠ b := by grind
      have hbk : b ≠ k := Ne.symm hne
      simp [Polynomial.coeff_monomial, hbk]

/-- Each fixed coefficient of the rescaled Jensen polynomials converges to
the corresponding exponential-generating-function coefficient. -/
theorem tendsto_coeff_rescaledJensenPolynomial (gamma : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (rescaledJensenPolynomial n gamma).coeff k) atTop
      (𝓝 (gamma k / k.factorial)) := by
  have heq : (fun n : ℕ => (rescaledJensenPolynomial n gamma).coeff k) =ᶠ[atTop]
      fun n => (n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k := by
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [coeff_rescaledJensenPolynomial, if_pos hn]
  refine Tendsto.congr' heq.symm ?_
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_choose_mul_inv_pow_atTop k).mul_const (gamma k)

end RealRooted
