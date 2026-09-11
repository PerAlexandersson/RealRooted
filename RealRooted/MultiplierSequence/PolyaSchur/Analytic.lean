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

/-- The coefficient-form rescaling agrees with substitution by `X / n`. -/
theorem rescaledJensenPolynomial_eq_jensenPolynomial_comp (n : ℕ)
    (gamma : ℕ → ℝ) :
    rescaledJensenPolynomial n gamma =
      (jensenPolynomial n gamma).comp (C ((n : ℝ)⁻¹) * X) := by
  ext k
  rw [coeff_rescaledJensenPolynomial, Polynomial.comp_C_mul_X_coeff,
    coeff_jensenPolynomial]
  split <;> simp_all [mul_left_comm, mul_comm]

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

/-- The rescaled Jensen coefficient has the summable majorant supplied by
the exponential-generating coefficient of `gamma`. -/
theorem norm_coeff_rescaledJensenPolynomial_le (n k : ℕ) (gamma : ℕ → ℝ) :
    ‖(rescaledJensenPolynomial n gamma).coeff k‖ ≤ ‖gamma k‖ / k.factorial := by
  rw [coeff_rescaledJensenPolynomial]
  split
  · calc
      ‖(n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k‖ =
          ‖(n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k‖ * ‖gamma k‖ := by
        have hreorder : (n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k =
            ((n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k) * gamma k := by
          ring
        rw [hreorder, norm_mul]
      _ ≤ (1 / (k.factorial : ℝ)) * ‖gamma k‖ :=
        mul_le_mul_of_nonneg_right (norm_choose_mul_inv_pow_le n k) (norm_nonneg _)
      _ = ‖gamma k‖ / k.factorial := by ring
  · simp only [norm_zero]
    exact div_nonneg (norm_nonneg _) (by positivity)

/-- Rescaled Jensen polynomials converge coefficientwise to the exponential
generating coefficients of `gamma`. -/
theorem tendsto_rescaledJensenPolynomial_coeffwise (gamma : ℕ → ℝ) :
    Tendsto (fun n k => (rescaledJensenPolynomial n gamma).coeff k) atTop
      (𝓝 fun k => gamma k / k.factorial) := by
  rw [tendsto_pi_nhds]
  intro k
  exact tendsto_coeff_rescaledJensenPolynomial gamma k

end RealRooted
