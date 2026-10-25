module

public import RealRooted.Mathlib.Probability.LocalLimit
public import RealRooted.PFPolynomial.CoefficientShape

/-!
# Bender's local limit theorem for real-rooted polynomial rows

This file combines the analytic local limit theorem with Harper's central limit theorem and the
coefficient-shape consequences of the Pólya-frequency API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Polynomial

/-- Bender's local limit theorem for real-rooted rows with nonnegative coefficients and
diverging coefficient variance. -/
theorem tendsto_localLimit_of_splits {P : ℕ → ℝ[X]}
    (hne : ∀ n, P n ≠ 0) (hs : ∀ n, (P n).Splits)
    (hnn : ∀ n k, 0 ≤ (P n).coeff k)
    (hvar : Tendsto (fun n => (P n).coeffVariance) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : ℕ,
      |(P n).coeffStdDev * ((P n).coeff k / (P n).eval 1) -
        gaussianPDFReal 0 1 (((k : ℝ) - (P n).coeffMean) / (P n).coeffStdDev)| < ε := by
  apply tendsto_localLimit_of_logConcave hnn hne
  · intro n k hk
    have hpf : RealRooted.IsPFPolynomial (P n) :=
      RealRooted.IsPFPolynomial.of_realRooted_nonneg (hnn n) (hs n)
    have hlc := hpf.hasLogConcaveCoeffs
    by_cases hkd : k < (P n).natDegree
    · exact hlc k hk hkd
    · rw [coeff_eq_zero_of_natDegree_lt (by lia : (P n).natDegree < k + 1), mul_zero]
      positivity
  · intro n i j k hij hjk hi hk
    have hpf : RealRooted.IsPFPolynomial (P n) :=
      RealRooted.IsPFPolynomial.of_realRooted_nonneg (hnn n) (hs n)
    exact hpf.hasNoInternalCoeffZeros i j k hij hjk
      (le_natDegree_of_ne_zero hk) hi hk
  · exact hvar
  · exact tendsto_standardizedCoeffDistribution hs hnn hvar

end Polynomial
