module

import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialLogLimit
public import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerCoefficients
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
import Mathlib.Tactic

/-! # Exact positive parameter coefficients of canonical logarithmic rows -/

public section

open Filter Topology

open PowerSeries

namespace RealRooted.BrandenLeite

/-- Every positive parameter coefficient of the canonical logarithmic row
is the corresponding integer negative-power coefficient divided by the parameter degree. -/
theorem coeff_affineLogCoeff_of_ne_zero
    (Q B : PowerSeries ℝ) (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0)
    {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (affineLogCoeff Q B n).coeff k =
      (1 / (k : ℝ)) * coeff n
        (B ^ k * subst (Q - 1) (binomialSeries ℝ (-(k : ℝ)))) := by
  have hG : constantCoeff (Q - 1) = 0 := by simp [hQ]
  have hc : Continuous (fun a : ℝ ↦ coeff n
      (B ^ k * subst (Q - 1) (binomialSeries ℝ (-a - (k : ℝ))))) :=
    (continuous_coeff_mul_subst_binomialSeries (B ^ k) (Q - 1) hG n).comp
      (continuous_id.neg.sub continuous_const)
  have hlim := (Ring.tendsto_multichoose_div_nhdsGT k hk).mul
    ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hsource (a : ℝ) :
      (affineNegativePowerCoeff a Q B n).coeff k / a =
      (Ring.multichoose a k / a) * coeff n
        (B ^ k * subst (Q - 1) (binomialSeries ℝ (-a - (k : ℝ)))) := by
    change (coeff n (subst
      (map Polynomial.C Q - C Polynomial.X * map Polynomial.C B - 1)
      (binomialSeries (Polynomial ℝ) (-Polynomial.C a)))).coeff k / a = _
    rw [coeff_coeff_subst_binomialSeries_neg Q B hQ hB]
    ring
  have hlim' : Tendsto (fun a : ℝ ↦ (affineNegativePowerCoeff a Q B n).coeff k / a)
      (𝓝[>] 0) (𝓝 ((1 / (k : ℝ)) * coeff n
        (B ^ k * subst (Q - 1) (binomialSeries ℝ (-(k : ℝ)))))) := by
    have heq := hlim.congr' (Filter.Eventually.of_forall (fun a ↦ (hsource a).symm))
    simpa only [neg_zero, zero_sub] using heq
  exact tendsto_nhds_unique
    (tendsto_coeff_affineNegativePowerCoeff_div Q B hQ hB hn k) hlim'

end RealRooted.BrandenLeite
