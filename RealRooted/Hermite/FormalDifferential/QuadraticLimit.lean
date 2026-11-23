module

public import RealRooted.Hermite.FormalDifferential.Basic
public import RealRooted.SimpleRoots
import RealRooted.Hermite.FormalDifferential.CenteredLimit
import RealRooted.Hermite.FormalDifferential.Covariance
import RealRooted.Hermite.FormalDifferential.Exponential
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.SimpleRoots.Affine
import RealRooted.Hermite.GaussianOperator
import RealRooted.Mathlib.Analysis.Polynomial.SimpleRootMatching
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import Mathlib.Tactic.NormNum

/-!
# Eventual simple real roots for centered negative quadratic symbols

The fixed-degree coefficient limit is a simple Hermite polynomial. Openness
of simple real roots and invertible root scaling then give the unscaled conclusion.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.HermitePoulain

/-- A negative quadratic formal exponential sends a monic leading monomial
to a simple real-rooted monic polynomial of the same degree. -/
private theorem quadratic_limit_isMonicOfDegree_simple {s : ℝ} (hs : s < 0) (d : ℕ) :
    let σ := PowerSeries.expand 2 (by decide)
      (PowerSeries.rescale s (PowerSeries.exp ℝ))
    let H := formalDifferentialOperator σ (X ^ d)
    IsMonicOfDegree H d ∧ IsSimpleRealRooted H := by
  dsimp only
  have hσ : PowerSeries.constantCoeff (PowerSeries.expand 2 (by decide)
      (PowerSeries.rescale s (PowerSeries.exp ℝ))) = 1 := by
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  refine ⟨⟨?_, formalDifferentialOperator_monic hσ (monic_X.pow d)⟩, ?_⟩
  · rw [natDegree_formalDifferentialOperator (by rw [hσ]; exact one_ne_zero)
      (pow_ne_zero d X_ne_zero), natDegree_X_pow]
  · rw [formalDifferentialOperator_exp_quadratic]
    simpa only [Complex.ofReal_zero, zero_mul, zero_add] using
      simple_taylor_exp_quadratic 0 hs (pow_ne_zero d X_ne_zero) (Splits.X_pow d)

/-- A centered formal symbol with negative quadratic coefficient eventually
sends every monic polynomial to a polynomial with simple real roots. -/
theorem eventually_simple_centered_formalDifferentialOperator
    {ψ : PowerSeries ℝ} (hψ : PowerSeries.constantCoeff ψ < 0)
    {P : ℝ[X]} (hP : P.Monic) :
    ∀ᶠ m : ℕ in atTop,
      IsSimpleRealRooted (formalDifferentialOperator ((1 + PowerSeries.X ^ 2 * ψ) ^ m) P) := by
  let χ : PowerSeries ℝ := 1 + PowerSeries.X ^ 2 * ψ
  let r : ℕ → ℝ := fun m ↦ (m : ℝ) ^ (-(2 : ℝ)⁻¹)
  let Q : ℕ → ℝ[X] := fun m ↦
    formalDifferentialOperator ((PowerSeries.rescale (r m) χ) ^ m) (P.scaleRoots (r m))
  let σ := PowerSeries.expand 2 (by decide)
    (PowerSeries.rescale (PowerSeries.constantCoeff ψ) (PowerSeries.exp ℝ))
  let H : ℝ[X] := formalDifferentialOperator σ (X ^ P.natDegree)
  obtain ⟨hH, hHs⟩ := quadratic_limit_isMonicOfDegree_simple hψ P.natDegree
  have hPzero : P.scaleRoots 0 = X ^ P.natDegree := by
    rw [scaleRoots_zero, hP, one_smul]
  have hlim (j : ℕ) : Tendsto (fun m ↦ (Q m).coeff j) atTop (𝓝 (H.coeff j)) := by
    change Tendsto (fun m ↦ (Q m).coeff j) atTop
      (𝓝 ((formalDifferentialOperator σ (X ^ P.natDegree)).coeff j))
    rw [← hPzero]
    exact tendsto_coeff_centered_formalDifferentialOperator ψ (by decide : 0 < 2) P j
  have hdeg : ∀ᶠ m in atTop, (Q m).natDegree ≤ P.natDegree :=
    Eventually.of_forall fun m ↦ (natDegree_formalDifferentialOperator_le _ _).trans
      (le_of_eq (natDegree_scaleRoots P (r m)))
  have hevent := eventually_roots_bijection_of_coeff_tendsto hH hHs.2.1
    hHs.2.2.roots_nodup hdeg (fun j _ ↦ hlim j) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  have hr : r m ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hmpos) _).ne'
  have hQ0 : Q m ≠ 0 := by
    apply degree_ne_bot.mp
    rw [hm.1]
    exact WithBot.coe_ne_bot
  have hQs : IsSimpleRealRooted (Q m) :=
    ⟨hQ0, hm.2.1, HasSimpleRoots.of_roots_nodup hQ0 hm.2.2.1⟩
  have hχ : PowerSeries.constantCoeff (χ ^ m) ≠ 0 := by simp [χ]
  apply (isSimpleRealRooted_scaleRoots_iff hr).mp
  rw [scaleRoots_formalDifferentialOperator hχ, map_pow]
  exact hQs

end RealRooted.HermitePoulain
