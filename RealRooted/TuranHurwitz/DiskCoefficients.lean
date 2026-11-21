module

public import RealRooted.TuranHurwitz.DiskKernel
public import RealRooted.TuranHurwitz.DiskInduction
import RealRooted.TuranHurwitz.TanhCoefficients
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The coefficient lemma for arbitrary complex disk parameters

The coefficients are defined by the actual formal product kernel. Its parameter
derivative gives the normalized positive-weight step, which preserves degree
and excludes all zeros outside the unit disk.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The polynomial `G` defined by the even coefficient of the complex product kernel. -/
@[expose] noncomputable def diskCoefficient (d : ℝ) (eta : ℕ → ℂ) (n ell : ℕ) : ℂ[X] :=
  PowerSeries.coeff (2 * n) (diskKernel d eta ell)

/-- The defining coefficient formula for the product kernel, with normalized real powers. -/
theorem diskCoefficient_eq_coeff_prod (d : ℝ) (eta : ℕ → ℂ) (n ell : ℕ) :
    diskCoefficient d eta n ell = PowerSeries.coeff (2 * n)
      ((PowerSeries.binomialSeries ℝ d).subst (-complexTanhSquare) *
        (∏ j ∈ Finset.range ell, (1 - PowerSeries.C (C (eta j)) * complexTanhSquare)) *
        (PowerSeries.binomialSeries ℝ (-(d + ell))).subst
          (-PowerSeries.C (X : ℂ[X]) * complexTanhSquare)) := by
  rw [diskCoefficient, diskKernel, diskNumerator_eq_prod, tanhDenominator]

/-- The base coefficient is the complex scalar extension of the real tanh coefficient. -/
theorem diskCoefficient_zero (d : ℝ) (eta : ℕ → ℂ) (n : ℕ) :
    diskCoefficient d eta n 0 =
      (PowerSeries.coeff (2 * n) (tanhKernel d)).map (algebraMap ℝ ℂ) := by
  rw [diskCoefficient, diskKernel_zero, PowerSeries.coeff_map]
  rfl

/-- Comparing formal coefficients gives the weighted differential step before division. -/
theorem diskCoefficient_succ_mul (d : ℝ) (eta : ℕ → ℂ) (n ell : ℕ) :
    C ((d + ell : ℝ) : ℂ) * diskCoefficient d eta n (ell + 1) =
      C ((d + ell : ℝ) : ℂ) * diskCoefficient d eta n ell +
        (X - C (eta ell)) * (diskCoefficient d eta n ell).derivative := by
  have h := congrArg (PowerSeries.coeff (2 * n)) (diskKernel_succ_mul d eta ell)
  rw [show PowerSeries.C (X : ℂ[X]) - PowerSeries.C (C (eta ell)) =
      PowerSeries.C (X - C (eta ell)) by rw [map_sub]] at h
  simpa only [map_add, PowerSeries.coeff_C_mul, coeff_complexParameterDerivative,
    diskCoefficient] using h

/-- The actual kernel coefficient satisfies the normalized positive-weight recurrence. -/
theorem diskCoefficient_succ {d : ℝ} (hd : 0 < d) (eta : ℕ → ℂ) (n ell : ℕ) :
    diskCoefficient d eta n (ell + 1) =
      diskStep (d + ell) (eta ell) (diskCoefficient d eta n ell) := by
  have ha : 0 < d + (ell : ℝ) := add_pos_of_pos_of_nonneg hd (Nat.cast_nonneg _)
  have hne : ((d + ell : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  calc
    _ = C (((d + ell : ℝ) : ℂ)⁻¹) *
        (C ((d + ell : ℝ) : ℂ) * diskCoefficient d eta n (ell + 1)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    _ = _ := by rw [diskCoefficient_succ_mul]; rfl

/-- Shi's coefficient lemma: every coefficient has degree `n` and all roots in the disk. -/
theorem diskCoefficient_degree_and_roots {d : ℝ} (hd : 0 < d) (eta : ℕ → ℂ)
    (heta : ∀ j, ‖eta j‖ ≤ 1) (n ell : ℕ) :
    diskCoefficient d eta n ell ≠ 0 ∧
      (diskCoefficient d eta n ell).natDegree = n ∧
      ∀ z ∈ (diskCoefficient d eta n ell).roots, ‖z‖ ≤ 1 := by
  induction ell with
  | zero =>
      rw [diskCoefficient_zero]
      refine ⟨Polynomial.map_ne_zero (coeff_even_tanhKernel_roots hd n).1, ?_,
        coeff_even_tanhKernel_complex_roots hd n⟩
      rw [natDegree_map]
      exact natDegree_coeff_even_tanhKernel hd n
  | succ ell ih =>
      have ha : 0 < d + (ell : ℝ) := add_pos_of_pos_of_nonneg hd (Nat.cast_nonneg _)
      rw [diskCoefficient_succ hd]
      exact ⟨diskStep_ne_zero ha _ ih.1,
        (diskStep_natDegree_and_leadingCoeff ha _ ih.1).1.trans ih.2.1,
        diskStep_roots_norm_le_one ha (heta ell) ih.1 ih.2.2⟩

/-- Every kernel coefficient is nonvanishing at every exterior point. -/
theorem eval_diskCoefficient_ne_zero {d : ℝ} (hd : 0 < d) (eta : ℕ → ℂ)
    (heta : ∀ j, ‖eta j‖ ≤ 1) (n ell : ℕ) {z : ℂ} (hz : 1 < ‖z‖) :
    (diskCoefficient d eta n ell).eval z ≠ 0 := by
  obtain ⟨hne, _, hroots⟩ := diskCoefficient_degree_and_roots hd eta heta n ell
  intro heval
  exact (not_le_of_gt hz) (hroots z ((mem_roots hne).mpr heval))

end RealRooted.TuranHurwitz
