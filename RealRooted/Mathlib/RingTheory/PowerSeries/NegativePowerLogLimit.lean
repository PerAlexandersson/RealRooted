/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialLogLimit
public import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
public import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerCoefficients
public import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic

/-! # The canonical logarithmic limit of normalized formal negative powers -/

public section

open Filter Polynomial Topology

namespace PowerSeries

/-- A parameter coefficient of a substituted real binomial series is a
finite scalar sum with fixed substitution coefficients. -/
theorem coeff_coeff_subst_binomialSeries_neg_eq_sum_range
    (G : PowerSeries ℝ[X]) (hG : constantCoeff G = 0) (a : ℝ) (n k : ℕ) :
    (coeff n (subst G (binomialSeries ℝ[X] (-a)))).coeff k =
      ∑ j ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ j * Ring.multichoose a j) * (coeff n (G ^ j)).coeff k := by
  rw [coeff_subst_eq_sum_range G _ hG n, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  simp only [binomialSeries_coeff, smul_mul_assoc, one_mul, Polynomial.coeff_smul,
    smul_eq_mul, Ring.choose_neg', Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow_natCast]

/-- A positive-degree coefficient of the canonical negative power, divided
by its exponent parameter, is a finite weighted sum with logarithmic limit. -/
theorem coeff_coeff_subst_binomialSeries_neg_div_eq_sum
    (H : PowerSeries ℝ[X]) (hH : constantCoeff H = 1)
    (a : ℝ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (coeff n (subst (H - 1) (binomialSeries ℝ[X] (-a)))).coeff k / a =
      ∑ j ∈ (Finset.range (n + 1)).erase 0,
        Ring.multichoose a j / a *
          ((-1 : ℝ) ^ j * (coeff n ((H - 1) ^ j)).coeff k) := by
  have hG : constantCoeff (H - 1) = 0 := by simp [hH]
  rw [coeff_coeff_subst_binomialSeries_neg_eq_sum_range (H - 1) hG]
  have hz : ((-1 : ℝ) ^ (0 : ℕ) * Ring.multichoose a 0) *
      (coeff n ((H - 1) ^ (0 : ℕ))).coeff k = 0 := by simp [hn]
  rw [← Finset.sum_erase_add _ _ (show 0 ∈ Finset.range (n + 1) by simp), hz, add_zero,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The parameter coefficients of a formal negative power, normalized by
its positive exponent parameter, converge to the coefficients of the
negative formal logarithm. -/
theorem tendsto_coeff_coeff_subst_binomialSeries_neg_div
    (H : PowerSeries ℝ[X]) (hH : constantCoeff H = 1)
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    Tendsto (fun a : ℝ ↦
      (coeff n (subst (H - 1) (binomialSeries ℝ[X] (-Polynomial.C a)))).coeff k / a)
      (𝓝[>] 0) (𝓝 ((coeff n (-logOf H)).coeff k)) := by
  let s := (Finset.range (n + 1)).erase 0
  let d : ℕ → ℝ := fun j ↦ (-1 : ℝ) ^ j * (coeff n ((H - 1) ^ j)).coeff k
  have hs : ∀ j ∈ s, j ≠ 0 := by
    intro j hj
    exact (Finset.mem_erase.mp hj).1
  have hlim := Ring.tendsto_sum_multichoose_div_nhdsGT s hs d
  have hbin (a : ℝ) : binomialSeries ℝ[X] (-Polynomial.C a) =
      binomialSeries ℝ[X] (-a) := by
    simpa only [Polynomial.algebraMap_eq, map_neg] using
      binomialSeries_algebraMap (A := ℝ[X]) (-a)
  have hsource (a : ℝ) :
      (coeff n (subst (H - 1) (binomialSeries ℝ[X] (-Polynomial.C a)))).coeff k / a =
        ∑ j ∈ s, Ring.multichoose a j / a * d j := by
    rw [hbin]
    exact coeff_coeff_subst_binomialSeries_neg_div_eq_sum H hH a hn k
  have htarget : (coeff n (-logOf H)).coeff k = ∑ j ∈ s, d j / (j : ℝ) := by
    have hG : constantCoeff (H - 1) = 0 := by simp [hH]
    rw [map_neg, Polynomial.coeff_neg, logOf_eq,
      coeff_subst_eq_sum_range (H - 1) _ hG n, Polynomial.finsetSum_coeff,
      ← Finset.sum_neg_distrib]
    have hzero : -(coeff 0 (log ℝ[X]) * coeff n ((H - 1) ^ (0 : ℕ))).coeff k = 0 := by
      simp
    rw [← Finset.sum_erase_add _ _ (show 0 ∈ Finset.range (n + 1) by simp), hzero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    rw [← map_log (Polynomial.C : ℝ →+* ℝ[X]), coeff_map]
    simp only [coeff_log, hj0, ite_false]
    simp only [map_div₀, map_pow, map_neg, map_one, map_natCast,
      Polynomial.coeff_C_mul, d]
    rw [pow_succ]
    ring
  rw [htarget]
  exact hlim.congr' (Filter.Eventually.of_forall (fun a ↦ (hsource a).symm))

end PowerSeries
