/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroDifference
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Square-root-step bounds for the zeta zero contribution under RH

Taking step `sqrt x` and cutoff `ceil (sqrt x) + 4` in the head/tail estimate
bounds the complete zero contribution by `C * sqrt x * log(x)^2` for `25 ≤ x`.
The statement covers both forward and backward differences.
-/

public section

open Complex Set

namespace RiemannHypothesis

private theorem sqrt_cutoff_bounds {x : ℝ} (hx : 25 ≤ x) :
    0 < Real.sqrt x ∧ 4 ≤ ⌈Real.sqrt x⌉₊ + 4 ∧
    Real.sqrt x ≤ (⌈Real.sqrt x⌉₊ + 4 : ℕ) ∧
    ((⌈Real.sqrt x⌉₊ + 4 : ℕ) : ℝ) ≤ x ∧ 1 ≤ Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have ht5 : 5 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by norm_num; exact hx)
  have ht0 : 0 < Real.sqrt x := by linarith
  have hsq := Real.sq_sqrt hx0
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg x)
  have hceil : Real.sqrt x ≤ (⌈Real.sqrt x⌉₊ : ℝ) := Nat.le_ceil _
  have hlog : 1 ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_three]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  refine ⟨ht0, by lia, ?_, ?_, hlog⟩
  · push_cast
    linarith
  · push_cast
    nlinarith

private theorem sqrt_cutoff_expression_le {x : ℝ} (hx : 25 ≤ x) :
    let N := ⌈Real.sqrt x⌉₊ + 4
    2 * x ^ (1 / 2 : ℝ) * (1 + Real.log N) ^ 2 +
      (8 * x ^ (3 / 2 : ℝ) / Real.sqrt x) * ((1 + Real.log N) / N) ≤
        40 * (Real.sqrt x * Real.log x ^ 2) := by
  dsimp only
  let N := ⌈Real.sqrt x⌉₊ + 4
  obtain ⟨ht0, hN4, htN, hNx, hlog1⟩ := sqrt_cutoff_bounds hx
  have hx0 : 0 ≤ x := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; lia)
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogNx : Real.log N ≤ Real.log x := Real.log_le_log hN0 hNx
  have hhalf : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have hthree : x ^ (3 / 2 : ℝ) = Real.sqrt x ^ 3 := by
    simpa using Real.rpow_div_two_eq_sqrt (3 : ℝ) hx0
  have hcoef : 8 * x ^ (3 / 2 : ℝ) / Real.sqrt x = 8 * x := by
    rw [hthree]
    calc
      8 * Real.sqrt x ^ 3 / Real.sqrt x = 8 * Real.sqrt x ^ 2 := by
        field_simp
      _ = 8 * x := by rw [Real.sq_sqrt hx0]
  have hdiv : x / N ≤ Real.sqrt x := by
    apply (div_le_iff₀ hN0).mpr
    have hm := mul_le_mul_of_nonneg_left htN ht0.le
    simpa only [Real.mul_self_sqrt hx0] using hm
  have hlogSq : (1 + Real.log N) ^ 2 ≤ (1 + Real.log x) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hhead : 2 * Real.sqrt x * (1 + Real.log N) ^ 2 ≤
      2 * Real.sqrt x * (1 + Real.log x) ^ 2 :=
    mul_le_mul_of_nonneg_left hlogSq (by positivity)
  have htail : (8 * x) * ((1 + Real.log N) / N) ≤
      8 * Real.sqrt x * (1 + Real.log x) ^ 2 := by
    calc
      _ = 8 * (x / N) * (1 + Real.log N) := by ring
      _ ≤ 8 * Real.sqrt x * (1 + Real.log x) := by gcongr
      _ ≤ 8 * Real.sqrt x * (1 + Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith :
          1 + Real.log x ≤ (1 + Real.log x) ^ 2) (by positivity)
  have hlogs : (1 + Real.log x) ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith
  rw [hhalf, hcoef]
  calc
    _ ≤ 10 * Real.sqrt x * (1 + Real.log x) ^ 2 := by linarith
    _ ≤ 10 * Real.sqrt x * (4 * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = _ := by ring

/-- Under RH, the multiplicity-weighted zero contribution to a square-root finite difference
is absolutely summable and bounded by `C sqrt(x) log(x)^2` for `25 ≤ x`. -/
theorem exists_tsum_norm_riemannZeta_sqrt_difference_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : ℝ, 25 ≤ x →
      y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) → |y - z| ≤ Real.sqrt x →
      let f := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) *
          (((y : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1)) -
            (z : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1))) / (Real.sqrt x : ℂ))
      Summable (fun ρ ↦ ‖f ρ‖) ∧ (∑' ρ, ‖f ρ‖) ≤ C * (Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := hRH.exists_tsum_norm_riemannZeta_difference_le
  refine ⟨40 * K, by positivity, fun x y z hx hy hz hyz ↦ ?_⟩
  obtain ⟨ht0, hN4, _, _, _⟩ := sqrt_cutoff_bounds hx
  have hb := hbound (⌈Real.sqrt x⌉₊ + 4) hN4 x (Real.sqrt x) y z
    (by linarith) ht0 hy hz hyz
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ K * (40 * (Real.sqrt x * Real.log x ^ 2)) :=
      mul_le_mul_of_nonneg_left (sqrt_cutoff_expression_le hx) hK.le
    _ = _ := by ring

end RiemannHypothesis
