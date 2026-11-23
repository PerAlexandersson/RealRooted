/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Minimal quadratic type of genus-one canonical products

A finite set of factors has an exponential linear bound. Square summability
makes the remaining quadratic bound arbitrarily small. The index type and
the natural multiplicities are unrestricted, including zero multiplicities.
-/

public section

open Finset

namespace Complex

/-- Taking a natural power multiplies an exponential norm-bound exponent. -/
private theorem norm_pow_le_exp_mul {w : ℂ} {B : ℝ}
    (h : ‖w‖ ≤ Real.exp B) (m : ℕ) : ‖w ^ m‖ ≤ Real.exp ((m : ℝ) * B) := by
  rw [norm_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) h m

/-- A finite exceptional set is bounded linearly; every other factor is
bounded quadratically, with its actual natural multiplicity. -/
private theorem norm_factor_le_piecewise_exp {ι : Type*} [DecidableEq ι] (a : ι → ℂ) (m : ι → ℕ)
    (s : Finset ι) (z : ℂ) (i : ι) :
    ‖weierstrassFactor 1 (a i * z) ^ m i‖ ≤ Real.exp
      (if i ∈ s then 2 * ((m i : ℝ) * ‖a i‖) * ‖z‖
        else 3 * ((m i : ℝ) * ‖a i‖ ^ 2) * ‖z‖ ^ 2) := by
  classical
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    have h := norm_pow_le_exp_mul (norm_weierstrassFactor_one_le_exp (a i * z)) (m i)
    convert h using 1
    congr 1
    rw [norm_mul]
    ring
  · rw [ite_eq_right hi]
    have h := norm_pow_le_exp_mul (norm_weierstrassFactor_one_le_exp_sq (a i * z)) (m i)
    convert h using 1
    congr 1
    rw [norm_mul, mul_pow]
    ring

/-- A small finite-sum tail gives a uniform linear-plus-quadratic bound for
the whole product. The totalized product inequality is valid also at zeros. -/
private theorem norm_product_le_exp_of_small_tail {ι : Type*}
    (a : ι → ℂ) (m : ι → ℕ) (s : Finset ι) {ε : ℝ}
    (htail : ∀ t : Finset ι, Disjoint t s →
      (∑ i ∈ t, (m i : ℝ) * ‖a i‖ ^ 2) ≤ ε / 6) (z : ℂ) :
    ‖∏' i, weierstrassFactor 1 (a i * z) ^ m i‖ ≤
      Real.exp ((2 * ∑ i ∈ s, (m i : ℝ) * ‖a i‖) * ‖z‖ + ε / 2 * ‖z‖ ^ 2) := by
  classical
  apply TauCeti.norm_tprod_le_exp_of_sum_le (norm_factor_le_piecewise_exp a m s z)
  intro t
  have hhead : (∑ i ∈ t.filter (fun i => i ∈ s), (m i : ℝ) * ‖a i‖) ≤
      ∑ i ∈ s, (m i : ℝ) * ‖a i‖ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact (mem_filter.mp hi).2
    · intro i _ _
      positivity
  have hdisjoint : Disjoint (t.filter (fun i => i ∉ s)) s := by
    rw [disjoint_left]
    intro i hi his
    exact (mem_filter.mp hi).2 his
  have ht := htail (t.filter (fun i => i ∉ s)) hdisjoint
  rw [sum_ite]
  simp only [← sum_mul, ← mul_sum]
  calc
    _ ≤ (2 * ∑ i ∈ s, (m i : ℝ) * ‖a i‖) * ‖z‖ +
        (3 * (ε / 6)) * ‖z‖ ^ 2 := by gcongr
    _ = _ := by ring

/-- Absorb the linear exponent into half of a positive quadratic allowance. -/
private theorem linear_le_half_quadratic_add {c t ε : ℝ} (hε : 0 < ε) :
    c * t ≤ ε / 2 * t ^ 2 + c ^ 2 / (2 * ε) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * ε by positivity)).mp
  calc
    (2 * ε) * (c * t) ≤ ε ^ 2 * t ^ 2 + c ^ 2 := by
      nlinarith [sq_nonneg (ε * t - c)]
    _ = (2 * ε) * (ε / 2 * t ^ 2 + c ^ 2 / (2 * ε)) := by
      field_simp [hε.ne']

/-- A genus-one canonical product with square-summable slopes and natural
multiplicities has arbitrarily small positive quadratic type. No countability
or enumeration hypothesis is needed. -/
theorem exists_norm_tprod_weierstrass_le_exp_sq {ι : Type*}
    (a : ι → ℂ) (m : ι → ℕ)
    (hm : Summable (fun i => (m i : ℝ) * ‖a i‖ ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ,
      ‖∏' i, weierstrassFactor 1 (a i * z) ^ m i‖ ≤ C * Real.exp (ε * ‖z‖ ^ 2) := by
  classical
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hm (ε / 6) (by positivity)
  have htail (t : Finset ι) (ht : Disjoint t s) :
      (∑ i ∈ t, (m i : ℝ) * ‖a i‖ ^ 2) ≤ ε / 6 := by
    have hnonneg : 0 ≤ ∑ i ∈ t, (m i : ℝ) * ‖a i‖ ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using (hs t ht).le
  let c : ℝ := 2 * ∑ i ∈ s, (m i : ℝ) * ‖a i‖
  refine ⟨Real.exp (c ^ 2 / (2 * ε)), Real.exp_pos _, fun z => ?_⟩
  calc
    _ ≤ Real.exp (c * ‖z‖ + ε / 2 * ‖z‖ ^ 2) :=
      norm_product_le_exp_of_small_tail a m s htail z
    _ ≤ Real.exp (c ^ 2 / (2 * ε) + ε * ‖z‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have h := linear_le_half_quadratic_add (c := c) (t := ‖z‖) hε
      linarith
    _ = _ := Real.exp_add _ _

end Complex
