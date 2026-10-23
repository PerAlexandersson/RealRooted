/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.SeriesBasic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Partial fractions for `sec + tan`

We show that the coefficients `e k` of the formal power series `sec + tan` are given by the
classical partial fraction formula
`e k = (1/π) (2π)⁻ᵏ (4^(k+1) + ∑ₙ ((1/4-(n+1))⁻¹^(k+1) + (1/4+(n+1))⁻¹^(k+1)))`,
starting from Mathlib's Mittag-Leffler expansion of the cotangent.
Adapted from Aristotle's centered-disk proof, `RequestProject/EulerAnalytic.lean`
(2026-10-23).
-/

@[expose] public section

open PowerSeries Real Filter Topology

namespace RealRooted.CenteredEulerian

/-- The real cotangent series (from Mathlib's complex version). -/
lemma real_cot_series (x : ℝ) (hx : ∀ n : ℤ, (n : ℝ) ≠ x) :
    HasSum (fun n : ℕ => 1 / (x - (n + 1)) + 1 / (x + (n + 1)))
      (π * Real.cot (π * x) - 1 / x) := by
  have hxC : (x : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.integerComplement_eq]
    rintro ⟨n, hn⟩
    exact hx n (by exact_mod_cast hn)
  have hsum : Summable fun n : ℕ => 1 / ((x : ℂ) - (n + 1)) + 1 / ((x : ℂ) + (n + 1)) := by
    have := summable_cotTerm hxC
    simpa [cotTerm] using this
  have h := cot_series_rep' hxC
  have hR : Summable fun n : ℕ => 1 / (x - (n + 1)) + 1 / (x + (n + 1)) := by
    have : (fun n : ℕ => 1 / ((x : ℂ) - (n + 1)) + 1 / ((x : ℂ) + (n + 1))) =
        fun n : ℕ => ((1 / (x - (n + 1)) + 1 / (x + (n + 1)) : ℝ) : ℂ) := by
      funext n; push_cast; ring
    rw [this] at hsum
    exact Complex.summable_ofReal.mp hsum
  convert hR.hasSum using 1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  push_cast
  exact h

/-- Geometric expansion of `1/(α - y)`. -/
lemma hasSum_inv_sub (α y : ℝ) (hα : α ≠ 0) (hy : |y| < |α|) :
    HasSum (fun k : ℕ => y ^ k * α⁻¹ ^ (k + 1)) (1 / (α - y)) := by
  have hr : |y * α⁻¹| < 1 := by
    rw [abs_mul, abs_inv]
    rw [mul_inv_lt_iff₀ (abs_pos.mpr hα)]; simpa using hy
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_left α⁻¹
  convert h using 1
  · funext k; ring
  · have hne : α - y ≠ 0 := by
      intro h0; have : y = α := by linarith
      rw [this] at hy; exact lt_irrefl _ hy
    field_simp

/-- The paired cotangent coefficient sums. -/
noncomputable def cotPairSum (k : ℕ) : ℝ :=
  ∑' n : ℕ,
    ((1 / 4 - ((n : ℝ) + 1))⁻¹ ^ (k + 1) + (1 / 4 + ((n : ℝ) + 1))⁻¹ ^ (k + 1))

/-- The analytic Taylor coefficients of `cot (π/4 - z/2)`. -/
noncomputable def eulerG (k : ℕ) : ℝ :=
  (1 / π) * (2 * π)⁻¹ ^ k * (4 ^ (k + 1) + cotPairSum k)

/-- The double-series term. -/
noncomputable def cotTau (y : ℝ) (p : ℕ × ℕ) : ℝ :=
  y ^ p.2 *
    ((1 / 4 - ((p.1 : ℝ) + 1))⁻¹ ^ (p.2 + 1) +
      (1 / 4 + ((p.1 : ℝ) + 1))⁻¹ ^ (p.2 + 1))

lemma abs_cotTau_le (y : ℝ) (hy : |y| ≤ 1 / 12) (p : ℕ × ℕ) :
    |cotTau y p| ≤ 4 * (1 / 9 : ℝ) ^ p.2 * (1 / ((p.1 : ℝ) + 1) ^ 2) := by
  obtain ⟨n, k⟩ := p
  simp only [cotTau]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : |(1 / 4 - ((n : ℝ) + 1))| = n + 3 / 4 := by
    rw [abs_of_neg (by linarith)]; ring
  have hb : |(1 / 4 + ((n : ℝ) + 1))| = n + 5 / 4 := by
    rw [abs_of_pos (by linarith)]; ring
  rcases k with _ | k
  · simp only [pow_zero, one_mul, zero_add, pow_one]
    have hne1 : (1 / 4 - ((n : ℝ) + 1)) ≠ 0 := by intro h; linarith
    have hne2 : (1 / 4 + ((n : ℝ) + 1)) ≠ 0 := by intro h; linarith
    have : (1 / 4 - ((n : ℝ) + 1))⁻¹ + (1 / 4 + ((n : ℝ) + 1))⁻¹ =
        (1 / 2) / ((1 / 4 - ((n : ℝ) + 1)) * (1 / 4 + ((n : ℝ) + 1))) := by
      rw [inv_add_inv hne1 hne2]; congr 1; ring
    rw [this, abs_div, abs_mul, ha, hb]
    have h1 : (0 : ℝ) < (n + 1) ^ 2 := by positivity
    rw [show (4 : ℝ) * 1 * (1 / ((n : ℝ) + 1) ^ 2) = 4 / (n + 1) ^ 2 by ring,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [div_le_div_iff₀ (by positivity) h1]
    norm_num
    nlinarith
  · -- k + 1 ≥ 1
    have hA : |(1 / 4 - ((n : ℝ) + 1))⁻¹| ≤ (4 / 3) * (1 / ((n : ℝ) + 1)) := by
      rw [abs_inv, ha]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      field_simp
      linarith
    have hB : |(1 / 4 + ((n : ℝ) + 1))⁻¹| ≤ (4 / 3) * (1 / ((n : ℝ) + 1)) := by
      rw [abs_inv, hb]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      field_simp
      linarith
    have hA' : |(1 / 4 - ((n : ℝ) + 1))⁻¹| ≤ 4 / 3 := by
      refine hA.trans ?_
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    have hB' : |(1 / 4 + ((n : ℝ) + 1))⁻¹| ≤ 4 / 3 := by
      refine hB.trans ?_
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    set u := 1 / ((n : ℝ) + 1) with hu
    have hu0 : 0 ≤ u := by positivity
    -- bound for |a|^(k+2) with |a| ≤ 4/3 u, |a| ≤ 4/3
    have key : ∀ a : ℝ, |a| ≤ 4 / 3 * u → |a| ≤ 4 / 3 →
        |a| ^ (k + 1 + 1) ≤ (4 / 3) ^ (k + 2) * u ^ 2 := by
      intro a h1 h2
      have : |a| ^ (k + 1 + 1) = |a| ^ k * |a| ^ 2 := by ring
      rw [this]
      have e1 : |a| ^ k ≤ (4 / 3) ^ k := pow_le_pow_left₀ (abs_nonneg _) h2 k
      have e2 : |a| ^ 2 ≤ (4 / 3 * u) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc |a| ^ k * |a| ^ 2 ≤ (4 / 3) ^ k * (4 / 3 * u) ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = (4 / 3) ^ (k + 2) * u ^ 2 := by ring
    rw [abs_mul, abs_pow]
    calc |y| ^ (k + 1) * |(1 / 4 - ((n : ℝ) + 1))⁻¹ ^ (k + 1 + 1) +
          (1 / 4 + ((n : ℝ) + 1))⁻¹ ^ (k + 1 + 1)|
        ≤ |y| ^ (k + 1) * (2 * ((4 / 3) ^ (k + 2) * u ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (abs_add_le _ _).trans ?_
          rw [abs_pow, abs_pow]
          have := key _ hA hA'
          have := key _ hB hB'
          linarith
      _ ≤ (1 / 12) ^ (k + 1) * (2 * ((4 / 3) ^ (k + 2) * u ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ (abs_nonneg _) hy _
      _ = (8 / 3) * ((1 / 12) ^ (k + 1) * (4 / 3) ^ (k + 1)) * u ^ 2 := by ring
      _ = (8 / 3) * (1 / 9) ^ (k + 1) * u ^ 2 := by
          rw [← mul_pow]; norm_num
      _ ≤ 4 * (1 / 9 : ℝ) ^ (k + 1) * (1 / ((n : ℝ) + 1) ^ 2) := by
          have hu2 : u ^ 2 = 1 / ((n : ℝ) + 1) ^ 2 := by rw [hu, div_pow, one_pow]
          rw [hu2]
          have : (0 : ℝ) ≤ (1 / 9) ^ (k + 1) * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
          nlinarith

lemma summable_cotTau_bound :
    Summable (fun p : ℕ × ℕ => 4 * (1 / 9 : ℝ) ^ p.2 * (1 / ((p.1 : ℝ) + 1) ^ 2)) := by
  have h1 : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (one_lt_two))
    simpa using this
  have h2 : Summable (fun k : ℕ => 4 * (1 / 9 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
  have := summable_mul_of_summable_norm (f := fun n : ℕ => (1 / ((n : ℝ) + 1) ^ 2))
    (g := fun k : ℕ => 4 * (1 / 9 : ℝ) ^ k) (by simpa using h1) (by
      simpa [abs_of_nonneg] using h2)
  convert this using 1
  funext p; ring

lemma summable_cotTau (y : ℝ) (hy : |y| ≤ 1 / 12) : Summable (cotTau y) :=
  Summable.of_norm_bounded summable_cotTau_bound (fun p => by
    rw [Real.norm_eq_abs]; exact abs_cotTau_le y hy p)

/-- The partial fraction expansion of `π cot (π (1/4 - y))`. -/
lemma hasSum_pi_cot (y : ℝ) (hy : |y| ≤ 1 / 12) :
    HasSum (fun k : ℕ => y ^ k * (4 ^ (k + 1) + cotPairSum k))
      (π * Real.cot (π * (1 / 4 - y))) := by
  set x := 1 / 4 - y with hxdef
  have hyb := abs_le.mp hy
  have hx : ∀ n : ℤ, (n : ℝ) ≠ x := by
    intro n hn
    have h1 : (n : ℝ) < 1 := by rw [hn]; linarith
    have h2 : (0 : ℝ) < n := by rw [hn]; linarith
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : 0 < n := by exact_mod_cast h2
    lia
  have hcot := real_cot_series x hx
  have hS := (summable_cotTau y hy).hasSum
  -- fibre over n
  have hfib1 : ∀ n : ℕ, HasSum (fun k => cotTau y (n, k))
      (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
    intro n
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hasSum_inv_sub (1 / 4 - ((n : ℝ) + 1)) y (by intro h; linarith) (by
      rw [abs_of_neg (a := 1 / 4 - ((n : ℝ) + 1)) (by linarith)]; linarith)
    have e2 := hasSum_inv_sub (1 / 4 + ((n : ℝ) + 1)) y (by intro h; linarith) (by
      rw [abs_of_pos (a := 1 / 4 + ((n : ℝ) + 1)) (by linarith)]; linarith)
    convert e1.add e2 using 1
    · funext k; simp only [cotTau]; ring
    · rw [hxdef]; congr 1 <;> congr 1 <;> ring
  have hA := hS.prod_fiberwise hfib1
  have hsumeq := hA.unique hcot
  -- fibre over k
  have hS' : HasSum (fun p : ℕ × ℕ => cotTau y (p.2, p.1)) (∑' p, cotTau y p) := by
    have := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS
    convert this using 1
    funext p
    cases p
    rfl
  have hfib2 : ∀ k : ℕ, HasSum (fun n => cotTau y (n, k)) (y ^ k * cotPairSum k) := by
    intro k
    have hsk : Summable (fun n => cotTau y (n, k)) := by
      have := (summable_cotTau y hy)
      have h2 := ((Equiv.prodComm ℕ ℕ).summable_iff.mpr this).prod_factor k
      simpa [Function.comp] using h2
    convert hsk.hasSum using 1
    rw [cotPairSum, ← tsum_mul_left]
    rfl
  have hB := hS'.prod_fiberwise hfib2
  have hgeom : HasSum (fun k : ℕ => y ^ k * 4 ^ (k + 1)) (1 / x) := by
    have := hasSum_inv_sub (1 / 4) y (by norm_num) (by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith)
    convert this using 1
    funext k; norm_num
  convert hgeom.add hB using 1
  · funext k; ring
  · rw [hsumeq]; ring

/-- Trigonometric identity: `cot (π/4 - z/2) * cos z = 1 + sin z`. -/
lemma cot_quarter_mul_cos (z : ℝ) (hz : |z| ≤ 1 / 2) :
    Real.cot (π / 4 - z / 2) * Real.cos z = 1 + Real.sin z := by
  set θ := z / 2 with hθ
  have hθb : |θ| ≤ 1 / 4 := by rw [hθ, abs_div]; norm_num; linarith
  have hz2 : z = 2 * θ := by rw [hθ]; ring
  have hc : Real.cos θ - Real.sin θ > 0 := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : Real.sin θ ≤ |θ| := (le_abs_self _).trans (Real.abs_sin_le_abs (x := θ))
    have h3 : θ ^ 2 ≤ 1 / 16 := by
      have := sq_abs θ ▸ (pow_le_pow_left₀ (abs_nonneg θ) hθb 2)
      nlinarith
    nlinarith
  rw [Real.cot_eq_cos_div_sin, Real.cos_sub, Real.sin_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four, hz2, Real.cos_two_mul, Real.sin_two_mul]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hden : Real.sqrt 2 / 2 * Real.cos θ - Real.sqrt 2 / 2 * Real.sin θ ≠ 0 := by
    have : Real.sqrt 2 / 2 * Real.cos θ - Real.sqrt 2 / 2 * Real.sin θ =
      Real.sqrt 2 / 2 * (Real.cos θ - Real.sin θ) := by ring
    rw [this]; positivity
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  have hsc := Real.sin_sq_add_cos_sq θ
  linear_combination (Real.sqrt 2 * Real.cos θ) * hsc

lemma eulerG_mul_pow (k : ℕ) (z : ℝ) :
    eulerG k * z ^ k = 1 / π * ((z / (2 * π)) ^ k * (4 ^ (k + 1) + cotPairSum k)) := by
  rw [eulerG, div_pow, inv_pow]; ring

/-- The analytic expansion of `cot (π/4 - z/2)`. -/
lemma hasSum_eulerG (z : ℝ) (hz : |z| ≤ 1 / 2) :
    HasSum (fun k : ℕ => eulerG k * z ^ k) (Real.cot (π / 4 - z / 2)) := by
  set y := z / (2 * π) with hy
  have hpi : 0 < π := Real.pi_pos
  have hyb : |y| ≤ 1 / 12 := by
    rw [hy, abs_div, abs_of_pos (by positivity : 0 < 2 * π)]
    rw [div_le_iff₀ (by positivity)]
    have := Real.pi_gt_three
    nlinarith
  have h := (hasSum_pi_cot y hyb).mul_left (1 / π)
  have harg : π * (1 / 4 - y) = π / 4 - z / 2 := by
    rw [hy]; field_simp
  rw [harg] at h
  convert h using 1
  · funext k
    rw [eulerG_mul_pow, hy]
  · field_simp

/-- Absolute summability of the analytic expansion. -/
lemma summable_abs_eulerG (z : ℝ) (hz : |z| ≤ 1 / 2) :
    Summable (fun k : ℕ => ‖eulerG k * z ^ k‖) := by
  set y := z / (2 * π) with hy
  have hpi : 0 < π := Real.pi_pos
  have hyb : |y| ≤ 1 / 12 := by
    rw [hy, abs_div, abs_of_pos (by positivity : 0 < 2 * π)]
    rw [div_le_iff₀ (by positivity)]
    have := Real.pi_gt_three
    nlinarith
  -- |eulerG k z^k| ≤ (1/π) (4 |4 y|^k + ∑ₙ |τ(n,k)|)
  have hτ := summable_cotTau y hyb
  have hτabs : Summable (fun p => |cotTau y p|) := hτ.abs
  have hfib : Summable (fun k : ℕ => ∑' n, |cotTau y (n, k)|) := by
    have := ((Equiv.prodComm ℕ ℕ).summable_iff.mpr hτabs)
    have h2 := this.prod
    simpa [Function.comp] using h2
  have hgeo : Summable (fun k : ℕ => 4 * (4 * |y|) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left 4
  refine Summable.of_norm_bounded ((hgeo.add hfib).mul_left (1 / π)) (fun k => ?_)
  rw [norm_norm, Real.norm_eq_abs]
  have hk : eulerG k * z ^ k = (1 / π) * (y ^ k * 4 ^ (k + 1) + y ^ k * cotPairSum k) := by
    rw [eulerG_mul_pow, hy]; ring
  rw [hk, abs_mul, abs_of_pos (by positivity : 0 < 1 / π)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_pow, abs_pow, mul_pow]; norm_num; ring_nf; rfl
  · have hsk : Summable (fun n => cotTau y (n, k)) := by
      have h2 := ((Equiv.prodComm ℕ ℕ).summable_iff.mpr hτ).prod_factor k
      simpa [Function.comp] using h2
    have : y ^ k * cotPairSum k = ∑' n, cotTau y (n, k) := by
      rw [cotPairSum, ← tsum_mul_left]; rfl
    rw [this]
    have := norm_tsum_le_tsum_norm (f := fun n => cotTau y (n, k)) (by simpa using hsk.abs)
    simpa using this

end RealRooted.CenteredEulerian
