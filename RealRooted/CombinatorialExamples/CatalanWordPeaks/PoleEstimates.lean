/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Real.Sqrt
import RealRooted.CombinatorialExamples.CatalanWordPeaks.PoleRadical
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Pole errors and logarithmic-derivative growth

Geometric majorants control the residue tails. These bounds give a positive
transition endpoint and uniform growth of the logarithmic derivative.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

public noncomputable section

open Finset
open scoped BigOperators

namespace RealRooted.CatalanWordPeaks.NearPoleSeries

local notation "S" => PowerSeries ℝ
local notation "c" => (PowerSeries.C : ℝ →+* S)
local notation "x" => (PowerSeries.X : S)
local notation "cf" => PowerSeries.coeff
local notation "β" => (5 / 4 : ℝ)

private def SmallCoeffs (P : S) : Prop :=
  ∀ k, |cf k P| ≤ 5 * β ^ k

private theorem H_coeff_le {R : S} (hr : ∀ k, |cf k R| ≤ 2 * β ^ k) :
    SmallCoeffs (H R) := by
  intro k
  have hp : (1 : ℝ) ≤ β ^ k := one_le_pow₀ (by norm_num)
  rw [coeff_H, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by norm_num)]
  have h1 : |b * cf k R| ≤ b * (2 * β ^ k) := by
    rw [abs_mul, abs_of_nonneg (by norm_num [b])]
    exact mul_le_mul_of_nonneg_left (hr k) (by norm_num [b])
  have h2 : |cf (k + 1) R| ≤ 2 * (β ^ k * β) := by simpa only [pow_succ] using hr (k+1)
  have h3 : |if k = 1 then a else 0| ≤ a := by split <;> norm_num [a, abs_of_nonneg]
  calc
    _ ≤ |b * cf k R| + |cf (k + 1) R| + |if k = 1 then a else 0| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ b * (2 * β ^ k) + 2 * (β ^ k * β) + a := add_le_add (add_le_add h1 h2) h3
    _ ≤ _ := by unfold a b; linarith only [hp]

private theorem B_coeff_le {Ri : S} (hr : ∀ k, |cf k Ri| ≤ 3 * β ^ k) :
    SmallCoeffs (B Ri) := by
  intro k
  cases k with
  | zero => norm_num
  | succ k =>
    rw [coeff_B_succ, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      div_le_iff₀ (by norm_num), pow_succ]
    have htail : |if 2 ≤ k then a * cf (k - 2) Ri else 0| ≤ a * (3 * β ^ k) := by
      split
      · rw [abs_mul, abs_of_nonneg (by norm_num [a])]
        apply mul_le_mul_of_nonneg_left _ (by norm_num [a])
        exact (hr (k-2)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (by lia)) (by norm_num))
      · simp only [abs_zero]
        exact mul_nonneg (by norm_num [a]) (by positivity)
    calc
      _ ≤ |cf k Ri| + |if 2 ≤ k then a * cf (k - 2) Ri else 0| := abs_add_le _ _
      _ ≤ 3 * β ^ k + a * (3 * β ^ k) := add_le_add (hr k) htail
      _ ≤ _ := by unfold a; linarith only [show 0 ≤ β ^ k by positivity]

private def EvalSeries (P : S) (t y : ℝ) : Prop :=
  HasSum (fun k => cf k P * t ^ k) y

private theorem coeff_mul_geo {P : S} {g : ℝ} (hg : 0 < g) (n : ℕ) :
    cf n (P * geo g) = g ^ n * ∑ k ∈ Finset.range (n + 1), cf k P * (g⁻¹) ^ k := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : g ^ (n - k) * g ^ k = g ^ n := by rw [← pow_add, Nat.sub_add_cancel hk']
  rw [coeff_geo, inv_pow, ← hpow]
  field_simp [pow_ne_zero _ hg.ne']

private theorem norm_coeff_geo_term {P : S} (hp : SmallCoeffs P) {g : ℝ} (hg : 0 < g) (k : ℕ) :
    |cf k P * (g⁻¹) ^ k| ≤ 5 * (β / g) ^ k := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hg.le) _), div_eq_mul_inv, mul_pow]
  calc
    _ ≤ (5 * β ^ k) * (g⁻¹) ^ k := mul_le_mul_of_nonneg_right (hp k) (by positivity)
    _ = _ := by ring

private theorem abs_geo_coeff {P : S} (hp : SmallCoeffs P) {g : ℝ}
    (hg : β < g) (hM : 5 / (1 - β / g) ≤ 20) (n : ℕ) :
    |cf n (P * geo g)| ≤ 20 * g ^ n := by
  have hg0 : 0 < g := lt_trans (by norm_num) hg
  let q := β / g
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q < 1 := (div_lt_one hg0).2 hg
  have hs : HasSum (fun k : ℕ => 5 * q ^ k) (5 / (1 - q)) := by
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hq₀ hq₁).mul_left (5 : ℝ)
  rw [coeff_mul_geo hg0, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ g ^ n * ∑ k ∈ Finset.range (n + 1), |cf k P * (g⁻¹) ^ k| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ g ^ n * ∑ k ∈ Finset.range (n + 1), 5 * q ^ k :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ => norm_coeff_geo_term hp hg0 k) (by positivity)
    _ ≤ g ^ n * (5 / (1 - q)) := mul_le_mul_of_nonneg_left
      ((hs.summable.sum_le_tsum _ (fun k _ => by positivity)).trans_eq hs.tsum_eq) (by positivity)
    _ ≤ _ := by rw [mul_comm 20]; exact mul_le_mul_of_nonneg_left hM (by positivity)

private theorem geo_residue_error {P : S} (hp : SmallCoeffs P) {g L : ℝ}
    (hg : β < g) (hM : 5 * β / (g - β) ≤ 15) (hL : EvalSeries P g⁻¹ L) (n : ℕ) :
    |cf n (P * geo g) - L * g ^ n| ≤ 15 * β ^ n := by
  have hg0 : 0 < g := lt_trans (by norm_num) hg
  let q := β / g
  let f := fun k : ℕ => cf k P * (g⁻¹) ^ k
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q < 1 := (div_lt_one hg0).2 hg
  have hLs : HasSum f L := hL
  have hs : HasSum (fun k : ℕ => 5 * q ^ (n+1) * q ^ k) (5 * q ^ (n+1) / (1-q)) := by
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hq₀ hq₁).mul_left (5 * q ^ (n+1))
  have hh (k : ℕ) : |f (k + (n+1))| ≤ 5 * q ^ (n+1) * q ^ k := by
    calc
      _ ≤ 5 * q ^ (k + (n+1)) := norm_coeff_geo_term hp hg0 _
      _ = _ := by rw [pow_add]; ring
  have hsum : Summable (fun k : ℕ => |f (k + (n+1))|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg (f (k + (n+1)))) hh hs.summable
  have habs : |∑' k, f (k + (n+1))| ≤ 5 * q ^ (n+1) / (1-q) := by
    have hnormSum : Summable (fun k : ℕ => ‖f (k + (n+1))‖) := by
      simpa only [Real.norm_eq_abs] using hsum
    have hnorm : |∑' k, f (k + (n+1))| ≤ ∑' k, |f (k + (n+1))| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnormSum
    apply hnorm.trans
    exact (hsum.tsum_le_tsum hh hs.summable).trans_eq hs.tsum_eq
  have hsplit := hLs.summable.sum_add_tsum_nat_add (n+1)
  rw [hLs.tsum_eq] at hsplit
  rw [coeff_mul_geo hg0, show g ^ n * (∑ k ∈ Finset.range (n+1), cf k P * (g⁻¹)^k) -
    L * g ^ n = -(g ^ n * ∑' k, f (k + (n+1))) by
      change g ^ n * (∑ k ∈ Finset.range (n+1), f k) - L * g ^ n = _
      rw [← hsplit]; ring,
    abs_neg, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ g ^ n * (5 * q ^ (n+1) / (1-q)) := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (5 * β / (g - β)) * β ^ n := by
      have hpow : g ^ n * q ^ n = β ^ n := by
        dsimp only [q]
        rw [div_pow]
        field_simp [pow_ne_zero n hg0.ne']
      have hq : 5 * q / (1-q) = 5 * β / (g-β) := by
        have hden : 1-q ≠ 0 := sub_ne_zero.mpr hq₁.ne'
        apply (div_eq_div_iff hden (sub_pos.mpr hg).ne').mpr
        dsimp only [q]
        field_simp [hg0.ne']
      rw [pow_succ]
      calc
        _ = (g ^ n * q ^ n) * (5 * q / (1 - q)) := by ring
        _ = _ := by rw [hpow, hq, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hM (by positivity)

private theorem coeff_geo_square (g : ℝ) (n : ℕ) :
    cf n ((geo g)^2) = ((n : ℝ) + 1) * g ^ n := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), g ^ n := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [coeff_geo, coeff_geo, ← pow_add, Nat.add_sub_of_le hk']
    _ = _ := by simp

private theorem abs_geo_square_coeff {P : S} (hp : SmallCoeffs P) {g : ℝ}
    (hg : β < g) (hM : 5 / (1 - β / g) ≤ 20) (n : ℕ) :
    |cf n (P * (geo g)^2)| ≤ 20 * ((n : ℝ) + 1) * g ^ n := by
  have hg0 : 0 < g := lt_trans (by norm_num) hg
  let E : S := PowerSeries.mk (fun k => 5 * β ^ k)
  have hE : SmallCoeffs E := by intro k; simp [E, abs_of_nonneg (by positivity : 0 ≤ 5 * β ^ k)]
  have hs : cf n (E * geo g) = ∑ k ∈ Finset.range (n + 1), (5 * β ^ k) * g ^ (n-k) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [E]
  have hbound := (le_abs_self (cf n (E*geo g))).trans (abs_geo_coeff hE hg hM n)
  rw [hs] at hbound
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ((n : ℝ) + 1) * ((5 * β ^ k) * g ^ (n-k)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      change |cf k P * cf (n-k) ((geo g)^2)| ≤ _
      have hpos : 0 ≤ ((((n-k : ℕ) : ℝ) + 1) * g ^ (n-k)) := by positivity
      rw [coeff_geo_square, abs_mul, abs_of_nonneg hpos]
      have hk' : ((n-k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
      calc
        _ ≤ (5 * β ^ k) * ((((n-k : ℕ) : ℝ) + 1) * g ^ (n-k)) :=
          mul_le_mul_of_nonneg_right (hp k) (by positivity)
        _ = (((n-k : ℕ) : ℝ) + 1) * ((5 * β ^ k) * g ^ (n-k)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hk']) (by positivity)
    _ = ((n : ℝ) + 1) * ∑ k ∈ Finset.range (n+1), (5 * β ^ k) * g ^ (n-k) := by rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) + 1) * (20 * g ^ n) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- The actual row value and its derivative have the stated pole errors
at the coalescence parameter. The two radical series supply only their
exact algebraic identity, scalar evaluations, and coefficient bounds. -/
private theorem row_pole_error_of_radical {R Ri : S}
    (hR0 : PowerSeries.constantCoeff R = 1) (hR : R ^ 2 = Q) (hRi : R * Ri = 1)
    (hRp : ∀ k, |cf k R| ≤ 2 * β ^ k) (hRip : ∀ k, |cf k Ri| ≤ 3 * β ^ k)
    (hHa : HasSum (fun k => cf k (H R) * (a⁻¹) ^ k) (11 / 16))
    (hBb : HasSum (fun k => cf k (B Ri) * (b⁻¹) ^ k) (4 * Real.sqrt 3 / 27))
    {n : ℕ} (hn : 150 ≤ n) :
    |(polynomial n).eval tau - (11 / 16 : ℝ) * a ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n ∧
      |(polynomial n).derivative.eval tau - (16 * Real.sqrt 3 / 27) * b ^ n| ≤
        20 * (n : ℝ) * a ^ n := by
  have hH := H_coeff_le hRp
  have hB := B_coeff_le hRip
  have hFa := geo_residue_error hH (by norm_num [a]) (by norm_num [a]) hHa n
  have hDb := geo_residue_error hB (by norm_num [b]) (by norm_num [b]) hBb n
  have hDa := abs_geo_coeff hB (g := a) (by norm_num [a]) (by norm_num [a]) n
  have ha : (1 : ℝ) ≤ a := by norm_num [a]
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hna : 0 ≤ a ^ n := by positivity
  have hβa : β ^ n ≤ a ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num [a]) _
  constructor
  · rw [← coeff_F_tau, F_tau_eq hR0 hR]
    calc
      _ ≤ 15 * β ^ n := hFa
      _ ≤ 15 * (3 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
    have hSimple : |((1 / 2 : ℝ) * cf n (x * geo a))| ≤ a ^ n := by
      rw [hk, PowerSeries.coeff_succ_X_mul, coeff_geo, abs_of_nonneg (by positivity), pow_succ]
      calc
        _ ≤ a * a ^ k := mul_le_mul_of_nonneg_right (by norm_num [a]) (by positivity)
        _ = _ := mul_comm _ _
    have hDouble : |cf n (x * (H R * (geo a)^2))| ≤ 12 * (n : ℝ) * a ^ n := by
      rw [hk, PowerSeries.coeff_succ_X_mul, pow_succ]
      have hh := abs_geo_square_coeff hH (g := a) (by norm_num [a]) (by norm_num [a]) k
      apply hh.trans
      push_cast
      calc
        _ = ((k : ℝ) + 1) * a ^ k * 20 := by ring
        _ ≤ ((k : ℝ) + 1) * a ^ k * (12 * a) :=
          mul_le_mul_of_nonneg_left (by norm_num [a]) (by positivity)
        _ = _ := by simp only [Nat.succ_eq_add_one, pow_succ]; ring
    rw [← coeff_DtF_tau, DtF_tau_eq hR0 hR hRi]
    simp only [map_add, map_sub, mul_assoc, ← map_ofNat c 4, ← map_ofNat c 3,
      PowerSeries.coeff_C_mul]
    change |((1 / 2 : ℝ) * cf n (x * geo a)) + 4 * cf n (B Ri * geo b) -
      3 * cf n (B Ri * geo a) - cf n (x * (H R * (geo a)^2)) -
      (16 * Real.sqrt 3 / 27) * b ^ n| ≤ _
    have hsum :
        ((1 / 2 : ℝ) * cf n (x * geo a)) + 4 * cf n (B Ri * geo b) -
          3 * cf n (B Ri * geo a) - cf n (x * (H R * (geo a)^2)) -
          (16 * Real.sqrt 3 / 27) * b ^ n =
        ((((1 / 2 : ℝ) * cf n (x * geo a)) +
          4 * (cf n (B Ri * geo b) - (4 * Real.sqrt 3 / 27) * b ^ n)) -
            3 * cf n (B Ri * geo a)) - cf n (x * (H R * (geo a)^2)) := by ring
    rw [hsum]
    have hb1 := mul_le_mul_of_nonneg_left hDb (show (0 : ℝ) ≤ 4 by norm_num)
    have hb2 := mul_le_mul_of_nonneg_left hDa (show (0 : ℝ) ≤ 3 by norm_num)
    have h4 (p q r s : ℝ) : |p + q - r - s| ≤ |p| + |q| + |r| + |s| :=
      (abs_sub _ _).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    apply (h4 _ _ _ _).trans
    rw [abs_mul (4 : ℝ), abs_mul (3 : ℝ), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hSimple, hb1, hb2, hDouble, hβa, hna,
      mul_nonneg (sub_nonneg.mpr hnR) hna]

/-- At the coalescence parameter the actual row and its derivative obey
the two quantitative pole estimates. -/
theorem row_pole_errors {n : ℕ} (hn : 150 ≤ n) :
    |(polynomial n).eval (-11 / 16) - (11 / 16 : ℝ) * (27 / 16 : ℝ) ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n ∧
    |(polynomial n).derivative.eval (-11 / 16) - (16 * Real.sqrt 3 / 27) * (9 / 4 : ℝ) ^ n| ≤
      20 * (n : ℝ) * (27 / 16 : ℝ) ^ n := by
  have hR : ∀ k, |PowerSeries.coeff k R| ≤ 2 * (5 / 4 : ℝ) ^ k := by
    intro k
    simpa only [Real.norm_eq_abs] using coeff_R_bound k
  have hRi : ∀ k, |PowerSeries.coeff k Ri| ≤ 3 * (5 / 4 : ℝ) ^ k := by
    intro k
    simpa only [Real.norm_eq_abs] using coeff_Ri_bound k
  have hHa : PoleHasSum (H R) a⁻¹ (11 / 16) := by
    rw [show a⁻¹ = 16 / 27 by norm_num [a]]
    exact hasSum_H_at_a
  have hBb : PoleHasSum (B Ri) b⁻¹ (4 * Real.sqrt 3 / 27) := by
    rw [show b⁻¹ = 4 / 9 by norm_num [b]]
    exact hasSum_B_at_b
  simpa only [tau, a, b] using row_pole_error_of_radical constantCoeff_R R_sq R_mul_Ri
    hR hRi hHa hBb hn

end RealRooted.CatalanWordPeaks.NearPoleSeries

namespace RealRooted.CatalanWordPeaks.RightEdge

private theorem relative_tail {n : ℕ} (hn : 150 ≤ n) :
    24 * (8 / 9 : ℝ) ^ n ≤ (11 / 16 : ℝ) / 100 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num) hn
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)

private theorem exponential_dominates {n : ℕ} (hn : 150 ≤ n) :
    1000 * (n : ℝ) ^ 3 < (4 / 3 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep : ((n : ℝ) + 1) ^ 3 ≤ (4 / 3) * (n : ℝ) ^ 3 := by
      calc
        _ ≤ ((151 / 150 : ℝ) * (n : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (151 / 150 : ℝ) ^ 3 * (n : ℝ) ^ 3 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    push_cast
    rw [pow_succ]
    calc
      _ ≤ (1000 * (n : ℝ) ^ 3) * (4 / 3) := by linarith
      _ < _ := mul_lt_mul_of_pos_right ih (by norm_num)

private theorem pole_ratio_bounds (v d : ℕ → ℝ) {K : ℝ} (hK : 1 < K) {n : ℕ}
    (hn : 150 ≤ n)
    (hv : |v n - (11 / 16 : ℝ) * (27 / 16 : ℝ) ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n)
    (hd : |d n - K * (9 / 4 : ℝ) ^ n| ≤ 20 * (n : ℝ) * (27 / 16 : ℝ) ^ n) :
    0 < v n ∧
      K * (4 / 3 : ℝ) ^ n / (1111 / 1600) - 20 * (n : ℝ) / (1089 / 1600) ≤ d n / v n ∧
      d n / v n ≤ K * (4 / 3 : ℝ) ^ n / (1089 / 1600) + 20 * (n : ℝ) / (1089 / 1600) := by
  let a : ℝ := (27 / 16) ^ n
  let P := v n / a
  let E := (d n - K * (9 / 4 : ℝ) ^ n) / a
  let L : ℝ := 1089 / 1600
  let U : ℝ := 1111 / 1600
  have ha : 0 < a := by dsimp [a]; positivity
  have herror : |P - 11 / 16| ≤ 11 / 16 / 100 := by
    have heq : P - 11 / 16 = (v n - (11 / 16) * a) / a := by
      dsimp [P]
      field_simp [ha.ne']
    rw [heq, abs_div, abs_of_pos ha]
    calc
      _ ≤ (24 * (3 / 2 : ℝ) ^ n) / a := div_le_div_of_nonneg_right hv ha.le
      _ = 24 * (8 / 9 : ℝ) ^ n := by
        dsimp only [a]
        rw [mul_div_assoc, ← div_pow]
        norm_num
      _ ≤ _ := relative_tail hn
  obtain ⟨h₁, h₂⟩ := abs_le.mp herror
  have hL : L ≤ P := by dsimp [L]; linarith
  have hU : P ≤ U := by dsimp [U]; linarith
  have hP : 0 < P := (show 0 < L by norm_num [L]).trans_le hL
  have hpos : 0 < v n := (div_pos_iff_of_pos_right ha).mp hP
  have hE : |E| ≤ 20 * (n : ℝ) := by
    dsimp only [E]
    rw [abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr hd
  obtain ⟨he₁, he₂⟩ := abs_le.mp hE
  have hlead : 0 ≤ K * (4 / 3 : ℝ) ^ n := by positivity
  have hquot : d n / v n = (K * (4 / 3 : ℝ) ^ n + E) / P := by
    have hfactor : (9 / 4 : ℝ) ^ n / a = (4 / 3 : ℝ) ^ n := by
      dsimp only [a]
      rw [← div_pow]
      norm_num
    rw [← hfactor, ← mul_div_assoc]
    dsimp only [E, P]
    rw [← add_div]
    field_simp [ha.ne', hpos.ne']
    ring
  have hminus : -(20 * (n : ℝ) / L) ≤ E / P := by
    calc
      _ = -(20 * (n : ℝ)) / L := by ring
      _ ≤ -(20 * (n : ℝ)) / P := by
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num [L]) hL
      _ ≤ _ := div_le_div_of_nonneg_right he₁ hP.le
  have hplus : E / P ≤ 20 * (n : ℝ) / L :=
    (div_le_div_of_nonneg_right he₂ hP.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by norm_num [L]) hL)
  refine ⟨hpos, ?_, ?_⟩
  · rw [hquot, add_div, sub_eq_add_neg]
    exact add_le_add (div_le_div_of_nonneg_left hlead hP hU) hminus
  · rw [hquot, add_div]
    exact add_le_add (div_le_div_of_nonneg_left hlead (by norm_num [L]) hL) hplus

/-- The coefficient estimates imply the absolute and successive logarithmic
derivative bounds required for the rightmost root. -/
theorem ratio_growth_of_poles (v d : ℕ → ℝ) {K : ℝ} (hK : 1 < K)
    (hv : ∀ n, 150 ≤ n → |v n - (11 / 16 : ℝ) * (27 / 16 : ℝ) ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n)
    (hd : ∀ n, 150 ≤ n → |d n - K * (9 / 4 : ℝ) ^ n| ≤ 20 * (n : ℝ) * (27 / 16 : ℝ) ^ n)
    {n : ℕ} (hn : 150 ≤ n) :
    0 < v n ∧ 300 * (n : ℝ) ^ 3 < d n / v n ∧
      100 * (n : ℝ) ^ 3 < d (n + 1) / v (n + 1) - d n / v n := by
  have hn' : 150 ≤ n + 1 := by lia
  obtain ⟨hpos, hlow, hhigh⟩ := pole_ratio_bounds v d hK hn (hv n hn) (hd n hn)
  obtain ⟨_, hlow', _⟩ := pole_ratio_bounds v d hK hn' (hv (n + 1) hn') (hd (n + 1) hn')
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpow : 0 < (4 / 3 : ℝ) ^ n := by positivity
  have hgrowth := exponential_dominates hn
  have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith only [hnR]
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      simpa using pow_le_pow_left₀ zero_le_one h1 2
    calc
      _ = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hn0
      _ = _ := by ring
  have hmain : (4 / 3 : ℝ) ^ n < K * (4 / 3 : ℝ) ^ n / (1111 / 1600) := by
    apply (lt_div_iff₀ (show (0 : ℝ) < 1111 / 1600 by norm_num)).mpr
    have h : (1111 / 1600 : ℝ) < K := by linarith only [hK]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right h hpow
  let c : ℝ := (4 / 3) / (1111 / 1600) - 1 / (1089 / 1600)
  have hc : (3 / 10 : ℝ) < c := by norm_num [c]
  have hcomp : (3 / 10) * (4 / 3 : ℝ) ^ n <
      K * (4 / 3 : ℝ) ^ (n + 1) / (1111 / 1600) -
        K * (4 / 3 : ℝ) ^ n / (1089 / 1600) := by
    have heq : K * (4 / 3 : ℝ) ^ (n + 1) / (1111 / 1600) -
        K * (4 / 3 : ℝ) ^ n / (1089 / 1600) = K * (4 / 3 : ℝ) ^ n * c := by
      rw [pow_succ]
      dsimp only [c]
      ring
    rw [heq]
    calc
      _ < c * (4 / 3 : ℝ) ^ n := mul_lt_mul_of_pos_right hc hpow
      _ = 1 * (4 / 3 : ℝ) ^ n * c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK.le hpow.le) (by norm_num [c])
  push_cast at hlow'
  exact ⟨hpos, by linarith only [hlow, hmain, hcube, hgrowth],
    by linarith only [hlow', hhigh, hcomp, hcube, hgrowth, hnR]⟩

/-- The transition value is positive, with the two logarithmic-derivative growth margins. -/
theorem transition_bounds {n : ℕ} (hn : 150 ≤ n) :
    0 < (polynomial n).eval (-11 / 16) ∧
      300 * (n : ℝ) ^ 3 <
        (polynomial n).derivative.eval (-11 / 16) / (polynomial n).eval (-11 / 16) ∧
      100 * (n : ℝ) ^ 3 <
        (polynomial (n + 1)).derivative.eval (-11 / 16) /
            (polynomial (n + 1)).eval (-11 / 16) -
          (polynomial n).derivative.eval (-11 / 16) / (polynomial n).eval (-11 / 16) := by
  have hS : (27 / 16 : ℝ) < Real.sqrt 3 := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hK : (1 : ℝ) < 16 * Real.sqrt 3 / 27 := by linarith
  exact ratio_growth_of_poles (fun m => (polynomial m).eval (-11 / 16))
    (fun m => (polynomial m).derivative.eval (-11 / 16)) hK
    (fun m hm => (NearPoleSeries.row_pole_errors hm).1)
    (fun m hm => (NearPoleSeries.row_pole_errors hm).2) hn

end RealRooted.CatalanWordPeaks.RightEdge
