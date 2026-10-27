/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.EulerAnalytic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import RealRooted.CenteredEulerian.SeriesBasic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Positivity.Finset

/-!
# The Euler numbers: exact formula and estimates

We identify the formal coefficients `eulerCoeff k` of `sec + tan` with the analytic coefficients
`eulerG k`, and derive the estimate `|b_k - π²/4| ≤ (π²/4) S_{k+1}` for the Euler ratios
`b_k = e_k / e_{k+2}`.
Adapted from Aristotle's centered-disk proof, `RequestProject/EulerFormula.lean`
(2026-10-23).
-/

@[expose] public section

open PowerSeries Real Filter Topology

namespace RealRooted.CenteredEulerian

/-- Uniqueness of power series coefficients. -/
lemma powerSeries_coeff_eq_zero (d : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hs : Summable (fun k => |d k| * r ^ k))
    (h : ∀ z, 0 < z → z ≤ r → HasSum (fun k => d k * z ^ k) 0) : ∀ k, d k = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  -- shifted summability
  have hs' : Summable (fun k => |d (k + 1 + m)| * r ^ (k + 1)) := by
    have := (summable_nat_add_iff (1 + m)).mpr hs
    have h2 := this.mul_left ((r ^ m)⁻¹)
    convert h2 using 1
    funext k
    rw [show k + (1 + m) = k + 1 + m by ring, pow_add r (k + 1) m]
    field_simp
  set C := ∑' k, |d (k + 1 + m)| * r ^ (k + 1) with hC
  have hC0 : 0 ≤ C := tsum_nonneg (fun k => by positivity)
  have key : ∀ z, 0 < z → z ≤ r → |d m| ≤ z * (C / r) := by
    intro z hz hzr
    have h1 := h z hz hzr
    have hzero : ∑ i ∈ Finset.range m, d i * z ^ i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [ih i (Finset.mem_range.mp hi)]; ring)
    rw [← hasSum_nat_add_iff' m, hzero, sub_zero] at h1
    have h2 : HasSum (fun k => d (k + m) * z ^ k) 0 := by
      have := h1.mul_left ((z ^ m)⁻¹)
      simp only [mul_zero] at this
      convert this using 1
      funext k
      rw [pow_add]; field_simp
    rw [← hasSum_nat_add_iff' 1] at h2
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, zero_add,
      zero_sub] at h2
    have h3 : |d m| = |∑' k, d (k + 1 + m) * z ^ (k + 1)| := by
      rw [h2.tsum_eq, abs_neg]
    rw [h3]
    have hsz : Summable (fun k => |d (k + 1 + m)| * z ^ (k + 1)) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs'
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.le hzr _) (abs_nonneg _)
    calc |∑' k, d (k + 1 + m) * z ^ (k + 1)|
        ≤ ∑' k, |d (k + 1 + m) * z ^ (k + 1)| := by
          have := norm_tsum_le_tsum_norm (f := fun k => d (k + 1 + m) * z ^ (k + 1))
            (by simpa [abs_mul, abs_pow, abs_of_pos hz] using hsz)
          simpa using this
      _ = ∑' k, |d (k + 1 + m)| * z ^ (k + 1) := by
          congr 1; funext k; rw [abs_mul, abs_pow, abs_of_pos hz]
      _ ≤ ∑' k, (z / r) * (|d (k + 1 + m)| * r ^ (k + 1)) := by
          refine hsz.tsum_le_tsum (fun k => ?_) (hs'.mul_left _)
          have : z ^ (k + 1) ≤ (z / r) * r ^ (k + 1) := by
            rw [pow_succ, pow_succ]
            have : z ^ k ≤ r ^ k := pow_le_pow_left₀ hz.le hzr _
            have e : (z / r) * (r ^ k * r) = r ^ k * z := by field_simp
            rw [e]; nlinarith
          nlinarith [abs_nonneg (d (k + 1 + m))]
      _ = z * (C / r) := by rw [tsum_mul_left, hC]; ring
  have hK : 0 ≤ C / r := div_nonneg hC0 hr.le
  have : |d m| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    set z := min r (ε / (C / r + 1)) with hz
    have hz0 : 0 < z := lt_min hr (by positivity)
    have hzr : z ≤ r := min_le_left _ _
    have hzε : z ≤ ε / (C / r + 1) := min_le_right _ _
    have := key z hz0 hzr
    have : z * (C / r) ≤ ε := by
      calc z * (C / r) ≤ ε / (C / r + 1) * (C / r) := mul_le_mul_of_nonneg_right hzε hK
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
    linarith
  exact abs_nonpos_iff.mp this

/-- `1 + sin` as a power series evaluated at a real point. -/
lemma hasSum_coeff_one_add_sinS (z : ℝ) :
    HasSum (fun n => coeff n (1 + sinS) * z ^ n) (1 + Real.sin z) := by
  have h1 : HasSum (fun n => coeff n (1 : ℝ⟦X⟧) * z ^ n) 1 := by
    have := hasSum_ite_eq 0 (1 : ℝ)
    convert this using 1
    funext n
    rw [coeff_one]
    split_ifs <;> simp_all
  convert h1.add (hasSum_coeff_sinS z) using 1
  funext n; rw [map_add, add_mul]

lemma abs_coeff_one_add_sinS_le (n : ℕ) : |coeff n (1 + sinS)| ≤ 2 / (n.factorial : ℝ) := by
  rw [map_add, coeff_one]
  have h := abs_coeff_sinS_le n
  have hf : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  split_ifs with hn
  · subst hn
    rw [coeff_sinS]; simp
  · rw [zero_add]
    refine h.trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]; norm_num

lemma summable_inv_factorial_mul_pow (r : ℝ) :
    Summable (fun n : ℕ => 2 / (n.factorial : ℝ) * |r| ^ n) := by
  have := (Real.summable_pow_div_factorial |r|).mul_left 2
  convert this using 1
  funext n; ring

/-- The formal coefficients of `sec + tan` agree with the analytic ones. -/
theorem eulerCoeff_eq_eulerG (k : ℕ) : eulerCoeff k = eulerG k := by
  -- Cauchy product identity on `(0, 1/2]`
  set ser : ℕ → ℝ := fun n => ∑ kl ∈ Finset.antidiagonal n, eulerG kl.1 * coeff kl.2 cosS
    with hser
  have hprod : ∀ z : ℝ, |z| ≤ 1 / 2 →
      HasSum (fun n => ser n * z ^ n) (1 + Real.sin z) ∧
      Summable (fun n => ‖ser n * z ^ n‖) := by
    intro z hz
    have hf := summable_abs_eulerG z hz
    have hg : Summable (fun n => ‖coeff n cosS * z ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
        (Real.summable_pow_div_factorial |z|)
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have := abs_coeff_cosS_le n
      calc |coeff n cosS| * |z| ^ n ≤ 1 / (n.factorial : ℝ) * |z| ^ n :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = |z| ^ n / n.factorial := by ring
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
    have hsn := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
    have hterm : ∀ n, ∑ kl ∈ Finset.antidiagonal n, eulerG kl.1 * z ^ kl.1 *
        (coeff kl.2 cosS * z ^ kl.2) = ser n * z ^ n := by
      intro n
      rw [hser, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [← hkl, pow_add]; ring
    simp_rw [hterm] at heq hsn
    refine ⟨?_, hsn⟩
    rw [(hasSum_eulerG z hz).tsum_eq, (hasSum_coeff_cosS z).tsum_eq,
      cot_quarter_mul_cos z hz] at heq
    rw [heq]
    exact (Summable.of_norm hsn).hasSum
  -- uniqueness
  have hd : ∀ n, ser n - coeff n (1 + sinS) = 0 := by
    apply powerSeries_coeff_eq_zero _ (1 / 2) (by norm_num)
    · have h1 := (hprod (1 / 2) (by rw [abs_of_pos (by norm_num)])).2
      have h2 := summable_inv_factorial_mul_pow (1 / 2)
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h1.add h2)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := abs_coeff_one_add_sinS_le n
      have e := abs_sub (ser n) (coeff n (1 + sinS))
      have hp : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      nlinarith
    · intro z hz hzr
      have h1 := (hprod z (by rw [abs_of_pos hz]; exact hzr)).1
      have h2 := hasSum_coeff_one_add_sinS z
      have := h1.sub h2
      rw [sub_self] at this
      convert this using 1
      funext n; ring
  have hmul : (PowerSeries.mk eulerG) * cosS = eulerS * cosS := by
    rw [eulerS_mul_cosS]
    ext n
    rw [coeff_mul]
    have := hd n
    rw [hser] at this
    simp only [coeff_mk]
    linarith
  have hcos : cosS ≠ 0 := by
    intro h0
    have := constantCoeff_cosS
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have := mul_right_cancel₀ hcos hmul
  rw [eulerCoeff, ← this, coeff_mk]

/-! ### The alternating and absolute sums `T_s`, `S_s` over odd `m ≥ 3` -/

/-- `t_m^s` for `m = 2t+3`, with `t_m = (-1)^((m-1)/2)/m`. -/
noncomputable def tSeq (s t : ℕ) : ℝ := ((-1 : ℝ) ^ (t + 1) / (2 * t + 3)) ^ s
/-- `|t_m|^s` for `m = 2t+3`. -/
noncomputable def sSeq (s t : ℕ) : ℝ := (1 / (2 * (t : ℝ) + 3)) ^ s
/-- `T_s = ∑_{m ≥ 3 odd} t_m^s`. -/
noncomputable def Tsum (s : ℕ) : ℝ := ∑' t, tSeq s t
/-- `S_s = ∑_{m ≥ 3 odd} m^{-s}`. -/
noncomputable def Ssum (s : ℕ) : ℝ := ∑' t, sSeq s t

lemma abs_tSeq (s t : ℕ) : |tSeq s t| = sSeq s t := by
  rw [tSeq, sSeq, abs_pow, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * t + 3)]

lemma sSeq_nonneg (s t : ℕ) : 0 ≤ sSeq s t := by rw [sSeq]; positivity

lemma summable_sSeq {s : ℕ} (hs : 2 ≤ s) : Summable (sSeq s) := by
  have h1 : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (one_lt_two))
    simpa using this
  refine Summable.of_nonneg_of_le (sSeq_nonneg s) (fun t => ?_) h1
  rw [sSeq]
  have h0 : 1 / (2 * (t : ℝ) + 3) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  calc (1 / (2 * (t : ℝ) + 3)) ^ s ≤ (1 / (2 * (t : ℝ) + 3)) ^ 2 :=
        pow_le_pow_of_le_one (by positivity) h0 hs
    _ ≤ 1 / ((t : ℝ) + 1) ^ 2 := by
        rw [div_pow, one_pow]
        apply one_div_le_one_div_of_le (by positivity)
        have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
        nlinarith

lemma summable_tSeq {s : ℕ} (hs : 2 ≤ s) : Summable (tSeq s) :=
  Summable.of_norm_bounded (summable_sSeq hs) (fun t => by
    rw [Real.norm_eq_abs, abs_tSeq])

lemma Ssum_nonneg (s : ℕ) : 0 ≤ Ssum s := tsum_nonneg (sSeq_nonneg s)

lemma abs_Tsum_le {s : ℕ} (hs : 2 ≤ s) : |Tsum s| ≤ Ssum s := by
  have := norm_tsum_le_tsum_norm (f := tSeq s) (by
    simpa [Real.norm_eq_abs, abs_tSeq] using summable_sSeq hs)
  simpa [Tsum, Ssum, Real.norm_eq_abs, abs_tSeq] using this

lemma Ssum_three_le : Ssum 3 ≤ 29 / 540 := by
  apply Real.tsum_le_of_sum_range_le (sSeq_nonneg 3)
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), sSeq 3 i ≤
      29 / 540 - 1 / 4 * (1 / ((2 * (N : ℝ) + 3) * (2 * N + 5))) := by
    intro N
    induction N with
    | zero => simp [sSeq]; norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hterm : sSeq 3 (N + 1) ≤ 1 / 4 * (1 / ((2 * (N : ℝ) + 3) * (2 * N + 5))) -
          1 / 4 * (1 / ((2 * ((N + 1 : ℕ) : ℝ) + 3) * (2 * ((N + 1 : ℕ) : ℝ) + 5))) := by
        rw [sSeq]
        push_cast
        rw [div_pow, one_pow]
        rw [show 1 / 4 * (1 / ((2 * (N : ℝ) + 3) * (2 * N + 5))) -
          1 / 4 * (1 / ((2 * ((N : ℝ) + 1) + 3) * (2 * ((N : ℝ) + 1) + 5))) =
          1 / ((2 * (N : ℝ) + 3) * (2 * N + 5) * (2 * N + 7)) by field_simp; ring]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith
  intro N
  rcases N with _ | N
  · norm_num
  · have := key N
    have : (0 : ℝ) ≤ 1 / 4 * (1 / ((2 * (N : ℝ) + 3) * (2 * N + 5))) := by positivity
    linarith

lemma sSeq_shift_le (k t : ℕ) : sSeq (k + 3) t ≤ (1 / 3) ^ k * sSeq 3 t := by
  rw [sSeq, sSeq, pow_add]
  have h0 : 1 / (2 * (t : ℝ) + 3) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have := pow_le_pow_left₀ (by positivity) h0 k
  have h3 : (0 : ℝ) ≤ (1 / (2 * (t : ℝ) + 3)) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_right this h3

lemma Ssum_shift_le (k : ℕ) : Ssum (k + 3) ≤ (1 / 3) ^ k * Ssum 3 := by
  rw [Ssum, Ssum, ← tsum_mul_left]
  exact (summable_sSeq (by lia)).tsum_le_tsum (sSeq_shift_le k)
    ((summable_sSeq (s := 3) (by norm_num)).mul_left _)

lemma Ssum_le_of_three_le {s : ℕ} (hs : 3 ≤ s) : Ssum s ≤ 29 / 540 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by lia⟩
  have h1 := Ssum_shift_le k
  have h2 : (1 / 3 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have := Ssum_three_le
  have := Ssum_nonneg 3
  nlinarith

lemma abs_Tsum_sub_le {s : ℕ} (hs : 2 ≤ s) :
    |Tsum s - Tsum (s + 2)| ≤ Ssum s - Ssum (s + 2) := by
  have h1 := summable_tSeq hs
  have h2 := summable_tSeq (s := s + 2) (by lia)
  have h3 := summable_sSeq hs
  have h4 := summable_sSeq (s := s + 2) (by lia)
  rw [Tsum, Tsum, Ssum, Ssum, ← h1.tsum_sub h2, ← h3.tsum_sub h4]
  have hterm : ∀ t, |tSeq s t - tSeq (s + 2) t| = sSeq s t - sSeq (s + 2) t := by
    intro t
    have e1 : tSeq (s + 2) t = tSeq s t * (1 / (2 * (t : ℝ) + 3)) ^ 2 := by
      rw [tSeq, tSeq, pow_add]
      congr 1
      rw [div_pow, div_pow, ← pow_mul, show (t + 1) * 2 = 2 * (t + 1) by ring, pow_mul]
      norm_num
    have e2 : sSeq (s + 2) t = sSeq s t * (1 / (2 * (t : ℝ) + 3)) ^ 2 := by
      rw [sSeq, sSeq, pow_add]
    rw [e1, e2, show tSeq s t - tSeq s t * (1 / (2 * (t : ℝ) + 3)) ^ 2 =
      tSeq s t * (1 - (1 / (2 * (t : ℝ) + 3)) ^ 2) by ring, abs_mul, abs_tSeq]
    have : (1 / (2 * (t : ℝ) + 3)) ^ 2 ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    rw [abs_of_nonneg (by linarith)]
    ring
  have := norm_tsum_le_tsum_norm (f := fun t => tSeq s t - tSeq (s + 2) t) (by
    simp only [Real.norm_eq_abs, hterm]; exact h3.sub h4)
  simp only [Real.norm_eq_abs, hterm] at this
  exact this

/-! ### The exact formula -/

lemma cotPairSum_eq {k : ℕ} (hk : 1 ≤ k) : cotPairSum k = 4 ^ (k + 1) * Tsum (k + 1) := by
  have hs : 2 ≤ k + 1 := by lia
  have hsum := summable_tSeq hs
  have he := (hsum.comp_injective (fun a b h => by simpa using h :
    Function.Injective (fun n : ℕ => 2 * n))).hasSum
  have ho := (hsum.comp_injective (fun a b h => by simpa using h :
    Function.Injective (fun n : ℕ => 2 * n + 1))).hasSum
  have hT := (he.even_add_odd ho).tsum_eq
  rw [Tsum, hT, cotPairSum, ← (he.add ho).tsum_eq, ← tsum_mul_left]
  congr 1
  funext n
  simp only [Function.comp, tSeq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : (1 / 4 - ((n : ℝ) + 1))⁻¹ =
      4 * ((-1 : ℝ) ^ (2 * n + 1) / (2 * ((2 * n : ℕ) : ℝ) + 3)) := by
    rw [Odd.neg_one_pow ⟨n, rfl⟩]; push_cast
    rw [show (1 / 4 - ((n : ℝ) + 1)) = -(4 * n + 3) / 4 by ring, inv_div]
    field_simp
    ring
  have e2 : (1 / 4 + ((n : ℝ) + 1))⁻¹ =
      4 * ((-1 : ℝ) ^ (2 * n + 1 + 1) / (2 * ((2 * n + 1 : ℕ) : ℝ) + 3)) := by
    rw [Even.neg_one_pow ⟨n + 1, by ring⟩]; push_cast
    rw [show (1 / 4 + ((n : ℝ) + 1)) = (4 * n + 5) / 4 by ring, inv_div]
    field_simp; ring
  rw [e1, e2, mul_pow, mul_pow, mul_add]

/-- The partial fraction formula `e_k = 2 (2/π)^(k+1) (1 + T_{k+1})` for `k ≥ 1`. -/
theorem eulerCoeff_formula {k : ℕ} (hk : 1 ≤ k) :
    eulerCoeff k = 2 * (2 / π) ^ (k + 1) * (1 + Tsum (k + 1)) := by
  rw [eulerCoeff_eq_eulerG, eulerG, cotPairSum_eq hk]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  rw [show (4 : ℝ) ^ (k + 1) = 2 ^ (k + 1) * 2 ^ (k + 1) by rw [← mul_pow]; norm_num]
  rw [div_pow, inv_pow, mul_pow]
  field_simp
  ring

/-! ### Small values -/

lemma coeff_eulerS_mul_cosS (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n, eulerCoeff kl.1 * coeff kl.2 cosS = coeff n (1 + sinS) := by
  rw [← eulerS_mul_cosS, coeff_mul]; rfl

lemma eulerCoeff_zero : eulerCoeff 0 = 1 := by
  have h := coeff_eulerS_mul_cosS 0
  simpa [coeff_cosS, coeff_sinS, constantCoeff_sinS] using h

lemma eulerCoeff_one : eulerCoeff 1 = 1 := by
  have h := coeff_eulerS_mul_cosS 1
  simp [Finset.Nat.sum_antidiagonal_succ, coeff_cosS, coeff_sinS] at h
  linarith

lemma eulerCoeff_two : eulerCoeff 2 = 1 / 2 := by
  have h := coeff_eulerS_mul_cosS 2
  simp [Finset.Nat.sum_antidiagonal_succ, coeff_cosS, coeff_sinS, eulerCoeff_zero] at h
  norm_num [Nat.factorial] at h
  linarith

lemma eulerCoeff_three : eulerCoeff 3 = 1 / 3 := by
  have h := coeff_eulerS_mul_cosS 3
  simp [Finset.Nat.sum_antidiagonal_succ, coeff_cosS, coeff_sinS, eulerCoeff_one] at h
  simp only [show ¬ Even 3 by decide, ite_false] at h
  norm_num [Nat.factorial] at h
  linarith

/-! ### Positivity and the ratio estimate -/

lemma one_add_Tsum_pos {s : ℕ} (hs : 3 ≤ s) : 0 < 1 + Tsum s := by
  have h1 := abs_Tsum_le (s := s) (by lia)
  have h2 := Ssum_le_of_three_le hs
  have := neg_abs_le (Tsum s)
  linarith

theorem eulerCoeff_pos (k : ℕ) : 0 < eulerCoeff k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [eulerCoeff_zero]; norm_num
    · rw [eulerCoeff_one]; norm_num
  · rw [eulerCoeff_formula (by lia)]
    have := one_add_Tsum_pos (s := k + 1) (by lia)
    have := Real.pi_pos
    positivity

theorem eulerCoeff_le {k : ℕ} (hk : 1 ≤ k) :
    eulerCoeff k ≤ 2 * (2 / π) ^ (k + 1) * (1 + Ssum (k + 1)) := by
  rw [eulerCoeff_formula hk]
  have h1 := abs_Tsum_le (s := k + 1) (by lia)
  have h2 := le_abs_self (Tsum (k + 1))
  have := Real.pi_pos
  have hp : 0 ≤ 2 * (2 / π) ^ (k + 1) := by positivity
  nlinarith

/-- The Euler ratios `b_k = (k+1)(k+2) E_k / E_{k+2} = e_k / e_{k+2}`. -/
noncomputable def eulerRatio (k : ℕ) : ℝ := eulerCoeff k / eulerCoeff (k + 2)

/-- The constant `a = π²/4`. -/
noncomputable def aConst : ℝ := π ^ 2 / 4

lemma eulerRatio_zero : eulerRatio 0 = 2 := by
  rw [eulerRatio, eulerCoeff_zero, eulerCoeff_two]; norm_num

lemma eulerRatio_one : eulerRatio 1 = 3 := by
  rw [eulerRatio, eulerCoeff_one, eulerCoeff_three]; norm_num

/-- The key estimate (B.4): `|b_k - a| ≤ a S_{k+1}` for `k ≥ 2`. -/
theorem abs_eulerRatio_sub_le {k : ℕ} (hk : 2 ≤ k) :
    |eulerRatio k - aConst| ≤ aConst * Ssum (k + 1) := by
  have hpi := Real.pi_pos
  have hT1 := one_add_Tsum_pos (s := k + 1) (by lia)
  have hT3 := one_add_Tsum_pos (s := k + 3) (by lia)
  have hb : eulerRatio k = aConst * ((1 + Tsum (k + 1)) / (1 + Tsum (k + 3))) := by
    rw [eulerRatio, eulerCoeff_formula (by lia), eulerCoeff_formula (by lia), aConst]
    rw [show k + 2 + 1 = (k + 1) + 2 by ring, show k + 1 + 2 = k + 3 by ring]
    simp only [div_pow]
    field_simp
    ring
  have ha : 0 < aConst := by rw [aConst]; positivity
  rw [hb, show aConst * ((1 + Tsum (k + 1)) / (1 + Tsum (k + 3))) - aConst =
    aConst * ((Tsum (k + 1) - Tsum (k + 3)) / (1 + Tsum (k + 3))) by field_simp; ring]
  rw [abs_mul, abs_of_pos ha, abs_div, abs_of_pos hT3]
  apply mul_le_mul_of_nonneg_left _ ha.le
  have hd := abs_Tsum_sub_le (s := k + 1) (by lia)
  rw [show k + 1 + 2 = k + 3 by ring] at hd
  have h3 := abs_Tsum_le (s := k + 3) (by lia)
  have hS1 := Ssum_le_of_three_le (s := k + 1) (by lia)
  have hS3 := Ssum_nonneg (k + 3)
  have hlow : 1 - Ssum (k + 3) ≤ 1 + Tsum (k + 3) := by
    have := neg_abs_le (Tsum (k + 3)); linarith
  rw [div_le_iff₀ hT3]
  have e1 := mul_le_mul_of_nonneg_left hlow (Ssum_nonneg (k + 1))
  have e2 : Ssum (k + 1) * Ssum (k + 3) ≤ Ssum (k + 3) :=
    mul_le_of_le_one_left hS3 (by linarith)
  nlinarith

end RealRooted.CenteredEulerian
