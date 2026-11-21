/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Rational bounds for the crown centered-disk estimate

These are the elementary numerical estimates in the centered-transfer proof
of Cao--Fu, arXiv:2610.40496v1, Theorem 1.1. The analytic cosecant expansion
of Lemmas 3.1--3.2 and its tail bound are separate obligations. In particular,
this file does not assert the centered-disk estimate for crown polynomials.
-/

public section

namespace RealRooted.CaoFu

/-- The uniform squared-radius bound used in the hyperbolic sine estimate. -/
theorem pi_sq_radius_le : 3 * Real.pi ^ 2 / 52 ≤ (10 / 3 : ℝ) := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

/-- The rational lower bound on the inverse squared sine after the radius estimate. -/
theorem sine_bound_constant_le :
    (1633 / 5000 : ℝ) ≤ 4 / (Real.pi ^ 2 * (1 + 3 * Real.pi ^ 2 / 260) ^ 2) := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hp : Real.pi ^ 2 ≤ (3.1416 : ℝ) ^ 2 := by nlinarith
  have hfactor : (1 + 3 * Real.pi ^ 2 / 260) ^ 2 ≤
      (1 + 3 * (3.1416 : ℝ) ^ 2 / 260) ^ 2 := by nlinarith [sq_nonneg Real.pi]
  rw [le_div_iff₀ (by positivity)]
  have hmul := mul_le_mul hp hfactor (sq_nonneg _) (by positivity)
  norm_num at hmul ⊢
  linarith

/-- A geometric-series remainder reduces to the cubic sine estimate on this radius. -/
theorem sinh_remainder_bound {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 10 / 3) :
    1 + (u / 6) / (1 - u / 20) ≤ 1 + u / 5 := by
  have hden : 0 < 1 - u / 20 := by linarith
  rw [add_le_add_iff_left, div_le_iff₀ hden]
  nlinarith

/-- The cubic lower bound dominates the affine error on the full exterior radius. -/
theorem cubic_bound_gt {w : ℝ} (hw : 13 / 3 ≤ w) :
    3 / 2 + w / 8 < (17 / 500 : ℝ) * w ^ 3 := by
  have hshift : 0 ≤ (w - 13 / 3) ^ 2 := sq_nonneg _
  have hcube : 0 ≤ (w - 13 / 3) ^ 3 := pow_nonneg (by linarith) _
  nlinarith

/-- The rational odd-tail estimate after extracting the first term. -/
theorem odd_tail_constant_le : (1 : ℝ) + (729 / 625) * (1 / 8) ≤ 23 / 20 := by
  norm_num

/-- The inverse-square tail comparison used to telescope over odd indices. -/
theorem inv_sq_le_telescope {m : ℝ} (hm : 1 < m) :
    1 / m ^ 2 ≤ (1 / 2 : ℝ) * (1 / (m - 1) - 1 / (m + 1)) := by
  have hden : m ^ 2 > 0 := by positivity
  rw [div_le_iff₀ hden]
  have hm₁ : m - 1 ≠ 0 := by linarith
  have hm₂ : m + 1 ≠ 0 := by linarith
  field_simp
  nlinarith

/-- The final power comparison in the centered-disk bound, uniformly for all `r ≥ 3`. -/
theorem power_bound_gt {r : ℕ} (hr : 3 ≤ r) {w X : ℝ} (hw : 13 / 3 ≤ w)
    (hX : (1633 / 5000 : ℝ) * w ≤ X) :
    3 / 2 + w / 8 + (23 / 40 : ℝ) * (w / 9) ^ r < X ^ r := by
  have hw0 : 0 ≤ w := by linarith
  have hb : (1 : ℝ) ≤ (1633 / 5000) * w := by linarith
  have hpow : ((1633 / 5000 : ℝ) * w) ^ 3 ≤ ((1633 / 5000) * w) ^ r :=
    pow_le_pow_right₀ hb hr
  have hscale : (25 : ℝ) ≤ (9 * (1633 / 5000)) ^ r := by
    calc
      (25 : ℝ) ≤ (9 * (1633 / 5000)) ^ 3 := by norm_num
      _ ≤ (9 * (1633 / 5000)) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hsmall : (w / 9) ^ r ≤ ((1633 / 5000 : ℝ) * w) ^ r / 25 := by
    have hmul := mul_le_mul_of_nonneg_right hscale (pow_nonneg (by positivity : 0 ≤ w / 9) r)
    rw [← mul_pow] at hmul
    have hid : 9 * (1633 / 5000 : ℝ) * (w / 9) = (1633 / 5000 : ℝ) * w := by ring
    rw [hid] at hmul
    linarith
  have hlarge : ((1633 / 5000 : ℝ) * w) ^ r ≤ X ^ r :=
    pow_le_pow_left₀ (by positivity) hX r
  have hconst : (17 / 500 : ℝ) ≤ (1633 / 5000) ^ 3 * (1 - (23 / 40) / 25) := by
    norm_num
  have hcubic := cubic_bound_gt hw
  have hcoeff := mul_le_mul_of_nonneg_right hconst (pow_nonneg hw0 3)
  rw [mul_pow] at hpow
  nlinarith

/-- The elementary lower bound from the principal-part and tail estimates exceeds one. -/
theorem two_pow_sub_tail_gt_one {r : ℕ} (hr : 3 ≤ r) {w X : ℝ} (hw : 13 / 3 ≤ w)
    (hX : (1633 / 5000 : ℝ) * w ≤ X) :
    1 < 2 * X ^ r - 2 - (w / 4 + (23 / 20 : ℝ) * (w / 9) ^ r) := by
  have := power_bound_gt hr hw hX
  linarith

/-- A single inverse-square term is bounded by a telescoping difference. -/
private theorem odd_inv_sq_le_sub {a : ℝ} (ha : 0 < a) :
    1 / (2 * a + 1) ^ 2 ≤ 1 / (4 * a) - 1 / (4 * (a + 1)) := by
  have h := inv_sq_le_telescope (m := 2 * a + 1) (by linarith)
  calc
    _ ≤ (1 / 2 : ℝ) * (1 / ((2 * a + 1) - 1) - 1 / ((2 * a + 1) + 1)) := h
    _ = _ := by field_simp; ring

/-- A finite odd inverse-square tail, including its terminal remainder. -/
private theorem sum_odd_inv_sq_le_sub {a : ℝ} (ha : 0 < a) (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / (2 * ((n : ℝ) + a) + 1) ^ 2) ≤
      1 / (4 * a) - 1 / (4 * ((N : ℝ) + a)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := odd_inv_sq_le_sub (a := (N : ℝ) + a) (by positivity)
    push_cast
    rw [show (N : ℝ) + 1 + a = (N : ℝ) + a + 1 by ring]
    linarith

/-- Odd inverse-square tails are summable, with the elementary telescoping bound. -/
theorem summable_odd_inv_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => 1 / (2 * ((n : ℝ) + a) + 1) ^ 2) := by
  apply summable_of_sum_range_le (c := 1 / (4 * a)) (fun n => by positivity)
  intro N
  have h := sum_odd_inv_sq_le_sub ha N
  have hlast : 0 ≤ 1 / (4 * ((N : ℝ) + a)) := by positivity
  linarith

/-- The odd inverse-square tail is at most `1/(4a)`; use `a = 1` or `a = 2`. -/
theorem tsum_odd_inv_sq_le {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, 1 / (2 * ((n : ℝ) + a) + 1) ^ 2) ≤ 1 / (4 * a) := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  have h := sum_odd_inv_sq_le_sub ha N
  have hlast : 0 ≤ 1 / (4 * ((N : ℝ) + a)) := by positivity
  linarith

/-- After extracting the first odd term, all higher powers have a uniform summable bound. -/
private theorem odd_power_term_le {r : ℕ} (hr : 3 ≤ r) (n : ℕ) :
    (9 / (2 * ((n : ℝ) + 2) + 1) ^ 2) ^ r ≤
      (729 / 625 : ℝ) * (1 / (2 * ((n : ℝ) + 2) + 1) ^ 2) := by
  let m : ℝ := 2 * ((n : ℝ) + 2) + 1
  have hm : 5 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm0 : 0 < m := by linarith
  have hd : 1 / m ^ 2 ≤ (1 / 25 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hd0 : 0 ≤ 1 / m ^ 2 := by positivity
  have hb : 9 / m ^ 2 ≤ (1 : ℝ) := by
    calc
      _ = 9 * (1 / m ^ 2) := by ring
      _ ≤ 1 := by linarith
  have hcubic : (9 / m ^ 2) ^ 3 ≤ (729 / 625 : ℝ) * (1 / m ^ 2) := by
    have hs := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd0 hd 2) hd0
    calc
      _ = 729 * ((1 / m ^ 2) ^ 2 * (1 / m ^ 2)) := by ring
      _ ≤ _ := by linarith
  exact (pow_le_pow_of_le_one (by positivity) hb hr).trans hcubic

/-- The odd power tail has a summable inverse-square majorant for every `r ≥ 3`. -/
theorem summable_odd_power_tail {r : ℕ} (hr : 3 ≤ r) :
    Summable (fun n : ℕ => (9 / (2 * ((n : ℝ) + 2) + 1) ^ 2) ^ r) :=
  Summable.of_nonneg_of_le (fun n => by positivity) (odd_power_term_le hr)
    ((summable_odd_inv_sq (a := 2) (by norm_num)).mul_left (729 / 625))

/-- The normalized odd power series is summable for every `r ≥ 3`. -/
theorem summable_odd_power {r : ℕ} (hr : 3 ≤ r) :
    Summable (fun n : ℕ => (9 / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
    summable_odd_power_tail hr

/-- The normalized odd power tail is bounded uniformly in the exponent. -/
theorem tsum_odd_power_le {r : ℕ} (hr : 3 ≤ r) :
    (∑' n : ℕ, (9 / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r) ≤ (23 / 20 : ℝ) := by
  have htail := summable_odd_power_tail hr
  have hsum := summable_odd_power hr
  rw [hsum.tsum_eq_zero_add]
  norm_num only [Nat.cast_zero, zero_add, mul_one, show (2 + 1 : ℝ) = 3 by norm_num,
    show (9 / 3 ^ 2 : ℝ) = 1 by norm_num, one_pow]
  have hle := htail.tsum_le_tsum (odd_power_term_le hr)
    ((summable_odd_inv_sq (a := 2) (by norm_num)).mul_left (729 / 625))
  rw [tsum_mul_left] at hle
  have hbound : (∑' n : ℕ, 1 / (2 * ((n : ℝ) + 2) + 1) ^ 2) ≤ 1 / 8 :=
    (tsum_odd_inv_sq_le (a := 2) (by norm_num)).trans (by norm_num)
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
  linarith

/-- The complete maximum tail in the centered-disk proof has a uniform bound. -/
theorem tsum_max_odd_le {r : ℕ} (hr : 3 ≤ r) {w : ℝ} (hw : 0 ≤ w) :
    (∑' n : ℕ, max (w / (2 * ((n : ℝ) + 1) + 1) ^ 2)
      ((w / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r)) ≤
        w / 4 + (23 / 20 : ℝ) * (w / 9) ^ r := by
  let a : ℕ → ℝ := fun n => w * (1 / (2 * ((n : ℝ) + 1) + 1) ^ 2)
  let b : ℕ → ℝ := fun n => (w / 9) ^ r * (9 / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r
  have ha : Summable a := (summable_odd_inv_sq (a := 1) (by norm_num)).mul_left w
  have hb : Summable b := (summable_odd_power hr).mul_left ((w / 9) ^ r)
  have hterm (n : ℕ) : max (w / (2 * ((n : ℝ) + 1) + 1) ^ 2)
      ((w / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r) ≤ a n + b n := by
    have hfirst : w / (2 * ((n : ℝ) + 1) + 1) ^ 2 = a n := by dsimp [a]; ring
    have hsecond : (w / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r = b n := by
      dsimp [b]
      rw [← mul_pow]
      congr 1
      ring
    rw [hsecond, hfirst]
    exact max_le (le_add_of_nonneg_right (by dsimp [b]; positivity))
      (le_add_of_nonneg_left (by dsimp [a]; positivity))
  have hsum := Summable.of_nonneg_of_le
    (fun n => le_max_of_le_left (by positivity)) hterm (ha.add hb)
  have hle := hsum.tsum_le_tsum hterm (ha.add hb)
  rw [ha.tsum_add hb] at hle
  have haeq : ∑' n, a n = w * ∑' n : ℕ, 1 / (2 * ((n : ℝ) + 1) + 1) ^ 2 := by
    dsimp [a]
    rw [tsum_mul_left]
  have hbeq : ∑' n, b n =
      (w / 9) ^ r * ∑' n : ℕ, (9 / (2 * ((n : ℝ) + 1) + 1) ^ 2) ^ r := by
    dsimp [b]
    rw [tsum_mul_left]
  rw [haeq, hbeq] at hle
  have hi : (∑' n : ℕ, 1 / (2 * ((n : ℝ) + 1) + 1) ^ 2) ≤ 1 / 4 :=
    (tsum_odd_inv_sq_le (a := 1) (by norm_num)).trans (by norm_num)
  have h₁ := mul_le_mul_of_nonneg_left hi hw
  have h₂ := mul_le_mul_of_nonneg_left (tsum_odd_power_le hr)
    (pow_nonneg (by positivity : 0 ≤ w / 9) r)
  linarith

end RealRooted.CaoFu
