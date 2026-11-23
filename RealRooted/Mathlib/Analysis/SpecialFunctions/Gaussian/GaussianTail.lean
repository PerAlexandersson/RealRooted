/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity.Finset

/-!
# Geometric bounds for polynomially weighted Gaussian tails

A bound for the polynomial growth over one lattice step, together with the
Gaussian decay over that step, yields a quantitative convergent majorant.
-/

public section

namespace Real

/-- Every polynomially weighted Gaussian sequence on the natural lattice is summable. -/
theorem summable_nat_pow_mul_exp_neg_sq (q : ℕ) {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => (n : ℝ) ^ q * exp (-u * n ^ 2)) := by
  refine (summable_pow_mul_exp_neg_nat_mul q hu).of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_)
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
      nlinarith
  nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hsq)]

private theorem pow_mul_exp_neg_sq_step {N n q : ℕ} {u B : ℝ}
    (hN : 0 < N) (hn : N ≤ n) (hu : 0 ≤ u)
    (hB : (((N : ℝ) + 1) / N) ^ q ≤ B) :
    ((n : ℝ) + 1) ^ q * exp (-u * ((n : ℝ) + 1) ^ 2) ≤
      (B * exp (-u * (2 * N + 1))) * ((n : ℝ) ^ q * exp (-u * n ^ 2)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlinear : (n : ℝ) + 1 ≤ (((N : ℝ) + 1) / N) * n := by
    rw [div_mul_eq_mul_div₀, le_div_iff₀ hN']
    nlinarith
  have hpoly : ((n : ℝ) + 1) ^ q ≤ B * (n : ℝ) ^ q := by
    calc
      ((n : ℝ) + 1) ^ q ≤ ((((N : ℝ) + 1) / N) * n) ^ q :=
        pow_le_pow_left₀ (by positivity) hlinear q
      _ = (((N : ℝ) + 1) / N) ^ q * (n : ℝ) ^ q := mul_pow _ _ _
      _ ≤ B * (n : ℝ) ^ q := mul_le_mul_of_nonneg_right hB (by positivity)
  have hexp : exp (-u * ((n : ℝ) + 1) ^ 2) ≤
      exp (-u * n ^ 2) * exp (-u * (2 * N + 1)) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hn')]
  calc
    _ ≤ (B * (n : ℝ) ^ q) *
        (exp (-u * n ^ 2) * exp (-u * (2 * N + 1))) :=
      mul_le_mul hpoly hexp (exp_nonneg _) (le_trans (by positivity) hpoly)
    _ = _ := by ring

/-- A lattice Gaussian tail is bounded termwise by an explicit geometric sequence. -/
theorem nat_add_pow_mul_exp_neg_sq_le_geom {N q : ℕ} {u B : ℝ}
    (hN : 0 < N) (hu : 0 ≤ u) (hB : (((N : ℝ) + 1) / N) ^ q ≤ B) (k : ℕ) :
    ((N + k : ℕ) : ℝ) ^ q * exp (-u * ((N + k : ℕ) : ℝ) ^ 2) ≤
      (B * exp (-u * (2 * N + 1))) ^ k * ((N : ℝ) ^ q * exp (-u * N ^ 2)) := by
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ (((N : ℝ) + 1) / N) ^ q).trans hB
  have h := le_geom (u := fun k : ℕ =>
    ((N + k : ℕ) : ℝ) ^ q * exp (-u * ((N + k : ℕ) : ℝ) ^ 2))
      (mul_nonneg hB0 (exp_nonneg (-u * (2 * N + 1)))) k (fun i _ => by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          pow_mul_exp_neg_sq_step hN (Nat.le_add_right N i) hu hB)
  simpa only [Nat.add_zero] using h

/-- A geometric one-step ratio below one proves summability of the Gaussian tail. -/
theorem summable_nat_add_pow_mul_exp_neg_sq_of_ratio {N q : ℕ} {u B : ℝ}
    (hN : 0 < N) (hu : 0 ≤ u) (hB : (((N : ℝ) + 1) / N) ^ q ≤ B)
    (hr : B * exp (-u * (2 * N + 1)) < 1) :
    Summable (fun k : ℕ =>
      ((N + k : ℕ) : ℝ) ^ q * exp (-u * ((N + k : ℕ) : ℝ) ^ 2)) := by
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ (((N : ℝ) + 1) / N) ^ q).trans hB
  have hs := (summable_geometric_of_lt_one (mul_nonneg hB0 (exp_nonneg _)) hr).mul_right
    ((N : ℝ) ^ q * exp (-u * N ^ 2))
  exact hs.of_nonneg_of_le (fun k => by positivity)
    (nat_add_pow_mul_exp_neg_sq_le_geom hN hu hB)

/-- Summing the geometric majorant gives an explicit bound for a Gaussian tail. -/
theorem tsum_nat_add_pow_mul_exp_neg_sq_le_of_ratio {N q : ℕ} {u B : ℝ}
    (hN : 0 < N) (hu : 0 ≤ u) (hB : (((N : ℝ) + 1) / N) ^ q ≤ B)
    (hr : B * exp (-u * (2 * N + 1)) < 1) :
    (∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ q * exp (-u * ((N + k : ℕ) : ℝ) ^ 2)) ≤
      ((N : ℝ) ^ q * exp (-u * N ^ 2)) / (1 - B * exp (-u * (2 * N + 1))) := by
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ (((N : ℝ) + 1) / N) ^ q).trans hB
  have hr0 := mul_nonneg hB0 (exp_nonneg (-u * (2 * N + 1)))
  have hs := summable_nat_add_pow_mul_exp_neg_sq_of_ratio hN hu hB hr
  calc
    _ ≤ ∑' k : ℕ, (B * exp (-u * (2 * N + 1))) ^ k *
        ((N : ℝ) ^ q * exp (-u * N ^ 2)) :=
      hs.tsum_le_tsum (nat_add_pow_mul_exp_neg_sq_le_geom hN hu hB)
        ((summable_geometric_of_lt_one hr0 hr).mul_right _)
    _ = _ := by rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr, div_eq_mul_inv]; ring

end Real
