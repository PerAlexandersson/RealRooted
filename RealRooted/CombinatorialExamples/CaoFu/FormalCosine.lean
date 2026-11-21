/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.FormalSine
public import RealRooted.CombinatorialExamples.CaoFu.Chebyshev
import Mathlib.Tactic

/-!
# The formal Chebyshev identity for the Cao--Fu determinant

We prove the power-series form of the cosine identity in Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2. Formal differential equations give addition
formulas, which imply the same recurrence as the determinant polynomial.
-/

public section
noncomputable section
open PowerSeries RealRooted.CenteredEulerian
namespace RealRooted.CaoFu

private theorem derivative_rescale (a : ℝ) (F : ℝ⟦X⟧) :
    derivative (rescale a F) = C a * rescale a (derivative F) := by
  ext n
  rw [coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative, pow_succ]
  ring

private abbrev cs (a : ℝ) := rescale a cosS
private abbrev ss (a : ℝ) := rescale a sinS

private theorem derivative_cs (a : ℝ) : derivative (cs a) = -C a * ss a := by
  rw [derivative_rescale, derivative_cosS, map_neg]
  ring

private theorem derivative_ss (a : ℝ) : derivative (ss a) = C a * cs a := by
  rw [derivative_rescale, derivative_sinS]

private theorem constantCoeff_cs (a : ℝ) : constantCoeff (cs a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_cosS]
  simp

private theorem constantCoeff_ss (a : ℝ) : constantCoeff (ss a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_sinS]
  simp

/-- Differentiation of the formal cosine after a scalar change of variable. -/
theorem derivative_rescale_cosS (a : ℝ) :
    derivative (rescale a cosS) = -C a * rescale a sinS := derivative_cs a

private theorem trig_ode_unique (a : ℝ) (U V F G : ℝ⟦X⟧)
    (hU : derivative U = -C a * V) (hV : derivative V = C a * U)
    (hF : derivative F = -C a * G) (hG : derivative G = C a * F)
    (h0 : coeff 0 U = coeff 0 F) (h1 : coeff 0 V = coeff 0 G) : U = F ∧ V = G := by
  have hcoeff (n : ℕ) : coeff n U = coeff n F ∧ coeff n V = coeff n G := by
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      have hu := congrArg (coeff n) hU
      have hv := congrArg (coeff n) hV
      have hf := congrArg (coeff n) hF
      have hg := congrArg (coeff n) hG
      simp only [coeff_derivative, neg_mul, map_neg, coeff_C_mul] at hu hv hf hg
      rw [ih.2] at hu
      rw [ih.1] at hv
      constructor <;> nlinarith [show (0 : ℝ) < n + 1 by positivity]
  exact ⟨PowerSeries.ext (fun n => (hcoeff n).1), PowerSeries.ext (fun n => (hcoeff n).2)⟩

/-- Addition of the arguments in the formal cosine series. -/
private theorem rescale_cosS_add (a b : ℝ) :
    cs (a + b) = cs a * cs b - ss a * ss b := by
  have hC : derivative (cs a * cs b - ss a * ss b) =
      -C (a + b) * (ss a * cs b + cs a * ss b) := by
    simp only [map_sub, derivative.leibniz, derivative_cs, derivative_ss, smul_eq_mul, map_add]
    ring
  have hS : derivative (ss a * cs b + cs a * ss b) =
      C (a + b) * (cs a * cs b - ss a * ss b) := by
    simp only [map_add, derivative.leibniz, derivative_cs, derivative_ss, smul_eq_mul]
    ring
  exact (trig_ode_unique (a + b) _ _ _ _ (derivative_cs _) (derivative_ss _) hC hS
    (by simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_cs, constantCoeff_ss,
      constantCoeff_cosS])
    (by simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_cs, constantCoeff_ss,
      constantCoeff_sinS])).1

private theorem cs_neg (a : ℝ) : cs (-a) = cs a := by
  ext n
  rw [coeff_rescale, coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_pow]
  · rw [isEvenPS_cosS.coeff_odd hn]
    ring

private theorem ss_neg (a : ℝ) : ss (-a) = -ss a := by
  ext n
  rw [coeff_rescale, map_neg, coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [isOddPS_sinS.coeff_even hn]
    ring
  · rw [hn.neg_pow]
    ring

private theorem cs_add_cs_sub (a b : ℝ) :
    cs (a + b) + cs (a - b) = 2 * cs a * cs b := by
  rw [sub_eq_add_neg, rescale_cosS_add, rescale_cosS_add, cs_neg, ss_neg]
  ring

private theorem cs_two : cs 2 = 1 - 2 * sinS ^ 2 := by
  have h := rescale_cosS_add 1 1
  norm_num only [cs, ss, one_add_one_eq_two, rescale_one, RingHom.id_apply] at h
  change rescale 2 cosS = _
  rw [h]
  linear_combination sinS_sq_add_cosS_sq

/-- The determinant's real cosine identity also holds in formal power series. -/
theorem traceDenominator_eval_sinS_sq_mul_cosS (N : ℕ) :
    (traceDenominator N).eval₂ PowerSeries.C (4 * sinS ^ 2) * cosS =
      rescale (2 * (N : ℝ) + 1) cosS := by
  induction N using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [traceDenominator_one]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X, Nat.cast_one]
    norm_num only [mul_one, show (2 : ℝ) + 1 = 3 by norm_num]
    have h := cs_add_cs_sub 1 2
    norm_num only [show (1 : ℝ) + 2 = 3 by norm_num,
      show (1 : ℝ) - 2 = -1 by norm_num] at h
    rw [cs_neg, show cs 1 = cosS by simp [cs], cs_two] at h
    linear_combination -h
  | more n ih0 ih1 =>
    rw [traceDenominator_add_two, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X, sub_mul, mul_assoc,
      ih1, ih0]
    have h := cs_add_cs_sub (2 * (n + 1 : ℕ) + 1) 2
    have ha : (2 * (n + 1 : ℕ) + 1 : ℝ) + 2 = 2 * (n + 2 : ℕ) + 1 := by
      push_cast; ring
    have hb : (2 * (n + 1 : ℕ) + 1 : ℝ) - 2 = 2 * (n : ℝ) + 1 := by
      push_cast; ring
    rw [ha, hb, cs_two] at h
    norm_num only [map_ofNat]
    linear_combination -h

end RealRooted.CaoFu
