/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The finite Laguerre Laplace kernel

The repository normalization is `generalizedLaguerre k m = k! L_k^(m)(-X)`.
Consequently evaluation at `-x*t` already supplies the factorial in Zhang's
Laguerre integral formula. The finite coefficient identities below avoid
endpoint assumptions from repeated improper integration by parts.
-/

public section

open Finset MeasureTheory Set

namespace Polynomial

/-- Factorial moments turn the generalized Laguerre coefficient sum into
a binomial power. No sign or positivity hypothesis on the evaluation is needed. -/
theorem sum_generalizedLaguerre_laplace_coefficients (k m : ℕ)
    {y : ℝ} (hy : y ≠ 0) (z : ℝ) :
    (∑ j ∈ range (k + 1),
      (k.choose j : ℝ) * (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) *
        z ^ j * ((m + j).factorial : ℝ) / y ^ (m + j + 1)) =
      ((k + m).factorial : ℝ) * (y + z) ^ k / y ^ (k + m + 1) := by
  have hterm (j : ℕ) (hj : j ∈ range (k + 1)) :
      (k.choose j : ℝ) * (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) *
          z ^ j * ((m + j).factorial : ℝ) / y ^ (m + j + 1) =
        (((k + m).factorial : ℝ) / y ^ (m + 1)) *
          ((z / y) ^ j * (k.choose j : ℝ)) := by
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hf : (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) *
        ((m + j).factorial : ℝ) = ((k + m).factorial : ℝ) := by
      calc
        _ = ((m + j).factorial : ℝ) *
            (ascPochhammer ℝ (k - j)).eval (((m + j : ℕ) : ℝ) + 1) := by
              simp only [Nat.cast_add]
              ring
        _ = ((m + j + (k - j)).factorial : ℝ) :=
          factorial_mul_ascPochhammer ℝ (m + j) (k - j)
        _ = _ := by rw [show m + j + (k - j) = k + m by lia]
    calc
      _ = ((ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) *
          ((m + j).factorial : ℝ)) * (k.choose j : ℝ) * z ^ j /
          y ^ (m + j + 1) := by ring
      _ = _ := by
        rw [hf, show m + j + 1 = m + 1 + j by lia, pow_add, div_pow]
        field_simp [hy]
  rw [sum_congr rfl hterm, ← mul_sum]
  have hbinom := add_pow (z / y) (1 : ℝ) k
  simp only [one_pow, mul_one] at hbinom
  rw [← hbinom]
  have hbase : z / y + 1 = (y + z) / y := by field_simp; ring
  rw [hbase, div_pow, show k + m + 1 = m + 1 + k by lia, pow_add]
  field_simp [hy]
  simp only [pow_add, pow_succ]
  ring

/-- Expanding the Laguerre kernel reduces its integral to finitely many
ordinary Laplace moments. This statement requires no spectral representation. -/
theorem integrableOn_and_integral_exp_mul_pow_mul_eval_generalizedLaguerre
    (H : ℝ → ℝ) (k m : ℕ) (x : ℝ)
    (hint : ∀ j ≤ k, IntegrableOn
      (fun t : ℝ ↦ Real.exp (-x * t) * t ^ (m + j) * H t) (Ioi 0)) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * H t *
        (generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * H t *
        (generalizedLaguerre k (m : ℝ)).eval (-x * t)) =
          ∑ j ∈ range (k + 1),
            ((k.choose j : ℝ) *
              (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) * (-x) ^ j) *
                ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ (m + j) * H t := by
  let c : ℕ → ℝ := fun j ↦ (k.choose j : ℝ) *
    (ascPochhammer ℝ (k - j)).eval ((m : ℝ) + j + 1) * (-x) ^ j
  let F : ℕ → ℝ → ℝ := fun j t ↦ c j * (Real.exp (-x * t) * t ^ (m + j) * H t)
  have hF (j : ℕ) (hj : j ∈ range (k + 1)) : IntegrableOn (F j) (Ioi 0) :=
    (hint j (Nat.lt_succ_iff.mp (mem_range.mp hj))).const_mul (c j)
  have hfun : (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * H t *
      (generalizedLaguerre k (m : ℝ)).eval (-x * t)) =
        (fun t : ℝ ↦ ∑ j ∈ range (k + 1), F j t) := by
    funext t
    simp only [generalizedLaguerre, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    dsimp only [F, c]
    rw [mul_pow, pow_add]
    ring
  rw [hfun]
  refine ⟨integrable_finsetSum _ hF, ?_⟩
  rw [integral_finsetSum _ hF]
  apply sum_congr rfl
  intro j _
  exact integral_const_mul _ _

end Polynomial
