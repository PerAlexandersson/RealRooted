/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.LongCutoffDominance
public import RealRooted.IntervalDifferential.CoefficientDisk
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.Factorization
import Mathlib.Tactic

/-!
# The complex root disk of a long-cutoff alphabet

Exact rational coefficient dominance is transported to the original real
alphabet polynomial, and reflection gives a strict disk of radius `5/4`.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

private theorem ratCast_coefficientNorm (r : ℚ) (p : ℚ[X]) :
    ((coefficientNorm r p : ℚ) : ℝ) =
      coefficientNorm (r : ℝ) (p.map (Rat.castHom ℝ)) := by
  simp only [coefficientNorm, sum_def,
    support_map_of_injective p (Rat.castHom ℝ).injective, coeff_map]
  push_cast
  rfl

/-- Transport rational reflected coefficient dominance to the actual alphabet. -/
theorem descentAlphabetPolynomial_coefficientNorm_lt_of_lossRow {n k : ℕ}
    (hn : 0 < n)
    (hh : coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0) :
    coefficientNorm (4 / 5 : ℝ) (reflect n (descentAlphabetPolynomial n k) -
      C ((descentAlphabetPolynomial n k).coeff n)) <
      (descentAlphabetPolynomial n k).coeff n := by
  have hc : ((coefficientNorm (4 / 5 : ℚ)
      (lossRow k n - C ((lossRow k n).coeff 0)) : ℚ) : ℝ) <
      ((lossRow k n).coeff 0 : ℝ) := by exact_mod_cast hh
  have hm : (lossRow k n).map (Rat.castHom ℝ) =
      reflect n (descentAlphabetPolynomial n k) := by
    rw [lossRow, ← reflect_map, map_alphabetRow hn]
  have h0 : ((lossRow k n).coeff 0 : ℝ) = (descentAlphabetPolynomial n k).coeff n := by
    change (Rat.castHom ℝ) ((lossRow k n).coeff 0) = _
    rw [← coeff_map, hm, coeff_reflect, revAt_zero]
  rw [ratCast_coefficientNorm] at hc
  simp only [Polynomial.map_sub, map_C, hm] at hc
  change coefficientNorm ((4 / 5 : ℚ) : ℝ)
    (reflect n (descentAlphabetPolynomial n k) - C (((lossRow k n).coeff 0 : ℚ) : ℝ)) <
      ((lossRow k n).coeff 0 : ℝ) at hc
  rw [h0] at hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  exact hc

/-- Coefficient dominance for the actual real alphabet at every cutoff at least
thirteen. -/
theorem descentAlphabetPolynomial_coefficientNorm_lt {n k : ℕ}
    (hk : 13 ≤ k) (hkn : k ≤ n) :
    coefficientNorm (4 / 5 : ℝ) (reflect n (descentAlphabetPolynomial n k) -
      C ((descentAlphabetPolynomial n k).coeff n)) <
      (descentAlphabetPolynomial n k).coeff n :=
  descentAlphabetPolynomial_coefficientNorm_lt_of_lossRow (by lia)
    (coefficientNorm_lossRow_sub_constant_lt hk hkn)

/-- Every complex zero of the actual long-cutoff alphabet is strictly inside
the disk of radius `5/4`. -/
theorem norm_root_descentAlphabetPolynomial_lt {n k : ℕ}
    (hk : 13 ≤ k) (hkn : k ≤ n) {z : ℂ}
    (hz : ((descentAlphabetPolynomial n k).map (algebraMap ℝ ℂ)).eval z = 0) :
    ‖z‖ < 5 / 4 := by
  have hd := descentAlphabetPolynomial_coefficientNorm_lt hk hkn
  have hh := norm_lt_inv_of_reflect_coefficientNorm_lt (by norm_num : (0 : ℝ) < 4 / 5)
    (natDegree_descentAlphabetPolynomial_le n k) (hd.trans_le (le_abs_self _))
    (by simpa only [eval_map] using hz)
  norm_num at hh
  exact hh

/-- The same disk bound holds for the actual alphabet quotient. -/
theorem normSq_root_alphabet_quotient_le {n k : ℕ} (hk : 13 ≤ k) (hkn : k ≤ n)
    {Q : ℝ[X]} (hf : descentAlphabetPolynomial n k = X * (X ^ 2 - 1) * Q)
    {z : ℂ} (hz : (Q.map (algebraMap ℝ ℂ)).eval z = 0) :
    Complex.normSq z ≤ 25 / 16 := by
  have hfz : ((descentAlphabetPolynomial n k).map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [hf, Polynomial.map_mul, eval_mul, hz, mul_zero]
  have hh := norm_root_descentAlphabetPolynomial_lt hk hkn hfz
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z]

/-- Strict disk control is preserved by arbitrary nonzero nonnegative mixtures
of the cutoffs at least thirteen. -/
theorem norm_root_sum_descentAlphabetPolynomial_lt_of_dominance {n : ℕ} {s : Finset ℕ}
    (hdom : ∀ k ∈ s, coefficientNorm (4 / 5 : ℝ)
      (reflect n (descentAlphabetPolynomial n k) - C ((descentAlphabetPolynomial n k).coeff n)) <
      (descentAlphabetPolynomial n k).coeff n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) {z : ℂ}
    (hz : (((∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).map
      (algebraMap ℝ ℂ)).eval z) = 0) : ‖z‖ < 5 / 4 := by
  let f := ∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k
  have hd : f.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_le _ _).trans (natDegree_descentAlphabetPolynomial_le n k)
  have hmarg := coefficientNorm_sum_sub_constant_lt (by norm_num : (0 : ℝ) ≤ 4 / 5)
    s (fun k => reflect n (descentAlphabetPolynomial n k)) w hw hp (by
      intro k hk
      simpa only [coeff_reflect, revAt_zero] using
        hdom k hk)
  have he : (∑ k ∈ s, C (w k) * reflect n (descentAlphabetPolynomial n k)) = reflect n f := by
    ext i
    simp [f, coeff_reflect, coeff_C_mul]
  rw [he] at hmarg
  simp only [coeff_reflect, revAt_zero] at hmarg
  have hh := norm_lt_inv_of_reflect_coefficientNorm_lt (by norm_num : (0 : ℝ) < 4 / 5)
    hd (hmarg.trans_le (le_abs_self _)) (by simpa only [eval_map] using hz)
  norm_num at hh
  exact hh

/-- Every nonnegative mixture of cutoffs at least thirteen obeys the strict disk bound. -/
theorem norm_root_sum_descentAlphabetPolynomial_lt {n : ℕ} {s : Finset ℕ}
    (hs : ∀ k ∈ s, 13 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) {z : ℂ}
    (hz : (((∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).map
      (algebraMap ℝ ℂ)).eval z) = 0) : ‖z‖ < 5 / 4 :=
  norm_root_sum_descentAlphabetPolynomial_lt_of_dominance
    (fun k hk => descentAlphabetPolynomial_coefficientNorm_lt (hs k hk).1 (hs k hk).2) hw hp hz

end RealRooted.LongCycleDescents.Structural
