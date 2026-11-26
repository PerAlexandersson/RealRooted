/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetLeading
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetTransform
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.LongCutoffDominance
public import RealRooted.IntervalDifferential.CoefficientNorm
import RealRooted.IntervalDifferential.MobiusRoots
import Mathlib.Tactic

/-!
# Transferring alphabet bounds to descent roots

Coefficient dominance puts the complex alphabet roots inside radius `5/4`. The
second-power-sum bound permits interval insertion; the Möbius transform returns
simple nonpositive roots of every nonzero nonnegative long-cutoff mixture.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

public noncomputable section

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
  norm_num only at hh
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
  norm_num only at hh
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

open Polynomial

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

private theorem mobius_interval_roots (G : ℝ[X]) (hG : G ≠ 0) (hs : G.Splits)
    (hn : G.roots.Nodup) (hi : ∀ r ∈ G.roots, -1 < r ∧ r < 1) :
    let H := mobiusTransform G.natDegree 1 1 (-1) 1 G
    H ≠ 0 ∧ H.natDegree = G.natDegree ∧ H.Splits ∧ H.roots.Nodup ∧
      ∀ r ∈ H.roots, r < 0 := by
  have hH : mobiusTransform G.natDegree 1 1 (-1) 1 G ≠ 0 :=
    mobiusTransform_ne_zero _ _ _ _ _ hG le_rfl (by norm_num)
  refine ⟨hH, splits_roots_nodup_neg_of_mobius_eval hH
    (natDegree_mobiusTransform_le _ _ _ _ _ le_rfl) hG hs hn hi ?_⟩
  intro z hz _ hzero
  have hd : z + 1 ≠ 0 := by linarith
  have he : -mobiusIntervalRoot z + 1 = 2 / (z + 1) := by
    dsimp [mobiusIntervalRoot]
    field_simp
    ring
  have hden : (-1 : ℝ) * mobiusIntervalRoot z + 1 ≠ 0 := by
    rw [neg_one_mul, he]
    exact div_ne_zero (by norm_num) hd
  rw [eval_mobiusTransform _ _ _ _ _ le_rfl hden]
  have hinv : (1 * mobiusIntervalRoot z + 1) / (-1 * mobiusIntervalRoot z + 1) = z := by
    dsimp [mobiusIntervalRoot]
    field_simp
    ring
  rw [hinv, hzero, mul_zero]

/-- The spectral hypotheses give the complete root conclusion in the descent
variable, including its simple zero at zero and the exact degree. -/
theorem interval_transform_roots (Q : ℝ[X]) (hm : 15 ≤ Q.natDegree)
    {radiusSq : ℝ} (hradius : radiusSq ≤ 25 / 16)
    (hdisk : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval z = 0 →
      Complex.normSq z ≤ radiusSq)
    (hpower : -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum) :
    let p := C 6 * X * mobiusTransform Q.natDegree 1 1 (-1) 1 (intervalSpectralApply 4 Q 1)
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = Q.natDegree + 1 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  obtain ⟨hG, hd, hs, hn, hi⟩ := intervalSpectralApply_one_roots Q hm hradius hdisk hpower
  obtain ⟨hH, hHd, hHs, hHn, hHi⟩ := mobius_interval_roots _ hG hs hn hi
  rw [hd] at hH hHd hHs hHn hHi
  dsimp only
  let H := mobiusTransform Q.natDegree 1 1 (-1) 1 (intervalSpectralApply 4 Q 1)
  have hz : (0 : ℝ) ∉ H.roots := by intro hh; exact (lt_irrefl 0) (hHi 0 hh)
  have hroot : (C 6 * X * H).roots = {0} + H.roots := by
    rw [mul_assoc, roots_C_mul _ (by norm_num : (6 : ℝ) ≠ 0),
      roots_mul (mul_ne_zero X_ne_zero hH), roots_X]
  refine ⟨mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (by norm_num)) X_ne_zero) hH,
    (Splits.C 6).mul Splits.X |>.mul hHs, ?_, ?_, ?_, ?_⟩
  · rw [hroot, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨hz, hHn⟩
  · rw [hroot]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self 0))
  · rw [mul_assoc, natDegree_C_mul (by norm_num : (6 : ℝ) ≠ 0),
      natDegree_mul X_ne_zero hH, natDegree_X, hHd]
    lia
  · intro r hr
    rw [hroot, Multiset.mem_add, Multiset.mem_singleton] at hr
    exact hr.elim (fun h => h ▸ le_rfl) (fun h => (hHi r h).le)

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

private theorem spectral_sum {s : Finset ℕ} (w : ℕ → ℝ) (Q : ℕ → ℝ[X]) :
    intervalSpectralApply 4 (∑ k ∈ s, C (w k) * Q k) 1 =
      ∑ k ∈ s, C (w k) * intervalSpectralApply 4 (Q k) 1 := by
  simp only [intervalSpectralApply, map_sum, map_mul, aeval_C, LinearMap.sum_apply,
    mul_apply_eq_comp, Module.algebraMap_end_apply, smul_eq_C_mul]

/-- A family of actual alphabet dominance inequalities gives the complete root
conclusion for every nonzero nonnegative mixture in that family. -/
theorem mixture_roots_of_coefficientNorm_lt {m : ℕ} (hm : 15 ≤ m) {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ m + 3)
    (hdom : ∀ k ∈ s, coefficientNorm (4 / 5 : ℝ)
      (reflect (m + 3) (descentAlphabetPolynomial (m + 3) k) -
        C ((descentAlphabetPolynomial (m + 3) k).coeff (m + 3))) <
      (descentAlphabetPolynomial (m + 3) k).coeff (m + 3))
    {w : ℕ → ℝ} (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let p := ∑ k ∈ s, C (w k) * realDescentPolynomial (m + 3) k
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = m + 1 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  classical
  choose Q hQ using fun k : ℕ => exists_interval_transform m (le_max_left 3 k)
  have hmax k (hk : k ∈ s) : max 3 k = k := max_eq_right (hs k hk).1
  let f := ∑ k ∈ s, C (w k) * descentAlphabetPolynomial (m + 3) k
  let R := ∑ k ∈ s, C (w k) * Q k
  have hf : f = X * (X ^ 2 - 1) * R := by
    dsimp [f, R]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have hh := hQ k
    rw [hmax k hk] at hh
    rw [hh.2.1]
    ring
  have hlead := sum_descentAlphabetPolynomial_leading_signs hs hw hp
  have hfn : f ≠ 0 := by
    intro hz
    have hh : 0 < f.coeff (m + 3) := hlead.2.1
    simp [hz] at hh
  have hR : R ≠ 0 := by intro hz; simp only [hz, mul_zero] at hf; exact hfn hf
  have hb : (X * (X ^ 2 - 1) : ℝ[X]).natDegree = 3 := by
    compute_degree <;> norm_num
  have hbn : (X * (X ^ 2 - 1) : ℝ[X]) ≠ 0 := by
    intro hz; simp [hz] at hb
  have hd : R.natDegree = m := by
    have hh := hlead.1
    change f.natDegree = m + 3 at hh
    rw [hf, natDegree_mul hbn hR, hb] at hh
    lia
  have hroot (z : ℂ) (hz : (R.map (algebraMap ℝ ℂ)).eval z = 0) :
      Complex.normSq z ≤ (25 / 16 : ℝ) := by
    have hfz : (f.map (algebraMap ℝ ℂ)).eval z = 0 := by
      rw [hf, Polynomial.map_mul, eval_mul, hz, mul_zero]
    have hh := norm_root_sum_descentAlphabetPolynomial_lt_of_dominance hdom hw hp hfz
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hpower := quotient_second_powerSum_ge_neg_two hfn hf
    (sum_descentAlphabetPolynomial_second_powerSum_nonneg hs hw hp)
  have ht := interval_transform_roots R (by lia) le_rfl hroot hpower
  have he : (∑ k ∈ s, C (w k) * realDescentPolynomial (m + 3) k) =
      C 6 * X * mobiusTransform R.natDegree 1 1 (-1) 1 (intervalSpectralApply 4 R 1) := by
    rw [hd, spectral_sum, mobiusTransform_finset_sum, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hh := hQ k
    rw [hmax k hk] at hh
    rw [mobiusTransform_C_mul, hh.2.2]
    ring
  rw [he]
  simpa only [hd] using ht

end RealRooted.LongCycleDescents.Structural
