/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetDisk
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetMoment
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.RootTransfer
import Mathlib.Tactic

/-!
# Structural transfer for nonnegative long-cutoff mixtures

We sum the proved alphabet factorizations and operator identities before applying
one instance of the interval root theorem.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

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
  have hR : R ≠ 0 := by intro hz; simp [hz] at hf; exact hfn hf
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
