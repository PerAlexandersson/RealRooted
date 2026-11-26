/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortTailCertificates
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortCutoffDominance
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.MixtureTransfer
import Mathlib.Tactic

/-!
# Uniform alphabet bounds beyond rank seventeen

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

/-- Every genuine long-cutoff alphabet is strictly coefficient-dominant from rank 18. -/
theorem coefficientNorm_lossRow_sub_constant_lt_of_rank {n k : ℕ}
    (hn : 18 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  by_cases h13 : 13 ≤ k
  · exact coefficientNorm_lossRow_sub_constant_lt h13 hkn
  · obtain ⟨H, hH, hc, hp⟩ := exists_shortCertificates hk (by lia)
    by_cases hHn : H ≤ n
    · exact coefficientNorm_lt_of_shortTailCertificate (by lia) (by lia) hHn hc
    · exact coefficientNorm_lt_of_shortPrefixCertificate hn (by lia) hp

/-- Coefficient dominance for every actual alphabet from rank 18. -/
theorem descentAlphabetPolynomial_coefficientNorm_lt_of_rank {n k : ℕ}
    (hn : 18 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) :
    coefficientNorm (4 / 5 : ℝ) (reflect n (descentAlphabetPolynomial n k) -
      C ((descentAlphabetPolynomial n k).coeff n)) <
      (descentAlphabetPolynomial n k).coeff n :=
  descentAlphabetPolynomial_coefficientNorm_lt_of_lossRow (by lia)
    (coefficientNorm_lossRow_sub_constant_lt_of_rank hn hk hkn)

/-- The strict `5/4` disk holds for every nonzero nonnegative alphabet mixture from rank 18. -/
theorem norm_root_sum_descentAlphabetPolynomial_lt_of_rank {n : ℕ} (hn : 18 ≤ n)
    {s : Finset ℕ} (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) {z : ℂ}
    (hz : (((∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).map
      (algebraMap ℝ ℂ)).eval z) = 0) : ‖z‖ < 5 / 4 :=
  norm_root_sum_descentAlphabetPolynomial_lt_of_dominance
    (fun k hk => descentAlphabetPolynomial_coefficientNorm_lt_of_rank hn
      (hs k hk).1 (hs k hk).2) hw hp hz

/-- All long-cutoff descent mixtures have simple nonpositive roots from rank 18. -/
theorem mixture_roots_of_rank {n : ℕ} (hn : 18 ≤ n) {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let p := ∑ k ∈ s, C (w k) * realDescentPolynomial n k
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = n - 2 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by lia⟩
  simpa only [show m + 3 - 2 = m + 1 by lia] using
    mixture_roots_of_coefficientNorm_lt (by lia : 15 ≤ m) hs
      (fun k hk => descentAlphabetPolynomial_coefficientNorm_lt_of_rank hn
        (hs k hk).1 (hs k hk).2) hw hp

/-- Every actual long-cutoff row has the structural simple-root conclusion from rank 18. -/
theorem realDescentPolynomial_roots_of_rank {n k : ℕ} (hn : 18 ≤ n)
    (hk : 3 ≤ k) (hkn : k ≤ n) :
    let p := realDescentPolynomial n k
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = n - 2 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  simpa using mixture_roots_of_rank hn (s := {k}) (w := fun _ => 1)
    (by simpa using And.intro hk hkn) (by simp) (by simp)

end RealRooted.LongCycleDescents.Structural
