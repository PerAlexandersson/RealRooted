/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetLeading
import RealRooted.RootVieta.Newton
import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.Factorization
import Mathlib.Tactic

/-!
# The alphabet second power sum

We apply Newton's second identity to the proved leading-coefficient signs.
No root-disk estimate is needed for this condition.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

private theorem second_powerSum_nonneg {p : ℝ[X]} {n : ℕ} (hn : 2 ≤ n)
    (hd : p.natDegree ≤ n) (h0 : 0 < p.coeff n)
    (h1 : p.coeff (n - 1) = 0) (h2 : p.coeff (n - 2) ≤ 0) :
    0 ≤ (((p.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  let f := p.map (algebraMap ℝ ℂ)
  have hpn : p ≠ 0 := by intro he; simp [he] at h0
  have hfn : f ≠ 0 := Polynomial.map_ne_zero hpn
  have hdeg : p.natDegree = n := hd.antisymm (le_natDegree_of_ne_zero h0.ne')
  have hfdeg : f.natDegree = n := by simpa [f] using hdeg
  have he := RootVieta.leadingCoeff_mul_roots_powerSum (IsAlgClosed.splits f) hfn
    2 (by decide) (by lia)
  have ha : (Finset.HasAntidiagonal.antidiagonal 2).filter
      (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by decide
  rw [ha] at he
  simp only [sum_singleton, hfdeg] at he
  have hl : p.leadingCoeff = p.coeff n := by rw [leadingCoeff, hdeg]
  simp only [f, coeff_map, leadingCoeff_map, hl, h1, map_zero, zero_mul, sub_zero,
    Complex.coe_algebraMap] at he
  have hr := congrArg Complex.re he
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.neg_re] at hr
  norm_num at hr
  have hs : Complex.re ((f.roots.map fun z => z ^ 2).sum) =
      ((f.roots.map fun z => (z ^ 2).re).sum) := by
    exact (map_multiset_sum Complex.reAddGroupHom _).trans (by simp)
  change p.coeff n * Complex.re ((f.roots.map fun z => z ^ 2).sum) = _ at hr
  rw [hs] at hr
  change 0 ≤ ((f.roots.map fun z => (z ^ 2).re).sum)
  nlinarith

/-- The second power sum of every actual long-cutoff alphabet is nonnegative. -/
theorem descentAlphabetPolynomial_second_powerSum_nonneg {n k : ℕ}
    (hk : 3 ≤ k) (hkn : k ≤ n) :
    0 ≤ ((((descentAlphabetPolynomial n k).map (algebraMap ℝ ℂ)).roots).map
      fun z => (z ^ 2).re).sum := by
  have hs := descentAlphabetPolynomial_leading_signs (by lia : 2 ≤ n) hk hkn
  exact second_powerSum_nonneg (by lia) (natDegree_descentAlphabetPolynomial_le n k)
    hs.1 hs.2.1 hs.2.2

/-- All nonzero nonnegative sums of long-cutoff alphabets have the same
leading-coefficient signs. -/
theorem sum_descentAlphabetPolynomial_leading_signs {n : ℕ} {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let f := ∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k
    f.natDegree = n ∧ 0 < f.coeff n ∧ f.coeff (n - 1) = 0 ∧ f.coeff (n - 2) ≤ 0 := by
  classical
  dsimp only
  have hn : 2 ≤ n := by obtain ⟨k, hk, _⟩ := hp; have := hs k hk; lia
  have hl k hk := descentAlphabetPolynomial_leading_signs hn (hs k hk).1 (hs k hk).2
  have hd : (∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_le _ _).trans (natDegree_descentAlphabetPolynomial_le n k)
  have hz : 0 < (∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).coeff n := by
    simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_pos' (fun k hk => mul_nonneg (hw k hk) (hl k hk).1.le)
      (hp.imp fun k hk => ⟨hk.1, mul_pos hk.2 (hl k hk.1).1⟩)
  refine ⟨hd.antisymm (le_natDegree_of_ne_zero hz.ne'), hz, ?_, ?_⟩
  · simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_eq_zero (fun k hk => by rw [(hl k hk).2.1, mul_zero])
  · simp only [finsetSum_coeff, coeff_C_mul]
    exact sum_nonpos (fun k hk => mul_nonpos_of_nonneg_of_nonpos (hw k hk) (hl k hk).2.2)

/-- The second power sum is nonnegative for every nonzero nonnegative
long-cutoff alphabet mixture. -/
theorem sum_descentAlphabetPolynomial_second_powerSum_nonneg {n : ℕ} {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let f := ∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k
    0 ≤ (((f.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  have hn : 2 ≤ n := by obtain ⟨k, hk, _⟩ := hp; have := hs k hk; lia
  have hf := sum_descentAlphabetPolynomial_leading_signs hs hw hp
  exact second_powerSum_nonneg hn hf.1.le hf.2.1 hf.2.2.1 hf.2.2.2

private theorem cubic_second_powerSum :
    (((((X * (X ^ 2 - 1) : ℝ[X]).map (algebraMap ℝ ℂ)).roots).map
      fun z => (z ^ 2).re).sum) = 2 := by
  have hf : (X * (X ^ 2 - 1) : ℂ[X]) = X * ((X - C 1) * (X - C (-1))) := by
    norm_num
    ring
  simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one]
  rw [hf, roots_mul (mul_ne_zero X_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X, roots_X_sub_C, roots_X_sub_C]
  norm_num

/-- Removing the three alphabet factors subtracts exactly two from the second
power sum. This lemma also applies to nonnegative mixtures. -/
theorem quotient_second_powerSum_ge_neg_two {f Q : ℝ[X]} (hf : f ≠ 0)
    (he : f = X * (X ^ 2 - 1) * Q)
    (hp : 0 ≤ (((f.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum) :
    -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  have hq : Q ≠ 0 := by intro hh; simp [hh] at he; exact hf he
  have hm : (X * (X ^ 2 - 1) : ℝ[X]).map (algebraMap ℝ ℂ) *
      Q.map (algebraMap ℝ ℂ) ≠ 0 := by
    rw [← Polynomial.map_mul, ← he]
    exact Polynomial.map_ne_zero hf
  rw [he, Polynomial.map_mul, roots_mul hm,
    Multiset.map_add, Multiset.sum_add, cubic_second_powerSum] at hp
  linarith

/-- The actual alphabet quotient always satisfies the moment hypothesis of the
structural insertion theorem. -/
theorem descentAlphabetPolynomial_quotient_second_powerSum {n k : ℕ}
    (hk : 3 ≤ k) (hkn : k ≤ n) {Q : ℝ[X]}
    (he : descentAlphabetPolynomial n k = X * (X ^ 2 - 1) * Q) :
    -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum := by
  have hh := (descentAlphabetPolynomial_leading_signs (by lia) hk hkn).1
  exact quotient_second_powerSum_ge_neg_two
    (fun hz => by simp [hz] at hh) he
    (descentAlphabetPolynomial_second_powerSum_nonneg hk hkn)

end RealRooted.LongCycleDescents.Structural
