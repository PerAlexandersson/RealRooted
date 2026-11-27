/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
import RealRooted.CombinatorialExamples.CatalanWordPeaks.RootSelection
import RealRooted.CombinatorialExamples.CatalanWordPeaks.PoleEstimates
import Mathlib.Tactic

/-!
# Closest-root signs from logarithmic-derivative growth

The transition endpoint and the gap to all other roots isolate the first
reciprocal term. Mathlib supplies the logarithmic derivative over the root multiset.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.RightEdge

open Finset

private def firstIndex (n : ℕ) (hn : 150 ≤ n) : Fin (rowDegree n) :=
  ⟨0, by unfold rowDegree; lia⟩

private theorem ne_first_pos {n : ℕ} (hn : 150 ≤ n) {i : Fin (rowDegree n)}
    (hi : i ≠ firstIndex n hn) : 0 < i.val := by
  by_contra! h
  exact hi (Fin.ext (by dsimp [firstIndex]; lia))

private theorem inverse_tail_bounds {n : ℕ} (hn : 150 ≤ n) {r : Fin (rowDegree n) → ℝ}
    (htail : ∀ i : Fin (rowDegree n), 0 < i.val → 11 / 16 + 1 / (n : ℝ) ^ 2 < r i) :
    let t := ∑ i ∈ Finset.univ.erase (firstIndex n hn), ((-11 / 16 : ℝ) + r i)⁻¹
    0 ≤ t ∧ t ≤ (n : ℝ) ^ 3 := by
  classical
  dsimp only
  let s := Finset.univ.erase (firstIndex n hn)
  have hpos (i : Fin (rowDegree n)) (hi : i ∈ s) : 0 < (-11 / 16 : ℝ) + r i := by
    have h := htail i (ne_first_pos hn (Finset.ne_of_mem_erase hi))
    linarith [show 0 ≤ 1 / (n : ℝ) ^ 2 by positivity]
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact Finset.sum_nonneg (fun i hi => (inv_pos.mpr (hpos i hi)).le)
  · calc
      _ ≤ ∑ _ ∈ s, (n : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := htail i (ne_first_pos hn (Finset.ne_of_mem_erase hi))
        have hp : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        have hle : ((n : ℝ) ^ 2)⁻¹ ≤ (-11 / 16 : ℝ) + r i := by
          rw [← one_div]
          linarith
        simpa only [inv_inv] using (inv_le_inv₀ (hpos i hi) (inv_pos.mpr hp)).mpr hle
      _ = (s.card : ℝ) * (n : ℝ) ^ 2 := by simp
      _ ≤ _ := by
        have hcard : s.card ≤ n :=
          (Finset.card_le_univ _).trans (by rw [Fintype.card_fin]; unfold rowDegree; lia)
        calc
          _ ≤ (n : ℝ) * (n : ℝ) ^ 2  :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
          _ = _ := by ring

/-- The two logarithmic-derivative estimates at the coalescence point,
with the checkpoint separation, give the exact rightmost-root sign. -/
private theorem rightmost_sign_of_logDerivative_growth {n : ℕ} (hn : 150 ≤ n)
    {old : Fin (rowDegree n) → ℝ} {new : Fin (rowDegree (n + 1)) → ℝ}
    (hOld : (↑(List.ofFn (fun i => -old i)) : Multiset ℝ) = (polynomial n).roots)
    (hNew : (↑(List.ofFn (fun i => -new i)) : Multiset ℝ) = (polynomial (n+1)).roots)
    (hsOld : (polynomial n).Splits) (hsNew : (polynomial (n+1)).Splits)
    (hAll : ∀ i, (11 / 16 : ℝ) < old i) (hAll' : ∀ i, (11 / 16 : ℝ) < new i)
    (hgap : ∀ i : Fin (rowDegree n), 0 < i.val → 11 / 16 + 1 / (n : ℝ) ^ 2 < old i)
    (hgap' : ∀ i : Fin (rowDegree (n + 1)), 0 < i.val →
      11 / 16 + 1 / ((n + 1 : ℕ) : ℝ) ^ 2 < new i)
    (hv : 0 < (polynomial n).eval (-11 / 16)) (hv' : 0 < (polynomial (n + 1)).eval (-11 / 16))
    (hlog : 300 * (n : ℝ) ^ 3 <
      (polynomial n).derivative.eval (-11 / 16) / (polynomial n).eval (-11 / 16))
    (hstep : 100 * (n : ℝ) ^ 3 <
      (polynomial (n + 1)).derivative.eval (-11 / 16) / (polynomial (n + 1)).eval (-11 / 16) -
        (polynomial n).derivative.eval (-11 / 16) / (polynomial n).eval (-11 / 16))
    (i : Fin (rowDegree n)) (hi : i.val = 0) : (polynomial (n + 1)).eval (-old i) < 0 := by
  classical
  rw [show i = firstIndex n hn from Fin.ext hi]
  have hn' : 150 ≤ n + 1 := by lia
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  let i₀ := firstIndex n hn
  let i₀' := firstIndex (n + 1) hn'
  let τ : ℝ := -11 / 16
  let A := τ + old i₀
  let B := τ + new i₀'
  let T := ∑ i ∈ Finset.univ.erase i₀, (τ + old i)⁻¹
  let U := ∑ i ∈ Finset.univ.erase i₀', (τ + new i)⁻¹
  have hA : 0 < A := by have := hAll i₀; dsimp [A, τ]; linarith
  have hB : 0 < B := by have := hAll' i₀'; dsimp [B, τ]; linarith
  have hl := derivative_div_eval_eq_root_sum hsOld hOld (t := τ) hv.ne'
  have hr := derivative_div_eval_eq_root_sum hsNew hNew (t := τ) hv'.ne'
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀')] at hr
  change _ = A⁻¹ + T at hl
  change _ = B⁻¹ + U at hr
  change 300 * (n : ℝ) ^ 3 < (polynomial n).derivative.eval τ / (polynomial n).eval τ at hlog
  change 100 * (n : ℝ) ^ 3 <
    (polynomial (n + 1)).derivative.eval τ / (polynomial (n + 1)).eval τ -
        (polynomial n).derivative.eval τ / (polynomial n).eval τ at hstep
  rw [hl] at hlog
  rw [hr, hl] at hstep
  obtain ⟨hT₀, hT⟩ := inverse_tail_bounds hn hgap
  obtain ⟨_, hU⟩ := inverse_tail_bounds hn' hgap'
  change 0 ≤ T at hT₀
  change T ≤ (n : ℝ) ^ 3 at hT
  change U ≤ ((n + 1 : ℕ) : ℝ) ^ 3 at hU
  push_cast at hU
  have hs : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hc3 : ((n : ℝ) + 1) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hs 3
      _ = _ := by ring
  have hBinv : A⁻¹ < B⁻¹ := by linarith [hc3, show 0 ≤ (n : ℝ) ^ 3 by positivity]
  have hBA : B < A := (inv_lt_inv₀ hA hB).mp hBinv
  have hAn : ((n : ℝ) + 1) ^ 2 < A⁻¹ := by
    have hs' : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      calc
        _ ≤ (2 * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
        _ = _ := by ring
    nlinarith only [hlog, hT, hs', mul_nonneg (sq_nonneg (n : ℝ))
      (show 0 ≤ (n : ℝ) - 1 by linarith)]
  have hAinv : A < 1 / ((n : ℝ) + 1) ^ 2 := by
    have hp : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    rw [one_div]
    apply (inv_lt_inv₀ (inv_pos.mpr hp) hA).mp
    simpa only [one_div, inv_inv] using hAn
  have htail : 0 < ∏ i ∈ Finset.univ.erase i₀', (-old i₀ + new i) := by
    apply Finset.prod_pos
    intro i hi
    have hh := hgap' i (ne_first_pos hn' (Finset.ne_of_mem_erase hi))
    push_cast at hh
    dsimp [A, τ] at hAinv
    linarith only [hh, hAinv]
  rw [eval_eq_root_product hsNew hNew, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀')]
  exact mul_neg_of_pos_of_neg (leadingCoeff_polynomial_pos (n + 1))
    (mul_neg_of_neg_of_pos (show -old i₀ + new i₀' < 0 by dsimp [B, A, τ] at hBA; linarith) htail)

/-- The next row is strictly negative at the old closest root. -/
theorem rightmost_root_sign {n : ℕ} (hn : 150 ≤ n)
    {old : Fin (rowDegree n) → ℝ} {new : Fin (rowDegree (n+1)) → ℝ}
    (hOld : (↑(List.ofFn (fun i => -old i)) : Multiset ℝ) = (polynomial n).roots)
    (hNew : (↑(List.ofFn (fun i => -new i)) : Multiset ℝ) = (polynomial (n+1)).roots)
    (hsOld : (polynomial n).Splits) (hsNew : (polynomial (n+1)).Splits)
    (hAll : ∀ i, (11 / 16 : ℝ) < old i) (hAll' : ∀ i, (11 / 16 : ℝ) < new i)
    (hgap : ∀ i, 0 < i.val → (11 / 16 : ℝ) + 1 / (n : ℝ)^2 < old i)
    (hgap' : ∀ i, 0 < i.val → (11 / 16 : ℝ) + 1 / ((n+1 : ℕ) : ℝ)^2 < new i)
    (i : Fin (rowDegree n)) (hi : i.val = 0) : (polynomial (n+1)).eval (-old i) < 0 := by
  obtain ⟨hv, hlog, hstep⟩ := transition_bounds hn
  exact rightmost_sign_of_logDerivative_growth hn hOld hNew hsOld hsNew hAll hAll'
    hgap hgap' hv (transition_bounds (by lia : 150 ≤ n+1)).1 hlog hstep i hi

end RealRooted.CatalanWordPeaks.RightEdge
