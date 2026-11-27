/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
import RealRooted.CombinatorialExamples.CatalanWordPeaks.Finite
import RealRooted.CombinatorialExamples.CatalanWordPeaks.FarEdge
import RealRooted.CombinatorialExamples.CatalanWordPeaks.NearEdge
import RealRooted.CombinatorialExamples.CatalanWordPeaks.RootSelection
import RealRooted.CombinatorialExamples.CatalanWordPeaks.InteriorSigns
import RealRooted.Interlacing.Residue
import RealRooted.MaWang.Weak.DerivativeSign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Simple negative roots and strict interlacing at every length

The explicit coefficient formula defines the rows. Exact finite certificates
and the checked analytic root signs cover every length without an analytic hypothesis.

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

namespace RealRooted.CatalanWordPeaks

open Polynomial

private theorem roots_nodup_of_list {p : ℝ[X]} {m : ℕ} {r : Fin m → ℝ}
    (hr : StrictMono r) (heq : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = p.roots) :
    p.roots.Nodup := by
  rw [← heq, Multiset.coe_nodup]
  exact List.nodup_ofFn.mpr (neg_injective.comp hr.injective)

/-- Every formula-defined Catalan strict-peak row has simple negative roots. -/
theorem polynomial_roots (n : ℕ) :
    (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ r ∈ (polynomial n).roots, r < 0 := by
  by_cases hn : n ≤ 150
  · exact Finite.polynomial_roots hn
  · obtain ⟨r, hr, ht, heq, hs, _, _⟩ := CutGeometry.roots_from_150 (by lia : 150 ≤ n)
    have hp : polynomial n ≠ 0 := leadingCoeff_ne_zero.mp (leadingCoeff_polynomial_pos n).ne'
    refine ⟨hs, HasSimpleRoots.of_roots_nodup hp (roots_nodup_of_list hr heq),
      natDegree_polynomial n, ?_⟩
    intro z hz
    rw [← heq] at hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hz)
    linarith [ht i]

private theorem derivative_sign_of_root_list {p : ℝ[X]} {m : ℕ} {r : Fin m → ℝ}
    (hs : p.Splits) (hlc : 0 < p.leadingCoeff) (hr : StrictMono r)
    (heq : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = p.roots) (i : Fin m) :
    0 < (-1 : ℝ) ^ i.val * p.derivative.eval (-r i) := by
  classical
  have hmem : -r i ∈ p.roots := by
    rw [← heq]
    exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hcount : p.roots.countP (fun a => -r i < a) = i.val := by
    rw [← heq, ← Fin.univ_val_map, Multiset.countP_map]
    change (Finset.univ.filter (fun j => -r i < -r j)).card = i.val
    have hf : Finset.univ.filter (fun j => -r i < -r j) = Finset.Iio i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        neg_lt_neg_iff, hr.lt_iff_lt]
    rw [hf, Fin.card_Iio]
  have hd := deriv_at_root_sign hs hlc (-r i) hmem
    (Multiset.count_eq_one_of_mem (roots_nodup_of_list hr heq) hmem)
  simpa only [hcount, mul_comm] using hd

private theorem analytic_root_signs {n : ℕ} (hn : 150 ≤ n) :
    ∀ z, (polynomial n).IsRoot z →
      (polynomial (n+1)).eval z * (polynomial n).derivative.eval z < 0 := by
  obtain ⟨old, hom, hot, ho, hos, hphase, hogap⟩ := CutGeometry.roots_from_150 hn
  obtain ⟨new, hem, het, he, hes, _, hegap⟩ :=
    CutGeometry.roots_from_150 (by lia : 150 ≤ n+1)
  have hp : polynomial n ≠ 0 := leadingCoeff_ne_zero.mp (leadingCoeff_polynomial_pos n).ne'
  intro z hz
  have hzmem := (mem_roots hp).mpr hz
  rw [← ho] at hzmem
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hzmem)
  have hnext : 0 < (-1 : ℝ) ^ (i.val + 1) * (polynomial (n+1)).eval (-old i) := by
    by_cases hi0 : i.val = 0
    · have h := RightEdge.rightmost_root_sign hn ho he hos hes hot het hogap hegap i hi0
      simpa only [hi0, zero_add, pow_one, neg_one_mul] using neg_pos.mpr h
    · by_cases hilast : i.val + 1 = rowDegree n
      · exact FarEdge.farthest_root_sign n hn old new hom hem
          (fun j => by linarith [hot j]) (fun j => by linarith [het j]) ho he i hilast
      · obtain ⟨θ, hθ, hr, hlo, hhi⟩ := hphase i (by lia) (by have := i.isLt; lia)
        have hzero : (polynomial n).eval (-CutGeometry.modulus θ) = 0 := by
          simpa only [hr] using hz.eq_zero
        simpa only [hr] using CutGeometry.eval_sign_at_oldRoot_in_phaseBand hn hθ
          (by lia) (by have := i.isLt; lia) hlo hhi hzero
  have hder := derivative_sign_of_root_list hos (leadingCoeff_polynomial_pos n) hom ho i
  rcases neg_one_pow_eq_or ℝ i.val with h | h <;>
    simp only [pow_succ, h, one_mul, neg_mul, neg_neg] at hnext hder <;>
    nlinarith

/-- Strict derivative signs at the old roots imply standard interlacing with no
common roots. This is the existing Ma--Wang criterion specialized to the row degrees. -/
private theorem polynomial_strictInterl_of_root_signs {n : ℕ}
    (hs : (polynomial n).Splits) (hsimple : HasSimpleRoots (polynomial n))
    (hsign : ∀ r, (polynomial n).IsRoot r →
      (polynomial (n + 1)).eval r * (polynomial n).derivative.eval r < 0) :
    StrictInterl (polynomial n) (polynomial (n + 1)) ∧
      ∀ r, ¬ ((polynomial n).IsRoot r ∧ (polynomial (n + 1)).IsRoot r) := by
  have hd := rowDegree_succ n
  refine ⟨strictInterl_of_eval_mul_derivative_nonpos (leadingCoeff_polynomial_pos n) hs
    hsimple.roots_nodup (leadingCoeff_polynomial_pos (n + 1)) ?_ ?_
    (fun r hr ↦ (hsign r hr).le), ?_⟩
  · rw [natDegree_polynomial, natDegree_polynomial]
    rcases hd with h | h <;> lia
  · rw [natDegree_polynomial, natDegree_polynomial]
    rcases hd with h | h <;> lia
  · intro r ⟨hr, hr'⟩
    have h := hsign r hr
    rw [hr'.eq_zero, zero_mul] at h
    exact (lt_irrefl 0) h

/-- Consecutive rows strictly interlace, have no common roots, and have the stated
rightmost-root orientation whenever the old row is nonconstant. -/
theorem polynomial_strictInterl (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n+1)) ∧
      (∀ r, ¬ ((polynomial n).IsRoot r ∧ (polynomial (n+1)).IsRoot r)) ∧
      (rowDegree n ≠ 0 → ∃ y ∈ (polynomial (n+1)).roots,
        (∀ r ∈ (polynomial n).roots, r < y) ∧
        ∀ z ∈ (polynomial (n+1)).roots, z ≤ y) := by
  by_cases hn : n < 150
  · exact Finite.polynomial_strictInterl hn
  · obtain ⟨hi, hno⟩ := polynomial_strictInterl_of_root_signs (polynomial_roots n).1
      (polynomial_roots n).2.1 (analytic_root_signs (by lia : 150 ≤ n))
    refine ⟨hi, hno, ?_⟩
    intro hm
    obtain ⟨y, hy, hmax⟩ := exists_rightmost_root_of_isRealRooted hi.2.1.1 hi.2.1.2 (by
      rw [natDegree_polynomial]
      have hd := rowDegree_succ n
      rcases hd with h | h <;> lia)
    refine ⟨y, (mem_roots hi.2.1.1).mpr hy, ?_, hmax⟩
    intro r hr
    exact lt_of_le_of_ne (hi.roots_le_of_right hmax r hr) fun heq =>
      hno r ⟨(mem_roots hi.1.1).mp hr, heq.symm ▸ hy⟩

/-- At every length the formula-defined rows have simple negative roots and
strictly interlace with disjoint roots and rightmost-root orientation. -/
theorem all_lengths :
    (∀ n, (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ r ∈ (polynomial n).roots, r < 0) ∧
    ∀ n, StrictInterl (polynomial n) (polynomial (n+1)) ∧
      (∀ r, ¬ ((polynomial n).IsRoot r ∧ (polynomial (n+1)).IsRoot r)) ∧
      (rowDegree n ≠ 0 → ∃ y ∈ (polynomial (n+1)).roots,
        (∀ r ∈ (polynomial n).roots, r < y) ∧
        ∀ z ∈ (polynomial (n+1)).roots, z ≤ y) :=
  ⟨polynomial_roots, polynomial_strictInterl⟩

end RealRooted.CatalanWordPeaks
