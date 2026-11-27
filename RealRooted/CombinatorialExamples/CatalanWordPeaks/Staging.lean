/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
import RealRooted.CombinatorialExamples.CatalanWordPeaks.Finite
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Tactic

/-!
# Conditional assembly awaiting the analytic Catalan strict-peak proof

This file is a reduction theorem, not an unconditional proof for all lengths.
The analytic sign grids and the signs at old roots remain explicit hypotheses.
ProgramComputer's four-cut integral, phase checkpoints, covariance bounds and
extreme-root comparisons are intended to discharge them. The original analytic
cutoff is 150, matching the kernel-checked finite prefix. No unconditional
all-length theorem is asserted elsewhere.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.Staging

open Polynomial

/-- Checkpoint signs give simple negative roots by the existing interval theorem.
The hypothesis is a finite sign grid, not a real-rootedness assertion. -/
theorem polynomial_roots_of_sign_grid {n : ℕ}
    (x : Fin (rowDegree n + 1) → ℝ) (hx : StrictMono x)
    (hneg : x (Fin.last (rowDegree n)) ≤ 0)
    (hsign : ∀ i : Fin (rowDegree n),
      (polynomial n).eval (x i.castSucc) * (polynomial n).eval (x i.succ) < 0) :
    (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ r ∈ (polynomial n).roots, r < 0 := by
  have hp : polynomial n ≠ 0 := leadingCoeff_ne_zero.mp (leadingCoeff_polynomial_pos n).ne'
  have h := Polynomial.splits_nodup_roots_of_strict_sign_changes hp
    (natDegree_polynomial_le n) x hx hsign
  exact ⟨h.2.1, HasSimpleRoots.of_roots_nodup hp h.2.2.1, h.1,
    fun r hr ↦ ((h.2.2.2 r hr).2).trans_le hneg⟩

/-- Strict derivative signs at the old roots imply standard interlacing with no
common roots. This is the existing Ma--Wang criterion specialized to the row degrees. -/
theorem polynomial_strictInterl_of_root_signs {n : ℕ}
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

/-- The precise conditional all-length target. The analytic inputs are unproved
here: sign grids for the remaining rows and strict derivative signs at old roots.
The conclusion includes genuine strictness in addition to the standard predicate. -/
theorem all_lengths_of_analytic_signs
    (grids : ∀ n, 150 ≤ n → ∃ x : Fin (rowDegree n + 1) → ℝ, StrictMono x ∧
      x (Fin.last (rowDegree n)) ≤ 0 ∧
      ∀ i : Fin (rowDegree n),
        (polynomial n).eval (x i.castSucc) * (polynomial n).eval (x i.succ) < 0)
    (rootSigns : ∀ n, 150 ≤ n → ∀ r, (polynomial n).IsRoot r →
      (polynomial (n + 1)).eval r * (polynomial n).derivative.eval r < 0) :
    (∀ n, (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ r ∈ (polynomial n).roots, r < 0) ∧
    ∀ n, StrictInterl (polynomial n) (polynomial (n + 1)) ∧
      (∀ r, ¬ ((polynomial n).IsRoot r ∧ (polynomial (n + 1)).IsRoot r)) ∧
      (rowDegree n ≠ 0 → ∃ y ∈ (polynomial (n + 1)).roots,
        (∀ r ∈ (polynomial n).roots, r < y) ∧
        ∀ z ∈ (polynomial (n + 1)).roots, z ≤ y) := by
  have hrows (n : ℕ) : (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ r ∈ (polynomial n).roots, r < 0 := by
    by_cases hn : n ≤ 150
    · exact Finite.polynomial_roots hn
    · obtain ⟨x, hx, hneg, hsign⟩ := grids n (by lia)
      exact polynomial_roots_of_sign_grid x hx hneg hsign
  refine ⟨hrows, ?_⟩
  intro n
  by_cases hn : n < 150
  · exact Finite.polynomial_strictInterl hn
  · obtain ⟨hi, hno⟩ := polynomial_strictInterl_of_root_signs (hrows n).1
      (hrows n).2.1 (rootSigns n (by lia))
    refine ⟨hi, hno, ?_⟩
    intro hm
    obtain ⟨y, hy, hmax⟩ := exists_rightmost_root_of_isRealRooted hi.2.1.1 hi.2.1.2 (by
      rw [natDegree_polynomial]
      have hd := rowDegree_succ n
      rcases hd with h | h <;> lia)
    refine ⟨y, (mem_roots hi.2.1.1).mpr hy, ?_, hmax⟩
    intro r hr
    exact lt_of_le_of_ne (hi.roots_le_of_right hmax r hr) fun heq ↦
      hno r ⟨(mem_roots hi.1.1).mp hr, heq.symm ▸ hy⟩

end RealRooted.CatalanWordPeaks.Staging
