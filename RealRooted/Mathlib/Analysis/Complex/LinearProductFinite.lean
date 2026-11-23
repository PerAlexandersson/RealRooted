/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.TypeStar

/-!
# Finite linear products as finitely supported natural sequences
-/

public section

open Function

namespace Complex

/-- A finite family of nonnegative slopes can be padded with zeros to a natural
sequence, preserving the exact complex product. Empty families are included. -/
theorem exists_finite_support_tprod_eq_prod {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (support b).Finite ∧
      ∀ z : ℂ, (∏' n, (1 + (b n : ℂ) * z)) = ∏ i, (1 + (a i : ℂ) * z) := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let b : ℕ → ℝ := extend e a 0
  have hbe (i : ι) : b (e i) = a i := he.extend_apply a 0 i
  have hbzero (n : ℕ) (hn : n ∉ Set.range e) : b n = 0 :=
    extend_apply' (f := e) a (0 : ℕ → ℝ) n hn
  have hb (n : ℕ) : 0 ≤ b n := by
    by_cases hn : n ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hn
      rw [hbe]
      exact ha i
    · rw [hbzero n hn]
  have hfin : (support b).Finite := (Set.finite_range e).subset (by
    intro n hn
    by_contra he'
    exact hn (hbzero n he'))
  refine ⟨b, hb, hfin, fun z => ?_⟩
  have hprod := he.tprod_eq (f := fun n => (1 + (b n : ℂ) * z)) (by
    intro n hn
    by_contra he'
    exact hn (by simp only [hbzero n he', ofReal_zero, zero_mul, add_zero]))
  simpa only [hbe, tprod_fintype] using hprod.symm

end Complex
