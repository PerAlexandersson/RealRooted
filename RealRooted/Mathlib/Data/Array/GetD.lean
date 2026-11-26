/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Tactic

/-!
# Checking arrays by their entries

Entrywise certificates avoid constructing an `ofFn` array repeatedly during
kernel reduction of its decidable equality.
-/

public section

namespace Array

/-- Identify a generated array by its size and defaulted entries. -/
theorem ofFn_eq_of_getD {α : Type*} {n : ℕ} (f : Fin n → α) (a : Array α) (d : α)
    (hs : a.size = n) (hf : ∀ i, f i = a.getD i.val d) : ofFn f = a := by
  apply Array.ext (by simp [hs])
  intro i hi hia
  rw [getElem_ofFn, getElem_eq_getD d]
  exact hf ⟨i, by simpa using hi⟩


end Array
