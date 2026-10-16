/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Order

/-!
# Ascent statistics of finite relations

This file defines the number of related pairs that increase in the ambient
linear order. Directed graphs and other finite relations can share this
statistic without introducing an object-specific copy.
-/

@[expose] public section

open Finset

namespace Rel

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The number of pairs `u < v` for which `r u v` holds. -/
def ascentCount (r : α → α → Prop) [DecidableRel r] : ℕ :=
  ∑ v : α, (univ.filter fun u : α => u < v ∧ r u v).card

end Rel
