/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite cardinality from unique hits under equivalences

This file provides a reusable counting principle for a finite family of
equivalences: if every point has a unique parameter whose image satisfies a
predicate, then the ambient cardinality is the parameter cardinality times the
cardinality of the predicate subtype.
-/

public section

namespace Fintype

open scoped BigOperators

/-- A finite family of equivalences with a unique predicate-hitting parameter
partitions the ambient finite type into equally sized predicate fibers. -/
theorem card_eq_card_mul_card_subtype_of_existsUnique_equiv
    (X C : Type*) [Fintype X] [Fintype C] (act : C → X ≃ X)
    (P : X → Prop) [DecidablePred P]
    (h : ∀ x : X, ∃! c : C, P (act c x)) :
    Fintype.card X = Fintype.card C * Fintype.card {x : X // P x} := by
  classical
  have hc (x : X) : Fintype.card {c : C // P (act c x)} = 1 :=
    (Fintype.card_subtype _).trans ((existsUnique_iff_card_one _).mp (h x))
  calc
    Fintype.card X = ∑ x : X, Fintype.card {c : C // P (act c x)} := by simp [hc]
    _ = ∑ c : C, Fintype.card {x : X // P (act c x)} := by
      simp only [Fintype.card_subtype, Finset.card_filter]
      exact Finset.sum_comm
    _ = ∑ _c : C, Fintype.card {x : X // P x} := by
      apply Finset.sum_congr rfl
      intro c _
      exact Fintype.card_congr (act c).subtypeEquivOfSubtype
    _ = Fintype.card C * Fintype.card {x : X // P x} := by simp

end Fintype
