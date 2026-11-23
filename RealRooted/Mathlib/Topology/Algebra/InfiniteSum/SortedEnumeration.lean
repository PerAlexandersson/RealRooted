/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Sort
import TauCeti.Order.Northcott.Enumeration

/-!
# Decreasing enumerations of summable positive families

Injective positive summable families have decreasing enumerations. Infinite
families are indexed by the natural numbers; finite families retain a finite
index, including the empty case. The infinite enumeration uses Tau Ceti's
finite-sublevel enumeration in the dual order on the positive reals.
-/

public section

open Filter Set Topology

namespace Summable

/-- An infinite injective positive summable family can be enumerated in strictly
decreasing order, without assuming a countability instance on its index type. -/
theorem exists_equiv_strictAnti_comp {ι : Type*} [Infinite ι] {a : ι → ℝ}
    (hs : Summable a) (ha : ∀ i, 0 < a i) (hi : Function.Injective a) :
    ∃ e : ℕ ≃ ι, StrictAnti (a ∘ e) := by
  let b : ι → (Ioi (0 : ℝ))ᵒᵈ := fun i ↦ ⟨a i, ha i⟩
  have hfin : ∀ c : (Ioi (0 : ℝ))ᵒᵈ, {i | b i ≤ c}.Finite := by
    intro c
    have hev : ∀ᶠ i in cofinite, a i < ((OrderDual.ofDual c : Ioi (0 : ℝ)) : ℝ) :=
      hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (OrderDual.ofDual c).property)
    change {i | ((OrderDual.ofDual c : Ioi (0 : ℝ)) : ℝ) ≤ a i}.Finite
    simpa only [not_lt] using eventually_cofinite.mp hev
  obtain ⟨e, he⟩ := TauCeti.exists_equiv_monotone_comp_of_finite_setOf_le b hfin
  refine ⟨e, ?_⟩
  have hanti : Antitone (a ∘ e) := fun i j hij ↦ he hij
  exact hanti.strictAnti_of_injective (hi.comp e.injective)

end Summable

namespace Function.Injective

/-- Every finite injective real family has a strictly decreasing enumeration.
The result includes the empty family, represented by `Fin 0`. -/
theorem exists_fin_equiv_strictAnti_comp {ι : Type*} [Finite ι] {a : ι → ℝ}
    (hi : Function.Injective a) :
    ∃ n : ℕ, ∃ e : Fin n ≃ ι, StrictAnti (a ∘ e) := by
  classical
  let b : ι → ℝᵒᵈ := a
  have hb : Function.Injective b := hi
  let : Fintype (range b) := Fintype.ofFinite _
  let o : Fin (Fintype.card (range b)) ≃o range b :=
    Fintype.orderIsoFinOfCardEq (range b) rfl
  let e := o.toEquiv.trans (Equiv.ofInjective b hb).symm
  have he (i) : b (e i) = (o i : ℝᵒᵈ) := Equiv.apply_ofInjective_symm hb _
  refine ⟨_, e, ?_⟩
  intro i j hij
  change b (e i) < b (e j)
  rw [he, he]
  exact o.strictMono hij

end Function.Injective
