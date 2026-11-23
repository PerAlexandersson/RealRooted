/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Grouping products with finite multiplicities

A convergent product over finite multiplicity fibers is the convergent product
of the corresponding natural powers. The ambient monoid may contain zero.
-/

public section

/-- Grouping identical factors in each finite multiplicity fiber. -/
theorem HasProd.sigma_fin_const {ι M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [RegularSpace M] {a : ι → M} {m : ι → ℕ} {p : M}
    (h : HasProd (fun j : Σ i, Fin (m i) ↦ a j.1) p) :
    HasProd (fun i ↦ a i ^ m i) p := by
  apply h.sigma
  intro i
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    hasProd_fintype (fun _ : Fin (m i) ↦ a i)
