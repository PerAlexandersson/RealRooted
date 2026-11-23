/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Grouping real sums by fiber cardinalities

Repeated values contribute their natural multiplicities. Conversely,
summability of a nonnegative weighted sum recovers the repeated sum when
all fibers are finite. This isolates the grouping argument also used in
the project's Edrei--Thoma uniqueness proof.
-/

public section

/-- Grouping a summable real family that is constant on each fiber gives
the fiber cardinality times its common value. -/
theorem Summable.hasSum_natCard_fiber_mul {ι κ : Type*} {u : ι → κ} {g : κ → ℝ}
    (hs : Summable (fun i ↦ g (u i))) :
    HasSum (fun t ↦ (Nat.card {i // u i = t} : ℝ) * g t) (∑' i, g (u i)) := by
  let e := Equiv.sigmaFiberEquiv u
  have hF : Summable (fun x : Σ t, {i // u i = t} ↦ g (u (e x))) :=
    (e.summable_iff (f := fun i ↦ g (u i))).mpr hs
  have hsum : HasSum (fun x : Σ t, {i // u i = t} ↦ g (u (e x))) (∑' i, g (u i)) := by
    rw [← e.tsum_eq (fun i ↦ g (u i))]
    exact hF.hasSum
  refine hsum.sigma fun t ↦ ?_
  have hterm (i : {i // u i = t}) : g (u (e ⟨t, i⟩)) = g t := by
    change g (u i.val) = g t
    exact congrArg g i.property
  simpa only [hterm, tsum_const, nsmul_eq_mul] using (hF.sigma_factor t).hasSum

/-- A nonnegative sum with finite multiplicity fibers is summable if its
fiber-cardinality weighted sum is summable. The finite-fiber condition is
essential because `Nat.card` of an infinite fiber is zero. -/
theorem summable_of_natCard_fiber_mul {ι κ : Type*} {u : ι → κ} {g : κ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hfin : ∀ t, Set.Finite {i | u i = t})
    (hs : Summable (fun t ↦ (Nat.card {i // u i = t} : ℝ) * g t)) :
    Summable (fun i ↦ g (u i)) := by
  let e := Equiv.sigmaFiberEquiv u
  apply (e.summable_iff (f := fun i ↦ g (u i))).mp
  apply (summable_sigma_of_nonneg (fun i ↦ hg (u (e i)))).mpr
  constructor
  · intro t
    have := (hfin t).to_subtype
    exact Summable.of_finite
  · convert hs using 1
    funext t
    let : Fintype {i // u i = t} := (hfin t).fintype
    have hterm (i : {i // u i = t}) : g (u (e ⟨t, i⟩)) = g t := by
      change g (u i.val) = g t
      exact congrArg g i.property
    simp only [hterm, tsum_fintype,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
