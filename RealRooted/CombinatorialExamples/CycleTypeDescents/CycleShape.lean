/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CycleTypeDescents.Basic
public import RealRooted.CombinatorialExamples.LongCycleDescents.Content
import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
import Mathlib.Tactic

/-!
# Cycle lengths in the necklace correspondence

We refine the proved cutoff correspondence by counting the itinerary periods of every length.
A cycle of length `j` contributes `j` positions; a primitive necklace of length `j`
contributes the same number of rooted words. Thus the correspondence preserves cycle type,
not merely the minimum cycle length (Gessel--Reutenauer, 1993).
-/

public section

noncomputable section

open Finset

namespace RealRooted.CycleTypeDescents

open LongCycleDescents LongCycleDescents.Necklace LongCycleDescents.Words

private theorem period_signature_eq_card {n q : ℕ} {σ : Equiv.Perm (Fin n)}
    {x : Fin n → Fin q} (hx : Stable σ x) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ σ.cycleFactorsFinset) {i : Fin n} (hi : i ∈ c.support) :
    period (ofLex (signature σ x i)) = c.support.card := by
  have he : c = σ.cycleOf i :=
    (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c hc i).mpr hi
  have hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  rw [← hcycle.orderOf]
  apply Nat.dvd_antisymm
  · apply (period_dvd_iff_return hx i _).mpr
    rw [← Equiv.Perm.cycleOf_pow_apply_self, ← he, pow_orderOf_eq_one]
    rfl
  · apply orderOf_dvd_of_pow_eq_one
    apply (hcycle.pow_eq_one_iff' (Equiv.Perm.mem_support.mp hi)).mpr
    rw [he, Equiv.Perm.cycleOf_pow_apply_self]
    exact (period_dvd_iff_return hx i _).mp (dvd_refl _)

private def cyclePositionsEquiv {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : σ.support = univ) :
    (Σ c : σ.cycleFactorsFinset, (c.val.support : Finset (Fin n))) ≃ Fin n :=
  Equiv.ofBijective (fun z => z.2.val) (by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ he
      have hc := (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c.val c.property i).mpr
        i.property
      have hd := (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ d.val d.property j).mpr
        j.property
      change i.val = j.val at he
      have hcd : c = d := Subtype.ext (by rw [hc, hd, he])
      subst d
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext he))
    · intro i
      have hi : i ∈ σ.support := by rw [hσ]; exact mem_univ i
      let c : σ.cycleFactorsFinset := ⟨σ.cycleOf i,
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hi⟩
      refine ⟨⟨c, ⟨i, ?_⟩⟩, rfl⟩
      exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c.val c.property i).mp rfl)

/-- The number of positions of itinerary period `j` is `j` times the number of `j`-cycles. -/
theorem sum_period_signature {n q : ℕ} {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (hx : Stable σ x) (hσ : σ.support = univ) (j : ℕ) :
    (∑ i : Fin n, if period (ofLex (signature σ x i)) = j then 1 else 0) =
      j * σ.cycleType.count j := by
  classical
  rw [← (cyclePositionsEquiv σ hσ).sum_comp, Fintype.sum_sigma]
  calc
    _ = ∑ c : σ.cycleFactorsFinset, if c.val.support.card = j then j else 0 := by
      apply sum_congr rfl
      intro c _
      change (∑ i : c.val.support, if period (ofLex (signature σ x i.val)) = j then 1 else 0) = _
      have hp (i : c.val.support) := period_signature_eq_card hx c.property i.property
      simp_rw [hp]
      split <;> simp_all
    _ = j * σ.cycleType.count j := by
      have hc : (∑ c : σ.cycleFactorsFinset, if c.val.support.card = j then 1 else 0) =
          Fintype.card {c : σ.cycleFactorsFinset // c.val.support.card = j} := by
        simp [Fintype.card_subtype]
      rw [Equiv.Perm.CycleType.count_def, ← hc, mul_sum]
      apply sum_congr rfl
      intro c _
      split <;> simp_all

/-- Lifting the necklace content of an original compatible pair recovers its itinerary counts. -/
theorem liftContent_originalNecklaceEquiv {n q k : ℕ} (u : AllowedCompatible n q k) :
    liftContent ((originalNecklaceEquiv n q k u).val) = frequency (signature u.val.val.1
      u.val.val.2) := by
  exact lift_descend (cutoffMassEquiv n q k u)

/-- Period counts read from a content lift count every necklace once per rooted position. -/
theorem sum_period_liftContent {n q : ℕ} (a : Types n q → ℕ) (j : ℕ) :
    (∑ s : Key n q, if period (ofLex s) = j then liftContent a s else 0) =
      j * ∑ N : Types n q, if N.1.val = j then a N else 0 := by
  classical
  rw [← (rootEquiv n q).sum_comp]
  simp only [rootEquiv, Equiv.ofBijective_apply, period_repeatRoot, liftContent_root]
  have he := sum_over_types (fun N : Types n q => if N.1.val = j then a N else 0)
  change (∑ u : Rooted n q, if u.1.val = j then a (cycleTypeOfRoot u) else 0) = _
  change (∑ u : Rooted n q, if u.1.val = j then a (cycleTypeOfRoot u) else 0) = _ at he
  rw [he, mul_sum]
  apply sum_congr rfl
  intro N _
  split <;> simp_all

/-- The existing Gessel--Reutenauer bijection preserves each cycle-length multiplicity. -/
theorem count_originalNecklaceEquiv {n q : ℕ} (u : AllowedCompatible n q 2)
    {j : ℕ} (hj : 0 < j) :
    (∑ N : Types n q, if N.1.val = j then (originalNecklaceEquiv n q 2 u).val N else 0) =
      u.val.val.1.cycleType.count j := by
  classical
  apply Nat.eq_of_mul_eq_mul_left hj
  rw [← sum_period_liftContent, liftContent_originalNecklaceEquiv]
  have he := Fintype.sum_fiberwise' (signature u.val.val.1 u.val.val.2)
    (fun s : Key n q => if period (ofLex s) = j then 1 else 0)
  have hf : (∑ s : Key n q, if period (ofLex s) = j then
      frequency (signature u.val.val.1 u.val.val.2) s else 0) =
      ∑ i : Fin n, if period (ofLex (signature u.val.val.1 u.val.val.2 i)) = j then 1 else 0 := by
    rw [← he]
    apply sum_congr rfl
    intro s _
    simp only [frequency, Nat.card_eq_fintype_card]
    split <;> simp_all
  rw [hf]
  exact sum_period_signature u.val.property
    (LongCycleDescents.support_univ_of_allowed u.property (by decide)) j

end RealRooted.CycleTypeDescents
