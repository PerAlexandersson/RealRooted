/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.Linarith

/-!
# Polynomial roots from finite strict sign changes

A degree-`n` real polynomial that changes sign across `n` consecutive
intervals has one distinct root in each interval, and no other roots.
This is the module-compatible version of the interval argument used in
`RealRooted.RootCounting.SignChanges`; its proof uses Mathlib's intermediate
value theorem and root-count bound directly.
-/

public noncomputable section

open Set Finset

namespace Polynomial

/-- Strict sign changes at an increasing grid select one root in every open
gap. The selected roots inherit the grid order. -/
theorem exists_ordered_roots_of_strict_sign_changes {p : ℝ[X]} {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hsign : ∀ i : Fin n, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    ∃ r : Fin n → ℝ, StrictMono r ∧
      ∀ i, x i.castSucc < r i ∧ r i < x i.succ ∧ p.IsRoot (r i) := by
  have hgap (i : Fin n) :
      ∃ z : ℝ, x i.castSucc < z ∧ z < x i.succ ∧ p.IsRoot z := by
    have hab : x i.castSucc ≤ x i.succ := (hx i.castSucc_lt_succ).le
    rcases (mul_neg_iff.mp (hsign i)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨z, hz, hzero⟩ :=
        intermediate_value_Ioo' hab p.continuous.continuousOn
          (show (0 : ℝ) ∈ Ioo (p.eval (x i.succ)) (p.eval (x i.castSucc)) from
            ⟨hb, ha⟩)
      exact ⟨z, hz.1, hz.2, hzero⟩
    · obtain ⟨z, hz, hzero⟩ :=
        intermediate_value_Ioo hab p.continuous.continuousOn
          (show (0 : ℝ) ∈ Ioo (p.eval (x i.castSucc)) (p.eval (x i.succ)) from
            ⟨ha, hb⟩)
      exact ⟨z, hz.1, hz.2, hzero⟩
  let r : Fin n → ℝ := fun i => (hgap i).choose
  have hr (i : Fin n) :
      x i.castSucc < r i ∧ r i < x i.succ ∧ p.IsRoot (r i) :=
    (hgap i).choose_spec
  refine ⟨r, ?_, hr⟩
  intro i j hij
  have hle : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij
  exact ((hr i).2.1.trans_le (hx.monotone hle)).trans (hr j).1

/-- A finite grid with strict sign changes accounts for every root of a
nonzero polynomial of degree at most the number of gaps. In particular all
its roots are simple and lie strictly between the outer grid points. -/
theorem splits_nodup_roots_of_strict_sign_changes {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0) (hdegree : p.natDegree ≤ n)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hsign : ∀ i : Fin n, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    p.natDegree = n ∧ p.Splits ∧ p.roots.Nodup ∧
      ∀ z ∈ p.roots, x 0 < z ∧ z < x (Fin.last n) := by
  classical
  obtain ⟨r, hrmono, hr⟩ :=
    exists_ordered_roots_of_strict_sign_changes x hx hsign
  let s : Finset ℝ := univ.image r
  have hs_card : s.card = n := by
    simpa only [s, card_univ, Fintype.card_fin] using
      (Finset.card_image_of_injective (s := (univ : Finset (Fin n))) hrmono.injective)
  have hs_sub : s ⊆ p.roots.toFinset := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (hr i).2.2)
  have hcount : p.roots.card = n := by
    have h₁ : n ≤ p.roots.toFinset.card := by
      simpa only [hs_card] using Finset.card_le_card hs_sub
    have h₂ : p.roots.toFinset.card ≤ p.roots.card :=
      Multiset.toFinset_card_le _
    have h₃ : p.roots.card ≤ p.natDegree := card_roots' p
    lia
  have hsetCard : p.roots.toFinset.card = p.roots.card := by
    have h₁ : n ≤ p.roots.toFinset.card := by
      simpa only [hs_card] using Finset.card_le_card hs_sub
    exact Nat.le_antisymm (Multiset.toFinset_card_le _) (by lia)
  have hs_eq : s = p.roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le hs_sub
    lia
  have hroot_degree : p.roots.card ≤ p.natDegree := card_roots' p
  refine ⟨by lia, (splits_iff_card_roots).mpr (by lia),
    Multiset.toFinset_card_eq_card_iff_nodup.mp hsetCard, ?_⟩
  intro z hz
  have hzs : z ∈ s := by rw [hs_eq]; exact Multiset.mem_toFinset.mpr hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzs
  constructor
  · exact (hx.monotone (Fin.zero_le i.castSucc)).trans_lt (hr i).1
  · exact (hr i).2.1.trans_le (hx.monotone (Fin.le_last i.succ))

end Polynomial
