module

public import RealRooted.EffectiveBKW.PairExpansion
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RealRooted.EffectiveBKW.Phase
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closing the effective BKW root count

Alternating samples yield distinct roots in their open gaps. A finite set of roots
whose cardinality reaches the degree closes the count, including several disjoint
regions or additional exterior roots supplied by sign data.

The main theorem `PairExpansion.splits_nodup_forall_ge` is a general form of the argument in
E. Torres, arXiv:2611.22110 (Prop. 5.7 and Thm. 7.1: domination of the nearest
conjugate pair at the phase extrema), with an explicit domination cutoff.
-/

public section

open Set

namespace RealRooted.EffectiveBKW

/-- Two successive integer-signed positive values have opposite signs. -/
theorem mul_neg_of_alternating {x y : ℝ} (k : ℤ)
    (hx : 0 < (-1 : ℝ) ^ k * x) (hy : 0 < (-1 : ℝ) ^ (k + 1) * y) :
    x * y < 0 := by
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    nlinarith [sq_abs ((-1 : ℝ) ^ k), show |(-1 : ℝ) ^ k| = 1 by simp]
  rw [zpow_add₀ (by norm_num), zpow_one, mul_neg_one] at hy
  have hprod := mul_pos hx hy
  nlinarith

/-- Reversing a decreasing alternating grid gives the usual increasing sign grid. -/
theorem eval_mul_eval_rev_neg {p : Polynomial ℝ} {K : ℕ} {L : ℤ}
    (s : Fin (K + 1) → ℝ)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ (L + (j.val : ℤ)) * p.eval (s j))
    (i : Fin K) :
    p.eval (s i.castSucc.rev) * p.eval (s i.succ.rev) < 0 := by
  let j : Fin K := i.rev
  have hj₁ : i.succ.rev = j.castSucc := by ext; simp [j, Fin.rev]
  have hj₂ : i.castSucc.rev = j.succ := by ext; simp [j, Fin.rev]; lia
  rw [hj₁, hj₂, mul_comm]
  apply mul_neg_of_alternating (L + (j.val : ℤ)) (hsign j.castSucc)
  convert hsign j.succ using 1; simp [Nat.cast_add, add_assoc]

/-- A decreasing alternating grid exhibits `K` distinct roots in its open gaps.
This statement does not require any degree bound. -/
theorem exists_roots_of_strictAnti_alternating {p : Polynomial ℝ} {J : Set ℝ}
    {K : ℕ} {L : ℤ} (hJ : OrdConnected J)
    (s : Fin (K + 1) → ℝ) (hs : StrictAnti s) (hmem : ∀ j, s j ∈ J)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ (L + (j.val : ℤ)) * p.eval (s j)) :
    ∃ r : Finset ℝ, r.card = K ∧ ∀ z ∈ r, z ∈ J ∧ p.IsRoot z := by
  classical
  let x : Fin (K + 1) → ℝ := fun i ↦ s i.rev
  obtain ⟨r, hrmono, hr⟩ := Polynomial.exists_ordered_roots_of_strict_sign_changes
    x (fun _ _ hij ↦ hs (Fin.rev_strictAnti hij)) (eval_mul_eval_rev_neg s hsign)
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective (s := Finset.univ) hrmono.injective
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨hJ.out (hmem _) (hmem _) ⟨(hr i).1.le, (hr i).2.1.le⟩, (hr i).2.2⟩

/-- An increasing alternating grid closes the degree bound and localizes every root
to any order-connected region containing the grid. -/
theorem splits_nodup_of_alternating {p : Polynomial ℝ} {J : Set ℝ} {K : ℕ} {L : ℤ}
    (hJ : OrdConnected J) (hdegree : p.natDegree ≤ K)
    (s : Fin (K + 1) → ℝ) (hs : StrictMono s) (hmem : ∀ j, s j ∈ J)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ (L + (j.val : ℤ)) * p.eval (s j)) :
    p.natDegree = K ∧ p.Splits ∧ p.roots.Nodup ∧ ∀ z ∈ p.roots, z ∈ J := by
  have hp : p ≠ 0 := by
    intro hp
    have := hsign 0
    simp [hp] at this
  have hchange (i : Fin K) : p.eval (s i.castSucc) * p.eval (s i.succ) < 0 := by
    apply mul_neg_of_alternating (L + (i.val : ℤ)) (hsign i.castSucc)
    convert hsign i.succ using 1; simp [Nat.cast_add, add_assoc]
  obtain ⟨hdeg, hsplit, hnodup, hroots⟩ :=
    Polynomial.splits_nodup_roots_of_strict_sign_changes hp hdegree s hs hchange
  refine ⟨hdeg, hsplit, hnodup, fun z hz ↦ ?_⟩
  exact hJ.out (hmem 0) (hmem (Fin.last K)) (Ioo_subset_Icc_self (hroots z hz))

/-- The decreasing-grid version used by phase crossings. -/
theorem splits_nodup_of_strictAnti_alternating {p : Polynomial ℝ} {J : Set ℝ}
    {K : ℕ} {L : ℤ} (hJ : OrdConnected J) (hdegree : p.natDegree ≤ K)
    (s : Fin (K + 1) → ℝ) (hs : StrictAnti s) (hmem : ∀ j, s j ∈ J)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ (L + (j.val : ℤ)) * p.eval (s j)) :
    p.natDegree = K ∧ p.Splits ∧ p.roots.Nodup ∧ ∀ z ∈ p.roots, z ∈ J := by
  have hp : p ≠ 0 := by
    intro hp
    have := hsign 0
    simp [hp] at this
  let x : Fin (K + 1) → ℝ := fun i ↦ s i.rev
  have hx : StrictMono x := fun _ _ hij ↦ hs (Fin.rev_strictAnti hij)
  obtain ⟨hdeg, hsplit, hnodup, hroots⟩ :=
    Polynomial.splits_nodup_roots_of_strict_sign_changes hp hdegree x hx
      (eval_mul_eval_rev_neg s hsign)
  refine ⟨hdeg, hsplit, hnodup, fun z hz ↦ ?_⟩
  exact hJ.out (hmem _) (hmem _) (Ioo_subset_Icc_self (hroots z hz))

/-- A finite set of distinct real roots reaching the degree accounts for every root.
This form combines arbitrary interior and exterior root certificates. -/
theorem splits_nodup_of_card_roots_ge {p : Polynomial ℝ} (hp : p ≠ 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s, p.IsRoot x) (hdegree : p.natDegree ≤ s.card) :
    p.Splits ∧ p.roots.Nodup ∧ p.roots.toFinset = s := by
  classical
  have hsub : s ⊆ p.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hs x hx))
  have h₁ := Finset.card_le_card hsub
  have h₂ := Multiset.toFinset_card_le p.roots
  have h₃ := Polynomial.card_roots' p
  have hcard : p.roots.card = p.natDegree := by lia
  have hset : p.roots.toFinset.card = p.roots.card := by lia
  refine ⟨Polynomial.splits_iff_card_roots.mpr hcard,
    Multiset.toFinset_card_eq_card_iff_nodup.mp hset, ?_⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by lia)).symm

/-- Disjoint root regions close a degree budget by adding their cardinalities. -/
theorem splits_nodup_of_disjoint_roots {p : Polynomial ℝ} (hp : p ≠ 0)
    (s t : Finset ℝ) (hst : Disjoint s t)
    (hs : ∀ x ∈ s, p.IsRoot x) (ht : ∀ x ∈ t, p.IsRoot x)
    (hdegree : p.natDegree ≤ s.card + t.card) : p.Splits ∧ p.roots.Nodup := by
  classical
  have hu : ∀ x ∈ s ∪ t, p.IsRoot x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hs x hx
    · exact ht x hx
  exact (splits_nodup_of_card_roots_ge hp (s ∪ t) hu
    (by simpa only [Finset.card_union_of_disjoint hst] using hdegree)).imp_right And.left

namespace PairExpansion

variable {P : ℕ → Polynomial ℝ} {J : Set ℝ} (h : PairExpansion P J)

open scoped Classical in
/-- Phase crossings give at least `K` distinct roots in the domain, before any
comparison with the degree or addition of exterior sign changes. -/
theorem le_card_roots (hJ : OrdConnected J) {n N K : ℕ} {L : ℤ}
    (hn : h.first ≤ n) (hd : h.Dom J N) (hN : N ≤ n)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ J)
    (hp : ∀ t ∈ J, (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos (φ t))
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (hlo : φ b < (L : ℝ) * Real.pi)
    (hhi : ((L : ℝ) + K) * Real.pi < φ a) :
    K ≤ ((P n).roots.toFinset.filter (fun t ↦ t ∈ J)).card := by
  classical
  obtain ⟨s, hs, hmem, hsign⟩ := h.exists_alternating hJ hn hd hN hc hp ha hb hab hlo hhi
  have hne : P n ≠ 0 := by
    intro heq
    have := hsign 0
    simp [heq] at this
  obtain ⟨r, hr, hroot⟩ := exists_roots_of_strictAnti_alternating hJ s hs hmem hsign
  rw [← hr]
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr (hroot z hz).2),
      (hroot z hz).1⟩

/-- Effective BKW with a closed degree budget. The hypotheses are exactly those of
`exists_alternating`, together with the degree bound. Every root is real, simple, and
in `J`. The caller supplies the continuous phase; no argument lift is postulated as a proof. -/
theorem splits_nodup (hJ : OrdConnected J) {n N K : ℕ} {L : ℤ}
    (hn : h.first ≤ n) (hd : h.Dom J N) (hN : N ≤ n)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ J)
    (hp : ∀ t ∈ J, (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos (φ t))
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (hlo : φ b < (L : ℝ) * Real.pi)
    (hhi : ((L : ℝ) + K) * Real.pi < φ a) (hdegree : (P n).natDegree ≤ K) :
    (P n).natDegree = K ∧ (P n).Splits ∧ (P n).roots.Nodup ∧
      ∀ z ∈ (P n).roots, z ∈ J := by
  obtain ⟨s, hs, hmem, hsign⟩ := h.exists_alternating hJ hn hd hN hc hp ha hb hab hlo hhi
  exact splits_nodup_of_strictAnti_alternating hJ hdegree s hs hmem hsign

/-- The order-two corollary needs no cutoff: the exact remainder vanishes. The first
valid expansion index and the caller's continuous phase and degree data remain explicit. -/
theorem splits_nodup_of_rest_eq_zero (hJ : OrdConnected J) {n K : ℕ} {L : ℤ}
    (hn : h.first ≤ n) (hr : ∀ k t, t ∈ J → h.rest k t = 0)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ J)
    (hp : ∀ t ∈ J, (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos (φ t))
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (hlo : φ b < (L : ℝ) * Real.pi)
    (hhi : ((L : ℝ) + K) * Real.pi < φ a) (hdegree : (P n).natDegree ≤ K) :
    (P n).natDegree = K ∧ (P n).Splits ∧ (P n).roots.Nodup ∧
      ∀ z ∈ (P n).roots, z ∈ J := by
  exact h.splits_nodup hJ hn (h.dom_of_rest_eq_zero (fun _ ht ↦ ht) hr)
    (Nat.zero_le n) hc hp ha hb hab hlo hhi hdegree

/-- A fixed domination cutoff proves every later row once its phase and degree data
are supplied. The phase, sample bounds, and degree budget may depend on the index. -/
theorem splits_nodup_forall_ge (hJ : OrdConnected J) (N : ℕ) (hfirst : h.first ≤ N)
    (hd : h.Dom J N) (K : ℕ → ℕ) (L : ℕ → ℤ) (φ : ℕ → ℝ → ℝ) (a b : ℕ → ℝ)
    (hc : ∀ n, N ≤ n → ContinuousOn (φ n) J)
    (hp : ∀ n, N ≤ n → ∀ t ∈ J, (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos (φ n t))
    (ha : ∀ n, N ≤ n → a n ∈ J) (hb : ∀ n, N ≤ n → b n ∈ J)
    (hab : ∀ n, N ≤ n → a n < b n)
    (hlo : ∀ n, N ≤ n → φ n (b n) < (L n : ℝ) * Real.pi)
    (hhi : ∀ n, N ≤ n → ((L n : ℝ) + K n) * Real.pi < φ n (a n))
    (hdegree : ∀ n, N ≤ n → (P n).natDegree ≤ K n) :
    ∀ n, N ≤ n → (P n).Splits ∧ (P n).roots.Nodup ∧
      ∀ z ∈ (P n).roots, z ∈ J := by
  intro n hn
  exact (h.splits_nodup hJ (hfirst.trans hn) hd hn (hc n hn) (hp n hn)
    (ha n hn) (hb n hn) (hab n hn) (hlo n hn) (hhi n hn) (hdegree n hn)).2

end PairExpansion
end RealRooted.EffectiveBKW
