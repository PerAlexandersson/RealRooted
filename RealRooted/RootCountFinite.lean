import Mathlib.Data.Multiset.Filter
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite Root-Count Reductions

This file contains polynomial-free finite-count lemmas used by the issue #42
root-continuity route.  The intended use is: once continuity accounts for all
finite roots of the lower-degree endpoint on both sides of a non-root threshold,
and the root-sum argument supplies one extra root on the lower side, the upper
root counts are forced to agree by cardinality.
-/

namespace Multiset

/-- A finite real multiset has positive distance from any real number it does
not contain. -/
theorem exists_pos_le_abs_sub_of_forall_mem_ne
    (s : Multiset ℝ) (x : ℝ) (hx : ∀ r ∈ s, r ≠ x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ s, ε ≤ |r - x| := by
  classical
  induction s using Multiset.induction with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | cons a s ih =>
      obtain ⟨ε, hε, hεs⟩ := ih (by simp_all)
      exact ⟨min ε |a - x|, by grind, by simp_all⟩

/-- A finite real multiset has positive distance from any absent real number. -/
theorem exists_pos_le_abs_sub_of_not_mem
    (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ s, ε ≤ |r - x| :=
  exists_pos_le_abs_sub_of_forall_mem_ne s x fun r hr h =>
    hx (by simp_all)

/-- A finite real multiset has a strict lower guard. -/
private theorem exists_lt_forall_mem_lt (s : Multiset ℝ) :
    ∃ B : ℝ, ∀ r ∈ s, B < r := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      obtain ⟨B, hB⟩ := ih
      exact ⟨min (a - 1) B, by simp_all⟩

/--
Choose a guard below all elements of a finite multiset and one positive
separation radius from both the guard and a fixed absent threshold.

In the issue #42 route, `x` is the non-root threshold, `B` is the bound below
which the escaping succ-degree root lies, and `ε` is the common radius used by
the finite-root matching argument.
-/
theorem exists_guard_le_and_pos_le_abs_sub
    (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    ∃ B ε : ℝ, B ≤ x ∧ 0 < ε ∧
      (∀ r ∈ s, B < r) ∧
      (∀ r ∈ s, ε ≤ |r - x|) ∧
      (∀ r ∈ s, ε ≤ |r - B|) := by
  obtain ⟨B₀, hB₀⟩ := exists_lt_forall_mem_lt s
  let B : ℝ := min B₀ x - 1
  have hB_le_x : B ≤ x := by grind
  have hB_lt_B₀ : B < B₀ := by grind
  have : ∀ r ∈ s, B < r := by grind
  have hB_not_mem : B ∉ s := by grind
  obtain ⟨εx, hεx_pos, hεx⟩ := exists_pos_le_abs_sub_of_not_mem s hx
  obtain ⟨εB, hεB_pos, hεB⟩ := exists_pos_le_abs_sub_of_not_mem s hB_not_mem
  grind

/-- If `r` is separated from a threshold `x` and lies above `x`, then every
point closer to `r` than the separation margin also lies above `x`. -/
private theorem threshold_lt_of_abs_sub_lt_of_threshold_lt
    {x r q ε : ℝ} (hxr : x < r) (hsep : ε ≤ |r - x|)
    (hclose : |q - r| < ε) :
    x < q := by grind

/-- If a submultiset consists only of elements satisfying a predicate, then
its cardinality is bounded by the corresponding filtered count of the ambient
multiset. -/
private theorem card_le_card_filter_of_le_of_forall_mem
    {α : Type*} {p : α → Prop} [DecidablePred p] {s t : Multiset α}
    (hst : s ≤ t) (hs : ∀ a ∈ s, p a) :
    s.card ≤ (t.filter p).card :=
  Multiset.card_le_card ((Multiset.le_filter).mpr ⟨hst, hs⟩)

/-- Extract a submultiset of any prescribed cardinality not exceeding the
ambient multiset cardinality. -/
theorem exists_le_card_eq_of_le_card {α : Type*} (t : Multiset α) {n : ℕ}
    (h : n ≤ t.card) :
    ∃ u : Multiset α, u ≤ t ∧ u.card = n := by
  induction t using Multiset.induction generalizing n with
  | empty => simp_all
  | cons a t ih =>
      cases n with
      | zero => exact ⟨0, zero_le _, by simp⟩
      | succ n =>
          have hn : n ≤ t.card := by simpa using h
          obtain ⟨u, hut, hcard⟩ := ih hn
          exact ⟨a ::ₘ u, Multiset.cons_le_cons a hut, by simp [hcard]⟩

/-- Filter cardinality is monotone along a `Multiset.Rel` matching. -/
private theorem card_filter_le_of_rel {α β : Type*} {r : α → β → Prop}
    {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    {s : Multiset α} {t : Multiset β}
    (h : Multiset.Rel r s t)
    (hpq : ∀ a ∈ s, ∀ b ∈ t, r a b → p a → q b) :
    (s.filter p).card ≤ (t.filter q).card := by
  induction h with
  | zero => simp
  | @cons a b s t hab _ ih =>
      have hpq_tail : ∀ a ∈ s, ∀ b ∈ t, r a b → p a → q b := by grind
      by_cases ha : p a
      · have hb : q b := hpq a (by simp) b (by simp) hab ha
        simpa [ha, hb] using Nat.succ_le_succ (ih hpq_tail)
      · by_cases hb : q b
        · simpa [ha, hb] using (ih hpq_tail).trans (Nat.le_succ _)
        · simpa [ha, hb] using ih hpq_tail

/-- A filter by a disjunction has cardinality bounded by the sum of the two
filtered cardinalities. -/
private theorem card_filter_or_le_add {α : Type*} {p q : α → Prop}
    [DecidablePred p] [DecidablePred q] (s : Multiset α) :
    (s.filter (fun a => p a ∨ q a)).card ≤
      (s.filter p).card + (s.filter q).card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq] <;> lia

/-- If the only element of `s` in the interval `(a, b]` is a point `c` that
appears exactly once in `s`, then that interval has cardinality one. -/
theorem card_filter_interval_eq_one_of_count_eq_one_of_forall_mem_eq
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b c : α}
    (hac : a < c) (hcb : c ≤ b) (hcount : s.count c = 1)
    (hmem : ∀ z ∈ s, a < z → z ≤ b → z = c) :
    (s.filter (fun z => a < z ∧ z ≤ b)).card = 1 := by
  have hfilter :
      s.filter (fun z => a < z ∧ z ≤ b) = s.filter (fun z => z = c) := by
    apply Multiset.filter_congr
    intro z hz
    constructor
    · intro hzI
      exact hmem z hz hzI.1 hzI.2
    · rintro rfl
      exact ⟨hac, hcb⟩
  rw [hfilter]
  simpa [hcount, eq_comm] using (Multiset.count_eq_card_filter_eq s c).symm

/--
A target cluster in a small ball around `r` matches a source cluster consisting
only of copies of `r`, provided the two clusters have the same cardinality.

This is the finite multiplicity atom for the issue #42 root-continuity route:
after the analytic argument extracts the right number of perturbed roots in a
neighborhood of a repeated endpoint root, this turns that local count into a
`Multiset.Rel` proximity match.
-/
theorem rel_abs_sub_lt_of_repeated_left
    {s u : Multiset ℝ} {r δ : ℝ}
    (hs : ∀ x ∈ s, x = r)
    (hu : ∀ q ∈ u, |q - r| < δ)
    (hcard : s.card = u.card) :
    Multiset.Rel (fun x q => |q - x| < δ) s u :=
  Multiset.rel_of_forall (by grind) hcard

/-- A proximity matching preserves weak-lower threshold counts when the source
multiset is separated from the threshold. -/
theorem card_filter_le_le_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (s.filter (fun r ↦ r ≤ x)).card ≤
      (t.filter (fun q ↦ q ≤ x)).card :=
  card_filter_le_of_rel hmatch (by grind)

/-- A proximity matching preserves strict-upper threshold counts when the source
multiset is separated from the threshold. -/
theorem card_filter_gt_le_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (s.filter (fun r ↦ x < r)).card ≤
      (t.filter (fun q ↦ x < q)).card :=
  card_filter_le_of_rel hmatch (by grind)

/-- A proximity matching preserves strict-upper threshold counts when only the
source roots already above the threshold are required to be separated from the
threshold. -/
theorem card_filter_gt_le_of_rel_abs_sub_lt_of_gt_sep
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, x < r → δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (s.filter (fun r ↦ x < r)).card ≤
      (t.filter (fun q ↦ x < q)).card :=
  card_filter_le_of_rel hmatch (by grind)

/-- Under a proximity matching, target roots above a threshold can only come
from source roots above that threshold or from source roots exactly at the
threshold, provided all other source roots are separated from the threshold. -/
private theorem card_filter_gt_le_add_card_filter_eq_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, r ≠ x → δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (t.filter (fun q => x < q)).card ≤
      (s.filter (fun r => x < r)).card +
        (s.filter (fun r => r = x)).card := by
  have hmatch_flip :
      Multiset.Rel (fun q r => |q - r| < δ) t s :=
    (Multiset.rel_flip).2 hmatch
  have hle_or :
      (t.filter (fun q => x < q)).card ≤
        (s.filter (fun r => x < r ∨ r = x)).card := by
    refine card_filter_le_of_rel hmatch_flip ?_
    grind
  exact le_trans hle_or (card_filter_or_le_add s)

/-- If a proximity-matched source multiset has a single element at the
threshold, then the target strict-upper count is at most one larger than the
source strict-upper count. -/
theorem card_filter_gt_le_add_one_of_rel_abs_sub_lt_of_count_eq_one
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, r ≠ x → δ ≤ |r - x|)
    (hx : s.count x = 1)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (t.filter (fun q => x < q)).card ≤
      (s.filter (fun r => x < r)).card + 1 := by
  simpa [← Multiset.count_eq_card_filter_eq, hx, eq_comm] using
    card_filter_gt_le_add_card_filter_eq_of_rel_abs_sub_lt hsep hmatch

/-- The weak-lower and strict-upper filters partition a finite multiset over a
linear order. -/
theorem card_filter_le_add_card_filter_gt {α : Type*} [LinearOrder α]
    (s : Multiset α) (x : α) :
    (s.filter (fun r => r ≤ x)).card + (s.filter (fun r => x < r)).card =
      s.card := by
  simpa [Multiset.card_add, not_le] using
    congrArg Multiset.card (Multiset.filter_add_not (fun r => r ≤ x) s)

/--
If `t` has one more element than `s`, at least as many strict-upper elements,
and strictly more weak-lower elements, then the strict-upper counts agree.

In the issue #42 route, continuity gives the weak-lower increase, and the
escaping root makes it strict.
-/
private theorem card_filter_gt_eq_of_filter_le_lt
    {α : Type*} [LinearOrder α] {s t : Multiset α} {x : α}
    (hgt : (s.filter (fun r => x < r)).card ≤
      (t.filter (fun r => x < r)).card)
    (hle : (s.filter (fun r => r ≤ x)).card <
      (t.filter (fun r => r ≤ x)).card)
    (hcard : t.card = s.card + 1) :
    (t.filter (fun r => x < r)).card =
      (s.filter (fun r => x < r)).card := by
  have hs := card_filter_le_add_card_filter_gt s x
  have ht := card_filter_le_add_card_filter_gt t x
  lia

/--
Assembly form for a proximity matching plus one escaped root.

Assume the roots in `s` are matched to roots in `u`, with every matched point
closer than the separation of `s` from the threshold `x`.  If `t` contains all
of `u` plus one extra element `a ≤ x`, and `t` has exactly one more element
than `s`, then the strict-upper counts of `s` and `t` are equal.

In the #42 route, `s` is the lower endpoint root multiset, `u` is the finite
root cluster of the small positive pencil, `t` is the full pencil root
multiset, and `a` is the root escaping to the left.
-/
private theorem card_filter_gt_eq_of_rel_with_extra_le
    {s u t : Multiset ℝ} {x δ a : ℝ}
    (hsep : ∀ r ∈ s, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s u)
    (hextra : a ::ₘ u ≤ t)
    (ha : a ≤ x)
    (hcard : t.card = s.card + 1) :
    (t.filter (fun q => x < q)).card =
      (s.filter (fun r => x < r)).card := by
  refine card_filter_gt_eq_of_filter_le_lt ?_ ?_ hcard
  · exact (card_filter_gt_le_of_rel_abs_sub_lt hsep hmatch).trans
      (Multiset.card_le_card (Multiset.filter_le_filter _
        ((Multiset.le_cons_self u a).trans hextra)))
  · have hsu := card_filter_le_le_of_rel_abs_sub_lt hsep hmatch
    have hfilter_extra : a ::ₘ (u.filter (fun q => q ≤ x)) ≤ t :=
      (Multiset.cons_le_cons a (Multiset.filter_le _ u)).trans hextra
    have hcard_extra : (u.filter (fun q => q ≤ x)).card + 1 ≤
        (t.filter (fun q => q ≤ x)).card := by
      simpa using card_le_card_filter_of_le_of_forall_mem hfilter_extra (by simp_all)
    grind

/-- A proximity matching keeps the matched roots above any guard threshold
which is separated from all source roots below them. -/
private theorem forall_mem_right_threshold_lt_of_rel_abs_sub_lt
    {s u : Multiset ℝ} {B δ : ℝ}
    (hB : ∀ r ∈ s, B < r)
    (hsep : ∀ r ∈ s, δ ≤ |r - B|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s u) :
    ∀ q ∈ u, B < q := by
  induction hmatch with
  | zero => simp
  | @cons r q s u hclose _ ih =>
      intro y hy
      simp only [Multiset.mem_cons] at hy
      rcases hy with rfl | hy
      · exact threshold_lt_of_abs_sub_lt_of_threshold_lt
          (hB r (by simp)) (hsep r (by simp)) hclose
      · simp_all

/--
Finite assembly form with an escaped root separated below the finite cluster.

The matching accounts for every source root in `s` by a nearby root in `u`.
If all matched roots are forced above a guard bound `B`, while an extra root
`a` of `t` lies below `B ≤ x`, then `a` is genuinely extra and the strict-upper
counts at `x` agree.
-/
theorem card_filter_gt_eq_of_rel_with_escaped_extra
    {s u t : Multiset ℝ} {x B δ a : ℝ}
    (hsep_x : ∀ r ∈ s, δ ≤ |r - x|)
    (hB : ∀ r ∈ s, B < r)
    (hsep_B : ∀ r ∈ s, δ ≤ |r - B|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s u)
    (hu : u ≤ t) (ha_mem : a ∈ t) (ha_lt : a < B) (hBx : B ≤ x)
    (hcard : t.card = s.card + 1) :
    (t.filter (fun q => x < q)).card =
      (s.filter (fun r ↦ x < r)).card := by
  have hcluster : ∀ q ∈ u, B < q :=
    forall_mem_right_threshold_lt_of_rel_abs_sub_lt hB hsep_B hmatch
  have ha_not_mem : a ∉ u := by grind
  exact card_filter_gt_eq_of_rel_with_extra_le hsep_x hmatch
    ((Multiset.cons_le_of_notMem ha_not_mem).mpr ⟨ha_mem, hu⟩)
    (le_trans (le_of_lt ha_lt) hBx) hcard

end Multiset
