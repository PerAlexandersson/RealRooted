import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Real.Basic
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
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp
  | cons a s ih =>
      have ha : a ≠ x := hx a (by simp)
      have hs : ∀ r ∈ s, r ≠ x := by
        intro r hr
        exact hx r (by simp [hr])
      obtain ⟨ε, hε, hεs⟩ := ih hs
      refine ⟨min ε |a - x|, ?_, ?_⟩
      · exact lt_min hε (abs_pos.mpr (sub_ne_zero.mpr ha))
      · intro r hr
        rw [Multiset.mem_cons] at hr
        rcases hr with rfl | hr
        · exact min_le_right _ _
        · exact le_trans (min_le_left _ _) (hεs r hr)

/-- A finite real multiset has positive distance from any absent real number. -/
theorem exists_pos_le_abs_sub_of_not_mem
    (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ s, ε ≤ |r - x| :=
  exists_pos_le_abs_sub_of_forall_mem_ne s x fun r hr h =>
    hx (by simpa [h] using hr)

/-- A finite real multiset has a strict lower guard. -/
private theorem exists_lt_forall_mem_lt (s : Multiset ℝ) :
    ∃ B : ℝ, ∀ r ∈ s, B < r := by
  classical
  induction s using Multiset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | cons a s ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨min (a - 1) B, ?_⟩
      have ha_guard : min (a - 1) B < a := by
        linarith [min_le_left (a - 1) B]
      intro r hr
      rw [Multiset.mem_cons] at hr
      rcases hr with rfl | hr
      · simp [ha_guard]
      · exact lt_of_le_of_lt (min_le_right (a - 1) B) (hB r hr)

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
  have hB_le_x : B ≤ x := by
    dsimp [B]
    linarith [min_le_right B₀ x]
  have hB_lt_B₀ : B < B₀ := by
    dsimp [B]
    linarith [min_le_left B₀ x]
  have hB : ∀ r ∈ s, B < r := by
    intro r hr
    exact lt_trans hB_lt_B₀ (hB₀ r hr)
  have hB_not_mem : B ∉ s := by
    intro h
    exact (lt_irrefl B) (hB B h)
  obtain ⟨εx, hεx_pos, hεx⟩ := exists_pos_le_abs_sub_of_not_mem s hx
  obtain ⟨εB, hεB_pos, hεB⟩ := exists_pos_le_abs_sub_of_not_mem s hB_not_mem
  refine ⟨B, min εx εB, hB_le_x, lt_min hεx_pos hεB_pos, hB, ?_, ?_⟩
  · intro r hr
    exact le_trans (min_le_left εx εB) (hεx r hr)
  · intro r hr
    exact le_trans (min_le_right εx εB) (hεB r hr)

/-- If `r` is separated from a threshold `x` and lies above `x`, then every
point closer to `r` than the separation margin also lies above `x`. -/
private theorem threshold_lt_of_abs_sub_lt_of_threshold_lt
    {x r q ε : ℝ} (hxr : x < r) (hsep : ε ≤ |r - x|)
    (hclose : |q - r| < ε) :
    x < q := by
  have hsep' : ε ≤ r - x := by
    simpa [abs_of_pos (sub_pos.mpr hxr)] using hsep
  have hq_lower : -ε < q - r := (abs_lt.mp hclose).1
  linarith

/-- If `r` is separated from a threshold `x` by a margin and lies at
or below `x`, then every point closer to `r` than the margin lies below `x`. -/
private theorem lt_threshold_of_abs_sub_lt_of_le_threshold
    {x r q ε : ℝ} (hrx : r ≤ x)
    (hsep : ε ≤ |r - x|) (hclose : |q - r| < ε) :
    q < x := by
  have hr_ne : r ≠ x := by
    intro h
    have hε : ε ≤ 0 := by simpa [h] using hsep
    have : |q - r| < 0 := lt_of_lt_of_le hclose hε
    exact not_lt_of_ge (abs_nonneg (q - r)) this
  have hrx_lt : r < x := lt_of_le_of_ne hrx hr_ne
  have hsep' : ε ≤ x - r := by
    simpa [abs_of_neg (sub_neg.mpr hrx_lt)] using hsep
  have hq_upper : q - r < ε := (abs_lt.mp hclose).2
  linarith

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
  | empty =>
      have hn : n = 0 := by simpa using h
      exact ⟨0, by simp [hn]⟩
  | cons a t ih =>
      cases n with
      | zero =>
          exact ⟨0, zero_le _, by simp⟩
      | succ n =>
          have hsucc : n.succ ≤ t.card.succ := by
            simpa using h
          have hn : n ≤ t.card := by
            exact Nat.succ_le_succ_iff.mp hsucc
          obtain ⟨u, hut, hcard⟩ := ih hn
          exact ⟨a ::ₘ u, Multiset.cons_le_cons a hut, by simp [hcard]⟩

/-- Filter cardinality is monotone along a `Multiset.Rel` matching. -/
private theorem card_filter_le_of_rel {α β : Type*} {r : α → β → Prop}
    {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    {s : Multiset α} {t : Multiset β}
    (h : Multiset.Rel r s t)
    (hpq : ∀ a ∈ s, ∀ b, r a b → p a → q b) :
    (s.filter p).card ≤ (t.filter q).card := by
  induction h with
  | zero => simp
  | @cons a b s t hab _ ih =>
      have hpq_tail : ∀ a ∈ s, ∀ b, r a b → p a → q b := by
        intro a ha b hab hpa
        exact hpq a (by simp [ha]) b hab hpa
      by_cases ha : p a
      · have hb : q b := hpq a (by simp) b hab ha
        simpa [ha, hb] using Nat.succ_le_succ (ih hpq_tail)
      · by_cases hb : q b
        · simpa [ha, hb] using le_trans (ih hpq_tail) (Nat.le_succ (filter q t).card)
        · simpa [ha, hb] using ih hpq_tail

/-- A filter by a disjunction has cardinality bounded by the sum of the two
filtered cardinalities. -/
private theorem card_filter_or_le_add {α : Type*} {p q : α → Prop}
    [DecidablePred p] [DecidablePred q] (s : Multiset α) :
    (s.filter (fun a => p a ∨ q a)).card ≤
      (s.filter p).card + (s.filter q).card := by
  induction s using Multiset.induction with
  | empty =>
      simp
  | cons a s ih =>
      by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq] <;> lia

/-- Filter cardinality monotonicity along a relation, with membership in both
matched multisets available to the predicate-transfer proof. -/
private theorem card_filter_le_of_rel_with_right_mem
    {α β : Type*} {r : α → β → Prop}
    {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    {s : Multiset α} {t : Multiset β}
    (h : Multiset.Rel r s t)
    (hpq : ∀ a ∈ s, ∀ b ∈ t, r a b → p a → q b) :
    (s.filter p).card ≤ (t.filter q).card := by
  induction h with
  | zero => simp
  | @cons a b s t hab _ ih =>
      have hpq_tail : ∀ a ∈ s, ∀ b ∈ t, r a b → p a → q b := by
        intro a ha b hb hab hpa
        exact hpq a (by simp [ha]) b (by simp [hb]) hab hpa
      by_cases ha : p a
      · have hb : q b := hpq a (by simp) b (by simp) hab ha
        simpa [ha, hb] using Nat.succ_le_succ (ih hpq_tail)
      · by_cases hb : q b
        · simpa [ha, hb] using le_trans (ih hpq_tail) (Nat.le_succ (filter q t).card)
        · simpa [ha, hb] using ih hpq_tail

/-- The equality-filter cardinality is the multiplicity of the filtered
element. -/
theorem card_filter_eq_eq_count {α : Type*} [DecidableEq α] (s : Multiset α)
    (x : α) :
    (s.filter (fun a => a = x)).card = s.count x := by
  induction s using Multiset.induction with
  | empty =>
      simp
  | cons a s ih =>
      by_cases hax : a = x
      · subst hax
        simp [ih, Multiset.count_cons_self]
      · simp [hax, ih, Multiset.count_cons_of_ne (Ne.symm hax)]

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
    Multiset.Rel (fun x q => |q - x| < δ) s u := by
  refine Multiset.rel_of_forall ?_ hcard
  intro x q hx hq
  have hx_eq : x = r := hs x hx
  simpa [hx_eq] using hu q hq

/-- A proximity matching preserves weak-lower threshold counts when the source
multiset is separated from the threshold. -/
theorem card_filter_le_le_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (s.filter (fun r => r ≤ x)).card ≤
      (t.filter (fun q => q ≤ x)).card := by
  refine card_filter_le_of_rel hmatch ?_
  intro r hr q hqr hrx
  exact le_of_lt (lt_threshold_of_abs_sub_lt_of_le_threshold hrx (hsep r hr) hqr)

/-- A proximity matching preserves strict-upper threshold counts when the source
multiset is separated from the threshold. -/
theorem card_filter_gt_le_of_rel_abs_sub_lt
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (s.filter (fun r => x < r)).card ≤
      (t.filter (fun q => x < q)).card := by
  refine card_filter_le_of_rel hmatch ?_
  intro r hr q hqr hxr
  exact threshold_lt_of_abs_sub_lt_of_threshold_lt hxr (hsep r hr) hqr

/-- A proximity matching preserves strict-upper threshold counts when only the
source roots already above the threshold are required to be separated from the
threshold. -/
theorem card_filter_gt_le_of_rel_abs_sub_lt_of_gt_sep
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep : ∀ r ∈ s, x < r → δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s t) :
    (s.filter (fun r => x < r)).card ≤
      (t.filter (fun q => x < q)).card := by
  refine card_filter_le_of_rel hmatch ?_
  intro r hr q hqr hxr
  exact threshold_lt_of_abs_sub_lt_of_threshold_lt hxr (hsep r hr hxr) hqr

/-- Under a proximity matching, target roots above a threshold can only come
from source roots above that threshold or from source roots exactly at the
threshold, provided all other source roots are separated from the threshold. -/
theorem card_filter_gt_le_add_card_filter_eq_of_rel_abs_sub_lt
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
    refine card_filter_le_of_rel_with_right_mem hmatch_flip ?_
    intro q _hq r hr hqr hxq
    by_cases hrx : r = x
    · exact Or.inr hrx
    · by_cases hxr : x < r
      · exact Or.inl hxr
      · have hr_le : r ≤ x := le_of_not_gt hxr
        have hq_lt : q < x :=
          lt_threshold_of_abs_sub_lt_of_le_threshold hr_le (hsep r hr hrx) hqr
        exact False.elim (not_lt_of_ge (le_of_lt hxq) hq_lt)
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
  have hle :=
    card_filter_gt_le_add_card_filter_eq_of_rel_abs_sub_lt hsep hmatch
  rw [card_filter_eq_eq_count, hx] at hle
  exact hle

/-- The weak-lower and strict-upper filters partition a finite multiset over a
linear order. -/
theorem card_filter_le_add_card_filter_gt {α : Type*} [LinearOrder α]
    (s : Multiset α) (x : α) :
    (s.filter (fun r => r ≤ x)).card + (s.filter (fun r => x < r)).card =
      s.card := by
  simpa [Multiset.card_add, not_le] using
    congrArg Multiset.card (Multiset.filter_add_not (fun r => r ≤ x) s)

/--
Finite count reduction for a one-root degree jump.

Assume `t` has one more element than `s`.  If `t` has at least all strict-upper
elements of `s`, and at least all weak-lower elements of `s` plus one more,
then the strict-upper counts are equal.  In the issue #42 route, the extra
weak-lower element is the root escaping to the left.
-/
private theorem card_filter_gt_eq_of_succ_le_filter_le
    {α : Type*} [LinearOrder α] {s t : Multiset α} {x : α}
    (hgt : (s.filter (fun r => x < r)).card ≤
      (t.filter (fun r => x < r)).card)
    (hle : (s.filter (fun r => r ≤ x)).card + 1 ≤
      (t.filter (fun r => r ≤ x)).card)
    (hcard : t.card = s.card + 1) :
    (t.filter (fun r => x < r)).card =
      (s.filter (fun r => x < r)).card := by
  have hs := card_filter_le_add_card_filter_gt s x
  have ht := card_filter_le_add_card_filter_gt t x
  lia

/--
Strict lower-count version of `card_filter_gt_eq_of_succ_le_filter_le`.

This is the form most directly consumed by the issue #42 escape argument: the
continuity part gives the weak lower bound, and the escaping root turns it into
a strict lower-count increase.
-/
private theorem card_filter_gt_eq_of_filter_le_lt
    {α : Type*} [LinearOrder α] {s t : Multiset α} {x : α}
    (hgt : (s.filter (fun r => x < r)).card ≤
      (t.filter (fun r => x < r)).card)
    (hle : (s.filter (fun r => r ≤ x)).card <
      (t.filter (fun r => r ≤ x)).card)
    (hcard : t.card = s.card + 1) :
    (t.filter (fun r => x < r)).card =
      (s.filter (fun r => x < r)).card :=
  card_filter_gt_eq_of_succ_le_filter_le hgt (Nat.succ_le_iff.mpr hle) hcard

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
  · have hsu : (s.filter (fun r => x < r)).card ≤
        (u.filter (fun q => x < q)).card :=
      card_filter_gt_le_of_rel_abs_sub_lt hsep hmatch
    have hut : u ≤ t := le_trans (Multiset.le_cons_self u a) hextra
    have hut_gt : (u.filter (fun q => x < q)).card ≤
        (t.filter (fun q => x < q)).card :=
      Multiset.card_le_card (Multiset.filter_le_filter (fun q => x < q) hut)
    exact le_trans hsu hut_gt
  · have hsu : (s.filter (fun r => r ≤ x)).card ≤
        (u.filter (fun q => q ≤ x)).card :=
      card_filter_le_le_of_rel_abs_sub_lt hsep hmatch
    have hfilter_extra : a ::ₘ (u.filter (fun q => q ≤ x)) ≤ t := by
      exact le_trans
        (Multiset.cons_le_cons a (Multiset.filter_le (fun q => q ≤ x) u))
        hextra
    have hcard_extra : (u.filter (fun q => q ≤ x)).card + 1 ≤
        (t.filter (fun q => q ≤ x)).card := by
      have hle_filter : (a ::ₘ (u.filter (fun q => q ≤ x))).card ≤
          (t.filter (fun q => q ≤ x)).card := by
        refine card_le_card_filter_of_le_of_forall_mem hfilter_extra ?_
        intro r hr
        rw [Multiset.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ha
        · exact (Multiset.mem_filter.mp hr).2
      simpa [Nat.add_comm] using hle_filter
    exact lt_of_le_of_lt hsu (Nat.lt_of_succ_le hcard_extra)

/--
Variant of `card_filter_gt_eq_of_rel_with_extra_le` for the form naturally
produced by the two analytic ingredients: a matching submultiset `u ≤ t` and
a separately found escaped root `a ∈ t`, with `a ∉ u`.
-/
private theorem card_filter_gt_eq_of_rel_with_separate_extra_le
    {s u t : Multiset ℝ} {x δ a : ℝ}
    (hsep : ∀ r ∈ s, δ ≤ |r - x|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s u)
    (hu : u ≤ t) (ha_mem : a ∈ t) (ha_not_mem : a ∉ u)
    (ha_le : a ≤ x)
    (hcard : t.card = s.card + 1) :
    (t.filter (fun q => x < q)).card =
      (s.filter (fun r => x < r)).card :=
  card_filter_gt_eq_of_rel_with_extra_le hsep hmatch
    ((Multiset.cons_le_of_notMem ha_not_mem).mpr ⟨ha_mem, hu⟩) ha_le hcard

/-- A proximity matching keeps the matched roots above any guard threshold
which is separated from all source roots below them. -/
private theorem forall_mem_right_threshold_lt_of_rel_abs_sub_lt
    {s u : Multiset ℝ} {B δ : ℝ}
    (hB : ∀ r ∈ s, B < r)
    (hsep : ∀ r ∈ s, δ ≤ |r - B|)
    (hmatch : Multiset.Rel (fun r q => |q - r| < δ) s u) :
    ∀ q ∈ u, B < q := by
  induction hmatch with
  | zero =>
      intro q hq
      simp at hq
  | @cons r q s u hclose _ ih =>
      intro y hy
      rw [Multiset.mem_cons] at hy
      rcases hy with rfl | hy
      · exact threshold_lt_of_abs_sub_lt_of_threshold_lt
          (hB r (by simp)) (hsep r (by simp)) hclose
      · have hB_tail : ∀ r ∈ s, B < r := by
          intro r hr
          exact hB r (by simp [hr])
        have hsep_tail : ∀ r ∈ s, δ ≤ |r - B| := by
          intro r hr
          exact hsep r (by simp [hr])
        exact ih hB_tail hsep_tail y hy

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
      (s.filter (fun r => x < r)).card := by
  have hcluster : ∀ q ∈ u, B < q :=
    forall_mem_right_threshold_lt_of_rel_abs_sub_lt hB hsep_B hmatch
  have ha_not_mem : a ∉ u := by
    intro hau
    exact (not_lt_of_ge (le_of_lt ha_lt)) (hcluster a hau)
  exact card_filter_gt_eq_of_rel_with_separate_extra_le hsep_x hmatch hu
    ha_mem ha_not_mem (le_trans (le_of_lt ha_lt) hBx) hcard

end Multiset
