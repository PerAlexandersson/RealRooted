import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Real.Basic
import RealRooted.RootContinuity

/-!
# Local constancy of threshold root counts

Reusable infrastructure for fixed-threshold count-jump arguments.

The lower root count `(p.roots.filter (· ≤ x)).card` is locally constant when
the threshold moves without crossing a root.  This lets us reduce a global
count bound to the regime of thresholds that are roots of neither polynomial.
-/

open Polynomial

namespace RealRooted

/-- Local constancy of the "elements `≤` threshold" count.

If a multiset `s` has no element in the half-open interval `(a, b]`, then the
number of elements `≤ a` equals the number of elements `≤ b`. -/
theorem card_filter_le_eq_of_no_mem_Ioc
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (h : ∀ r ∈ s, r ≤ a ∨ b < r) :
    (s.filter (· ≤ a)).card = (s.filter (· ≤ b)).card := by
  have hset : s.filter (· ≤ a) = s.filter (· ≤ b) := by
    apply Multiset.filter_congr
    grind
  simp_all

/-- Local constancy of the "elements strictly above threshold" count.

If a multiset `s` has no element in the half-open interval `(a, b]`, then the
number of elements `> a` equals the number of elements `> b`. -/
theorem card_filter_lt_eq_of_no_mem_Ioc
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (h : ∀ r ∈ s, r ≤ a ∨ b < r) :
    (s.filter (a < ·)).card = (s.filter (b < ·)).card := by
  have hset : s.filter (a < ·) = s.filter (b < ·) := by
    apply Multiset.filter_congr
    grind
  simp_all

/-- The elements in `(a, b]` and the elements strictly above `b` partition the
elements strictly above `a`. -/
theorem card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b) :
    (s.filter (fun r => a < r ∧ r ≤ b)).card + (s.filter (b < ·)).card =
      (s.filter (a < ·)).card := by
  have hIoc :
      s.filter (fun r => a < r ∧ r ≤ b) =
        (s.filter (a < ·)).filter (· ≤ b) := by
    ext r
    by_cases har : a < r <;> by_cases hrb : r ≤ b <;> simp [har, hrb]
  have hgt :
      s.filter (b < ·) =
        (s.filter (a < ·)).filter (fun r => ¬ r ≤ b) := by
    ext r
    by_cases hbr : b < r
    · simp [hbr, lt_of_le_of_lt hab hbr]
    · simp [hbr, not_le]
  rw [hIoc, hgt, ← Multiset.card_add, Multiset.filter_add_not]

/-- The strict-upper count at `a` is the strict-upper count at `b` plus the
count in the half-open window `(a, b]`. -/
theorem card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b) :
    (s.filter (a < ·)).card =
      (s.filter (fun r => a < r ∧ r ≤ b)).card + (s.filter (b < ·)).card :=
  (card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt s hab).symm

/-- The elements in `(a, b)` and the elements at or above `b` partition the
elements strictly above `a`, when `a < b`. -/
theorem card_filter_Ioo_add_card_filter_ge_eq_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a < b) :
    (s.filter (fun r => a < r ∧ r < b)).card + (s.filter (b ≤ ·)).card =
      (s.filter (a < ·)).card := by
  have hIoo :
      s.filter (fun r => a < r ∧ r < b) =
        (s.filter (a < ·)).filter (fun r => ¬ b ≤ r) := by
    ext r
    by_cases har : a < r <;> by_cases hbr : b ≤ r <;>
      simp [har, hbr, not_le, and_comm]
  have hge :
      s.filter (b ≤ ·) =
        (s.filter (a < ·)).filter (fun r => b ≤ r) := by
    ext r
    by_cases hbr : b ≤ r
    · simp [hbr, lt_of_lt_of_le hab hbr]
    · simp [hbr]
  rw [hIoo, hge, Nat.add_comm, ← Multiset.card_add, Multiset.filter_add_not]

/-- The sum of open-interval counts over a strictly increasing chain of
successive list entries is bounded by the strict-upper count above the first
entry. -/
theorem sum_card_filter_Ioo_zip_tail_le_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a : α} {xs : List α}
    (hchain : (a :: xs).IsChain (· < ·)) :
    (((a :: xs).zip xs).map
        (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum ≤
      (s.filter (a < ·)).card := by
  induction xs generalizing a with
  | nil => simp
  | cons b t ih =>
      have hab_lt : a < b := List.IsChain.rel hchain
      have htail : (b :: t).IsChain (· < ·) := List.IsChain.of_cons hchain
      have hgap_le :
          (s.filter (fun r => a < r ∧ r < b)).card ≤
            (s.filter (fun r => a < r ∧ r ≤ b)).card := by
        exact Multiset.card_le_card
          (Multiset.monotone_filter_right s fun _ hr => ⟨hr.1, le_of_lt hr.2⟩)
      have hpart :=
        card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt s (le_of_lt hab_lt)
      have hih := ih (a := b) htail
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      calc
        (s.filter (fun r => a < r ∧ r < b)).card +
            (((b :: t).zip t).map
                (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum
            ≤ (s.filter (fun r => a < r ∧ r ≤ b)).card +
                (s.filter (b < ·)).card :=
          Nat.add_le_add hgap_le hih
        _ = (s.filter (a < ·)).card := by
          simpa using hpart.symm

/-- The sum of open-interval counts over a strictly increasing chain, plus the
closed upper-tail count at the last list entry, is bounded by the strict-upper
count above the first list entry. -/
theorem sum_card_filter_Ioo_zip_tail_add_card_filter_ge_getLast_le_card_filter_gt
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} {xs : List α}
    (hchain : (a :: b :: xs).IsChain (· < ·)) :
    (((a :: b :: xs).zip (b :: xs)).map
        (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum +
      (s.filter (fun r => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ r)).card ≤
    (s.filter (a < ·)).card := by
  induction xs generalizing a b with
  | nil =>
      have hab_lt : a < b := List.IsChain.rel hchain
      simpa using
        (card_filter_Ioo_add_card_filter_ge_eq_card_filter_gt s hab_lt).le
  | cons c t ih =>
      have hab_lt : a < b := List.IsChain.rel hchain
      have htail : (b :: c :: t).IsChain (· < ·) := List.IsChain.of_cons hchain
      have hgap_le :
          (s.filter (fun r => a < r ∧ r < b)).card ≤
            (s.filter (fun r => a < r ∧ r ≤ b)).card := by
        exact Multiset.card_le_card
          (Multiset.monotone_filter_right s fun _ hr => ⟨hr.1, le_of_lt hr.2⟩)
      have hpart :=
        card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt s (le_of_lt hab_lt)
      have hih := ih (a := b) (b := c) htail
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      calc
        (s.filter (fun r => a < r ∧ r < b)).card +
            (((b :: c :: t).zip (c :: t)).map
                (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum +
              (s.filter (fun r =>
                (c :: t).getLast (List.cons_ne_nil c t) ≤ r)).card
            = (s.filter (fun r => a < r ∧ r < b)).card +
              ((((b :: c :: t).zip (c :: t)).map
                  (fun ab =>
                    (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum +
                (s.filter (fun r =>
                  (c :: t).getLast (List.cons_ne_nil c t) ≤ r)).card) := by
          rw [Nat.add_assoc]
        _ ≤ (s.filter (fun r => a < r ∧ r ≤ b)).card +
            (s.filter (b < ·)).card := Nat.add_le_add hgap_le hih
        _ = (s.filter (a < ·)).card := by
          simpa using hpart.symm

/-- The closed lower tail at the first list entry, the adjacent open gaps, and
the closed upper tail at the last list entry fit inside the whole multiset. -/
theorem card_filter_le_add_sum_card_filter_Ioo_zip_tail_add_card_filter_ge_getLast_le_card
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} {xs : List α}
    (hchain : (a :: b :: xs).IsChain (· < ·)) :
    (s.filter (· ≤ a)).card +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum +
      (s.filter (fun r => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ r)).card ≤
    s.card := by
  have hupper :=
    sum_card_filter_Ioo_zip_tail_add_card_filter_ge_getLast_le_card_filter_gt
      (s := s) hchain
  have hpart := Multiset.card_filter_le_add_card_filter_gt s a
  calc
    (s.filter (· ≤ a)).card +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum +
      (s.filter (fun r => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ r)).card
        = (s.filter (· ≤ a)).card +
          ((((a :: b :: xs).zip (b :: xs)).map
            (fun ab => (s.filter (fun r => ab.1 < r ∧ r < ab.2)).card)).sum +
          (s.filter (fun r =>
            (b :: xs).getLast (List.cons_ne_nil b xs) ≤ r)).card) := by
      rw [Nat.add_assoc]
    _ ≤ (s.filter (· ≤ a)).card + (s.filter (a < ·)).card :=
      Nat.add_le_add_left hupper _
    _ = s.card := by
      simpa using hpart

/-- If `(a, b]` contains an element of a multiset, then the strict-upper count
drops when the threshold moves from `a` to `b`. -/
theorem card_filter_gt_lt_of_mem_Ioc
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b c : α} (hab : a ≤ b)
    (hc : c ∈ s) (hac : a < c) (hcb : c ≤ b) :
    (s.filter (b < ·)).card < (s.filter (a < ·)).card := by
  have hpart := card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt s hab
  have hcIoc : c ∈ s.filter (fun r => a < r ∧ r ≤ b) := by
    simp [hc, hac, hcb]
  have hpos : 0 < (s.filter (fun r => a < r ∧ r ≤ b)).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨c, hcIoc⟩
  rw [← hpart]
  exact Nat.lt_add_of_pos_left hpos

/-- If every root of a polynomial is at most `x`, then its strict-upper root
count above `x` is zero. -/
theorem rootCountAbove_eq_zero_of_forall_roots_le {p : ℝ[X]} {x : ℝ}
    (h : ∀ r ∈ p.roots, r ≤ x) :
    (p.roots.filter (x < ·)).card = 0 := by
  have hfilter : p.roots.filter (x < ·) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro r hr
    exact not_lt.mpr (h r hr)
  simp [hfilter]

/-- If no root of a nonzero polynomial lies strictly above `x`, then the
strict-upper root count above `x` is zero. -/
theorem card_roots_filter_gt_eq_zero_of_no_isRoot_gt
    {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ}
    (h : ∀ r : ℝ, x < r → ¬ p.IsRoot r) :
    (p.roots.filter (x < ·)).card = 0 :=
  rootCountAbove_eq_zero_of_forall_roots_le fun r hr =>
    le_of_not_gt fun hxr => h r hxr ((Polynomial.mem_roots hp).mp hr)

/-- If neither polynomial has a root strictly above `x`, then their strict-upper
root-count difference above `x` is zero. -/
theorem card_roots_filter_gt_sub_eq_zero_of_no_isRoot_or_isRoot_gt
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {x : ℝ}
    (h : ∀ r : ℝ, x < r → ¬ f.IsRoot r ∧ ¬ g.IsRoot r) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 0 := by
  have hf_zero :=
    card_roots_filter_gt_eq_zero_of_no_isRoot_gt hf fun r hr => (h r hr).1
  have hg_zero :=
    card_roots_filter_gt_eq_zero_of_no_isRoot_gt hg fun r hr => (h r hr).2
  simp [hf_zero, hg_zero]

/-- Membership in the combined roots multiset is the same as being a root of
one of the two nonzero polynomials. -/
theorem mem_roots_add_iff_isRoot_or_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {x : ℝ} :
    x ∈ f.roots + g.roots ↔ f.IsRoot x ∨ g.IsRoot x := by
  rw [Multiset.mem_add, Polynomial.mem_roots hf, Polynomial.mem_roots hg]

/-- Exact jump formula for strict-upper multiset-count differences across
`(a, b]`. -/
theorem card_filter_gt_sub_eq_card_filter_Ioc_sub_add
    {α : Type*} [LinearOrder α] (s t : Multiset α) {a b : α} (hab : a ≤ b) :
    ((s.filter (a < ·)).card : ℤ) - (t.filter (a < ·)).card =
      (((s.filter (fun r => a < r ∧ r ≤ b)).card : ℤ) -
          (t.filter (fun r => a < r ∧ r ≤ b)).card) +
        (((s.filter (b < ·)).card : ℤ) -
          (t.filter (b < ·)).card) := by
  rw [card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt s hab,
    card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt t hab]
  push_cast
  ring

/-- Crossing exactly one simple root of the left polynomial and no roots of the
right polynomial increases the strict-upper count difference by one. -/
theorem card_roots_filter_gt_sub_eq_one_add_of_left_simple_root_Ioc
    {f g : ℝ[X]} (hf : f ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hcount : f.roots.count c = 1)
    (hf_no : ∀ z : ℝ, a < z → z ≤ b → z ≠ c → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z ≤ b → ¬ g.IsRoot z) :
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
      1 + (((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card) := by
  have hab : a ≤ b := (le_of_lt hac).trans hcb
  have hjump := card_filter_gt_sub_eq_card_filter_Ioc_sub_add f.roots g.roots hab
  have hfIoc :=
    card_roots_filter_Ioc_eq_one_of_count_eq_one_of_no_isRoot_ne
      hf hac hcb hcount hf_no
  have hgIoc := card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc hab hg_no
  simpa [hfIoc, hgIoc] using hjump

/-- Crossing exactly one simple root of the right polynomial and no roots of the
left polynomial decreases the strict-upper count difference by one. -/
theorem card_roots_filter_gt_sub_eq_neg_one_add_of_right_simple_root_Ioc
    {f g : ℝ[X]} (hg : g ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hcount : g.roots.count c = 1)
    (hf_no : ∀ z : ℝ, a < z → z ≤ b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z ≤ b → z ≠ c → ¬ g.IsRoot z) :
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
      -1 + (((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card) := by
  have hab : a ≤ b := (le_of_lt hac).trans hcb
  have hjump := card_filter_gt_sub_eq_card_filter_Ioc_sub_add f.roots g.roots hab
  have hfIoc := card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc hab hf_no
  have hgIoc :=
    card_roots_filter_Ioc_eq_one_of_count_eq_one_of_no_isRoot_ne
      hg hac hcb hcount hg_no
  simpa [hfIoc, hgIoc] using hjump

/-- If the unique combined root in `(a, b]` is a simple root of the left
polynomial, then the strict-upper count difference increases by one across the
window. -/
theorem card_roots_filter_gt_sub_eq_one_add_of_left_unique_simple_root_Ioc
    {f g : ℝ[X]} (hf : f ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hg_not : ¬ g.IsRoot c)
    (hcount : f.roots.count c = 1)
    (hunique : ∀ z : ℝ, a < z → z ≤ b →
      f.IsRoot z ∨ g.IsRoot z → z = c) :
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
      1 + (((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card) := by
  refine card_roots_filter_gt_sub_eq_one_add_of_left_simple_root_Ioc
    hf hac hcb hcount ?_ ?_
  · intro z haz hzb hzc hfz
    exact hzc (hunique z haz hzb (Or.inl hfz))
  · intro z haz hzb hgz
    exact hg_not ((hunique z haz hzb (Or.inr hgz)) ▸ hgz)

/-- If the unique combined root in `(a, b]` is a simple root of the right
polynomial, then the strict-upper count difference decreases by one across the
window. -/
theorem card_roots_filter_gt_sub_eq_neg_one_add_of_right_unique_simple_root_Ioc
    {f g : ℝ[X]} (hg : g ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hf_not : ¬ f.IsRoot c)
    (hcount : g.roots.count c = 1)
    (hunique : ∀ z : ℝ, a < z → z ≤ b →
      f.IsRoot z ∨ g.IsRoot z → z = c) :
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
      -1 + (((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card) := by
  refine card_roots_filter_gt_sub_eq_neg_one_add_of_right_simple_root_Ioc
    hg hac hcb hcount ?_ ?_
  · intro z haz hzb hfz
    exact hf_not ((hunique z haz hzb (Or.inl hfz)) ▸ hfz)
  · intro z haz hzb hzc hgz
    exact hzc (hunique z haz hzb (Or.inr hgz))

/-- A least combined root above `a`, together with a root-free half-open gap
`(c, b]`, is the unique combined root in `(a, b]`. -/
theorem eq_of_isRoot_or_isRoot_Ioc_of_least_of_roots_no_mem_Ioc
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b c : ℝ}
    (hleast : ∀ z : ℝ, a < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z)
    (hgap_f : ∀ r ∈ f.roots, r ≤ c ∨ b < r)
    (hgap_g : ∀ r ∈ g.roots, r ≤ c ∨ b < r) :
    ∀ z : ℝ, a < z → z ≤ b → f.IsRoot z ∨ g.IsRoot z → z = c := by
  intro z haz hzb hz
  rcases hz with hfz | hgz
  · have hz_mem : z ∈ f.roots := (Polynomial.mem_roots hf).mpr hfz
    rcases hgap_f z hz_mem with hle | hlt
    · exact le_antisymm hle (hleast z haz (Or.inl hfz))
    · linarith
  · have hz_mem : z ∈ g.roots := (Polynomial.mem_roots hg).mpr hgz
    rcases hgap_g z hz_mem with hle | hlt
    · exact le_antisymm hle (hleast z haz (Or.inr hgz))
    · linarith

/-- One-step suffix-count transport across a least combined root owned by the
left polynomial, with the upper endpoint chosen before the next combined root.
Crossing such a root raises the strict-upper `f`-minus-`g` count difference by
one. -/
theorem card_roots_filter_gt_sub_eq_add_one_of_left_least_root_no_mem_Ioc
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b c : ℝ} {k : ℤ}
    (hac : a < c) (hcb : c ≤ b) (hg_not : ¬ g.IsRoot c)
    (hcount : f.roots.count c = 1)
    (hleast : ∀ z : ℝ, a < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z)
    (hgap_f : ∀ r ∈ f.roots, r ≤ c ∨ b < r)
    (hgap_g : ∀ r ∈ g.roots, r ≤ c ∨ b < r)
    (hb : ((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card = k) :
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card = k + 1 := by
  have hunique :=
    eq_of_isRoot_or_isRoot_Ioc_of_least_of_roots_no_mem_Ioc
      hf hg hleast hgap_f hgap_g
  have hshift :=
    card_roots_filter_gt_sub_eq_one_add_of_left_unique_simple_root_Ioc
      hf hac hcb hg_not hcount hunique
  simpa [hb, add_comm] using hshift

/-- One-step suffix-count transport across a least combined root owned by the
right polynomial, with the upper endpoint chosen before the next combined root.
Crossing such a root lowers the strict-upper `f`-minus-`g` count difference by
one. -/
theorem card_roots_filter_gt_sub_eq_sub_one_of_right_least_root_no_mem_Ioc
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b c : ℝ} {k : ℤ}
    (hac : a < c) (hcb : c ≤ b) (hf_not : ¬ f.IsRoot c)
    (hcount : g.roots.count c = 1)
    (hleast : ∀ z : ℝ, a < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z)
    (hgap_f : ∀ r ∈ f.roots, r ≤ c ∨ b < r)
    (hgap_g : ∀ r ∈ g.roots, r ≤ c ∨ b < r)
    (hb : ((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card = k) :
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card = k - 1 := by
  have hunique :=
    eq_of_isRoot_or_isRoot_Ioc_of_least_of_roots_no_mem_Ioc
      hf hg hleast hgap_f hgap_g
  have hshift :=
    card_roots_filter_gt_sub_eq_neg_one_add_of_right_unique_simple_root_Ioc
      hg hac hcb hf_not hcount hunique
  calc
    ((f.roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
        -1 + (((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card) := hshift
    _ = k - 1 := by
      rw [hb]
      ring

/-- If `b` is not present, the elements in `(a, b)` and the elements strictly
above `b` partition the elements strictly above `a`. -/
theorem card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (hb : b ∉ s) :
    (s.filter (fun r => a < r ∧ r < b)).card + (s.filter (b < ·)).card =
      (s.filter (a < ·)).card := by
  have hIoo :
      s.filter (fun r ↦ a < r ∧ r < b) =
        s.filter (fun r ↦ a < r ∧ r ≤ b) := by
    apply Multiset.filter_congr
    grind
  rw [hIoo]
  exact card_filter_Ioc_add_card_filter_gt_eq_card_filter_gt s hab

/-- For an interval whose right endpoint is absent from a multiset, parity of
the open-interval count is the same as parity of the sum of the two
strict-upper endpoint counts. -/
theorem odd_card_filter_gt_add_iff_odd_card_filter_Ioo_of_not_mem
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (hb : b ∉ s) :
    Odd ((s.filter (a < ·)).card + (s.filter (b < ·)).card) ↔
      Odd (s.filter (fun r => a < r ∧ r < b)).card := by
  have hpart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem s hab hb
  rw [← hpart]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - (s.filter (b < ·)).card, ?_⟩
    lia
  · rintro ⟨k, hk⟩
    refine ⟨k + (s.filter (b < ·)).card, ?_⟩
    lia

/-- If two multisets have the same number of elements above each endpoint of
an interval, then they have the same number of elements inside the interval,
provided the right endpoint belongs to neither multiset. -/
theorem card_filter_Ioo_eq_of_card_filter_gt_eq
    {α : Type*} [LinearOrder α] (s t : Multiset α) {a b : α} (hab : a ≤ b)
    (hsb : b ∉ s) (htb : b ∉ t)
    (ha : (s.filter (a < ·)).card = (t.filter (a < ·)).card)
    (hb : (s.filter (b < ·)).card = (t.filter (b < ·)).card) :
    (s.filter (fun r => a < r ∧ r < b)).card =
      (t.filter (fun r => a < r ∧ r < b)).card := by
  have hspart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem s hab hsb
  have htpart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem t hab htb
  grind

/-- If two polynomials have the same number of roots above each endpoint of
an interval, then they have the same number of roots inside the interval,
provided the right endpoint is a root of neither polynomial. -/
theorem card_roots_filter_Ioo_eq_of_card_filter_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (ha :
      (f.roots.filter (a < ·)).card =
        (g.roots.filter (a < ·)).card)
    (hb :
      (f.roots.filter (b < ·)).card =
        (g.roots.filter (b < ·)).card) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_filter_Ioo_eq_of_card_filter_gt_eq f.roots g.roots hab
    (fun hb_mem => hfb ((mem_roots hf).mp hb_mem))
    (fun hb_mem => hgb ((mem_roots hg).mp hb_mem)) ha hb

/-- Polynomial-root form of
`odd_card_filter_gt_add_iff_odd_card_filter_Ioo_of_not_mem`. -/
theorem odd_card_roots_filter_gt_add_iff_odd_card_roots_filter_Ioo_of_not_isRoot
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hb : ¬ p.IsRoot b) :
    Odd ((p.roots.filter (a < ·)).card + (p.roots.filter (b < ·)).card) ↔
      Odd (p.roots.filter (fun r => a < r ∧ r < b)).card :=
  odd_card_filter_gt_add_iff_odd_card_filter_Ioo_of_not_mem p.roots hab
    (fun hb_mem => hb ((mem_roots hp).mp hb_mem))

/-- If an open interval contains at least two elements of a multiset, then the
strict-upper count drops by at least two across the interval, provided the
right endpoint is absent. -/
theorem card_filter_gt_add_two_le_of_two_le_card_filter_Ioo
    {α : Type*} [LinearOrder α] (s : Multiset α) {a b : α} (hab : a ≤ b)
    (hb : b ∉ s)
    (htwo : 2 ≤ (s.filter (fun r => a < r ∧ r < b)).card) :
    (s.filter (b < ·)).card + 2 ≤ (s.filter (a < ·)).card := by
  have hpart :=
    card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem s hab hb
  calc
    (s.filter (b < ·)).card + 2
        ≤ (s.filter (b < ·)).card +
            (s.filter (fun r => a < r ∧ r < b)).card :=
          Nat.add_le_add_left htwo _
    _ = (s.filter (fun r => a < r ∧ r < b)).card +
          (s.filter (b < ·)).card := Nat.add_comm _ _
    _ = (s.filter (a < ·)).card := hpart

/-- Polynomial root-count form of
`card_filter_gt_add_two_le_of_two_le_card_filter_Ioo`. -/
theorem card_roots_filter_gt_add_two_le_of_two_le_card_filter_Ioo
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hb : ¬ p.IsRoot b)
    (htwo : 2 ≤ (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    (p.roots.filter (b < ·)).card + 2 ≤ (p.roots.filter (a < ·)).card :=
  card_filter_gt_add_two_le_of_two_le_card_filter_Ioo p.roots hab
    (fun hb_mem => hb ((Polynomial.mem_roots hp_ne).mp hb_mem)) htwo

/-- A strict-upper count drop by at least two is impossible if the
strict-upper count difference against a comparison multiset is stable across an
interval where the comparison count is constant. -/
theorem not_card_filter_gt_add_two_le_of_card_filter_gt_sub_eq
    {α : Type*} [LinearOrder α] {s t : Multiset α} {a b : α}
    (ht : (t.filter (a < ·)).card = (t.filter (b < ·)).card)
    (hsub : ((s.filter (a < ·)).card : ℤ) - (t.filter (a < ·)).card =
      ((s.filter (b < ·)).card : ℤ) - (t.filter (b < ·)).card) :
    ¬ ((s.filter (b < ·)).card + 2 ≤ (s.filter (a < ·)).card) := by
  intro hdrop
  have ht_int : ((t.filter (a < ·)).card : ℤ) =
      ((t.filter (b < ·)).card : ℤ) := by
    exact_mod_cast ht
  have hdrop_int : ((s.filter (b < ·)).card : ℤ) + 2 ≤
      ((s.filter (a < ·)).card : ℤ) := by
    exact_mod_cast hdrop
  linarith

/-- A strict-upper count drop by at least two is impossible if the endpoint
counts agree with those of a multiset whose strict-upper count is constant
across the interval. -/
theorem not_card_filter_gt_add_two_le_of_card_filter_gt_eq
    {α : Type*} [LinearOrder α] {s t : Multiset α} {a b : α}
    (ht : (t.filter (a < ·)).card = (t.filter (b < ·)).card)
    (ha : (s.filter (a < ·)).card = (t.filter (a < ·)).card)
    (hb : (s.filter (b < ·)).card = (t.filter (b < ·)).card) :
    ¬ ((s.filter (b < ·)).card + 2 ≤ (s.filter (a < ·)).card) := by
  exact not_card_filter_gt_add_two_le_of_card_filter_gt_sub_eq ht
    (by rw [ha, hb]; simp)

/-- A strict-upper root-count drop by at least two is impossible if the
strict-upper root-count difference against a polynomial with no roots in
`(a, b]` is stable across the endpoints. -/
theorem not_card_roots_filter_gt_add_two_le_of_sub_eq_no_isRoot_Ioc
    {p q : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hq_no : ∀ x : ℝ, a < x → x ≤ b → ¬ q.IsRoot x)
    (hsub : ((p.roots.filter (a < ·)).card : ℤ) -
        (q.roots.filter (a < ·)).card =
      ((p.roots.filter (b < ·)).card : ℤ) -
        (q.roots.filter (b < ·)).card) :
    ¬ ((p.roots.filter (b < ·)).card + 2 ≤
      (p.roots.filter (a < ·)).card) := by
  have hq_eq : (q.roots.filter (a < ·)).card =
      (q.roots.filter (b < ·)).card :=
    card_roots_filter_gt_eq_of_no_isRoot_Ioc (p := q) hab hq_no
  exact not_card_filter_gt_add_two_le_of_card_filter_gt_sub_eq hq_eq hsub

/-- A strict-upper root-count drop by at least two is impossible if the two
endpoint counts agree with those of a polynomial having no roots in `(a, b]`. -/
theorem not_card_roots_filter_gt_add_two_le_of_eq_no_isRoot_Ioc
    {p q : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hq_no : ∀ x : ℝ, a < x → x ≤ b → ¬ q.IsRoot x)
    (ha : (p.roots.filter (a < ·)).card = (q.roots.filter (a < ·)).card)
    (hb : (p.roots.filter (b < ·)).card = (q.roots.filter (b < ·)).card) :
    ¬ ((p.roots.filter (b < ·)).card + 2 ≤
      (p.roots.filter (a < ·)).card) := by
  exact not_card_roots_filter_gt_add_two_le_of_sub_eq_no_isRoot_Ioc hab hq_no
    (by rw [ha, hb]; simp)

/-- A nonzero splitting polynomial with same-sign endpoint values has an even
number of roots in the open interval between those endpoints. -/
theorem even_card_roots_filter_Ioo_of_eval_mul_pos
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp : p.Splits)
    {a b : ℝ} (hab : a ≤ b) (hprod : 0 < p.eval a * p.eval b) :
    Even (p.roots.filter (fun r => a < r ∧ r < b)).card := by
  let A := (p.roots.filter (a < ·)).card
  let B := (p.roots.filter (b < ·)).card
  let I := (p.roots.filter (fun r => a < r ∧ r < b)).card
  have hpa : ¬ p.IsRoot a := by
    intro hroot
    have hzero : p.eval a = 0 := by
      simpa [Polynomial.IsRoot.def] using hroot
    rw [hzero, zero_mul] at hprod
    linarith
  have hpb : ¬ p.IsRoot b := by
    intro hroot
    have hzero : p.eval b = 0 := by
      simpa [Polynomial.IsRoot.def] using hroot
    rw [hzero, mul_zero] at hprod
    linarith
  have hnorm_a : 0 < p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A := by
    simpa [A] using hp.eval_mul_leadingCoeff_neg_one_pow_pos hp_ne hpa
  have hnorm_b : 0 < p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B := by
    simpa [B] using hp.eval_mul_leadingCoeff_neg_one_pow_pos hp_ne hpb
  have hlc_sq : 0 < p.leadingCoeff * p.leadingCoeff :=
    mul_self_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp_ne)
  have hAB_even : Even (A + B) := by
    by_contra hnot
    have hAB_odd : Odd (A + B) := Nat.not_even_iff_odd.mp hnot
    have hpow : (-1 : ℝ) ^ (A + B) = -1 := Odd.neg_one_pow hAB_odd
    have hnorm_prod :
        0 < (p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A) *
          (p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B) :=
      mul_pos hnorm_a hnorm_b
    have hcalc :
        (p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A) *
            (p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B) =
          (p.eval a * p.eval b) * (p.leadingCoeff * p.leadingCoeff) *
            ((-1 : ℝ) ^ (A + B)) := by
      rw [pow_add]
      ring
    rw [hcalc, hpow] at hnorm_prod
    nlinarith [hprod, hlc_sq]
  have hb_not_mem : b ∉ p.roots := by
    intro hb_mem
    exact hpb ((Polynomial.mem_roots hp_ne).mp hb_mem)
  have hsplit : I + B = A := by
    simpa [I, B, A] using
      card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
        (s := p.roots) hab hb_not_mem
  rw [← hsplit] at hAB_even
  have hsum : Even (I + (B + B)) := by
    simpa [Nat.add_assoc] using hAB_even
  rw [Nat.even_add] at hsum
  have hBB : Even (B + B) := by
    exact ⟨B, by ring⟩
  exact hsum.mpr hBB

/-- A nonzero splitting polynomial with an even number of roots, counted with
multiplicity, in an open interval has same-sign endpoint values, provided
neither endpoint is a root. -/
theorem eval_mul_eval_pos_of_even_card_roots_filter_Ioo
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp : p.Splits)
    {a b : ℝ} (hab : a ≤ b)
    (heven : Even (p.roots.filter (fun r => a < r ∧ r < b)).card)
    (ha : ¬ p.IsRoot a) (hb : ¬ p.IsRoot b) :
    0 < p.eval a * p.eval b := by
  let A := (p.roots.filter (a < ·)).card
  let B := (p.roots.filter (b < ·)).card
  let I := (p.roots.filter (fun r => a < r ∧ r < b)).card
  have hnorm_a : 0 < p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A := by
    simpa [A] using hp.eval_mul_leadingCoeff_neg_one_pow_pos hp_ne ha
  have hnorm_b : 0 < p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B := by
    simpa [B] using hp.eval_mul_leadingCoeff_neg_one_pow_pos hp_ne hb
  have hlc_sq : 0 < p.leadingCoeff * p.leadingCoeff :=
    mul_self_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp_ne)
  have hb_not_mem : b ∉ p.roots := by
    intro hb_mem
    exact hb ((Polynomial.mem_roots hp_ne).mp hb_mem)
  have hsplit : I + B = A := by
    simpa [I, B, A] using
      card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
        (s := p.roots) hab hb_not_mem
  have hI_even : Even I := by
    simpa [I] using heven
  have hBB_even : Even (B + B) := by
    exact ⟨B, by ring_nf⟩
  have hAB_even : Even (A + B) := by
    rw [← hsplit]
    simpa [Nat.add_assoc] using Even.add hI_even hBB_even
  have hpow : (-1 : ℝ) ^ (A + B) = 1 := Even.neg_one_pow hAB_even
  have hnorm_prod :
      0 < (p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A) *
        (p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B) :=
    mul_pos hnorm_a hnorm_b
  have hcalc :
      (p.eval a * p.leadingCoeff * (-1 : ℝ) ^ A) *
          (p.eval b * p.leadingCoeff * (-1 : ℝ) ^ B) =
        (p.eval a * p.eval b) * (p.leadingCoeff * p.leadingCoeff) *
          ((-1 : ℝ) ^ (A + B)) := by
    rw [pow_add]
    ring
  rw [hcalc, hpow, mul_one] at hnorm_prod
  exact (mul_pos_iff_of_pos_right hlc_sq).mp hnorm_prod

/-- A nonzero splitting polynomial with an odd number of roots, counted with
multiplicity, in an open interval has opposite-sign endpoint values, provided
neither endpoint is a root. -/
theorem eval_mul_eval_neg_of_odd_card_roots_filter_Ioo
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp : p.Splits)
    {a b : ℝ} (hab : a ≤ b)
    (hodd : Odd (p.roots.filter (fun r => a < r ∧ r < b)).card)
    (ha : ¬ p.IsRoot a) (hb : ¬ p.IsRoot b) :
    p.eval a * p.eval b < 0 := by
  have hpa : p.eval a ≠ 0 := by
    intro h
    exact ha (by simpa [Polynomial.IsRoot.def] using h)
  have hpb : p.eval b ≠ 0 := by
    intro h
    exact hb (by simpa [Polynomial.IsRoot.def] using h)
  have hprod_ne : p.eval a * p.eval b ≠ 0 := mul_ne_zero hpa hpb
  have hnot_pos : ¬ 0 < p.eval a * p.eval b := by
    intro hpos
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_card_roots_filter_Ioo_of_eval_mul_pos hp_ne hp hab hpos)
  exact lt_of_le_of_ne (le_of_not_gt hnot_pos) hprod_ne

/-- If an even root count over an open interval contains an interior root, then
the interval contains at least two roots, counted with multiplicity. -/
theorem two_le_card_roots_filter_Ioo_of_even_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b y : ℝ}
    (hy : p.IsRoot y) (hay : a < y) (hyb : y < b)
    (heven : Even (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    2 ≤ (p.roots.filter (fun r => a < r ∧ r < b)).card := by
  let s := p.roots.filter (fun r => a < r ∧ r < b)
  have hmem : y ∈ s := by
    exact Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hp_ne).mpr hy, ⟨hay, hyb⟩⟩
  have hcard_pos : 0 < s.card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨y, hmem⟩
  exact Nat.one_lt_of_ne_zero_of_even (Nat.ne_of_gt hcard_pos) heven

/-- If a nonzero polynomial has at least two roots in an open interval,
counted with multiplicity, then a two-element multiset of roots lies in that
filtered root multiset.  The two values are allowed to coincide, which covers
repeated roots. -/
theorem exists_roots_pair_le_roots_filter_Ioo_of_two_le_card_roots_filter_Ioo
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b : ℝ}
    (hcard : 2 ≤ (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    ∃ u v : ℝ,
      a < u ∧ u < b ∧ a < v ∧ v < b ∧ p.IsRoot u ∧ p.IsRoot v ∧
        ({u, v} : Multiset ℝ) ≤ p.roots.filter (fun r => a < r ∧ r < b) := by
  let s := p.roots.filter (fun r => a < r ∧ r < b)
  change 2 ≤ s.card at hcard
  have hs_pos : 0 < s.card := by
    linarith
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp hs_pos
  have herase_pos : 0 < (s.erase u).card := by
    rw [Multiset.card_erase_of_mem hu]
    exact Nat.sub_pos_of_lt (Nat.lt_of_succ_le hcard)
  obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp herase_pos
  have hv_mem : v ∈ s := Multiset.mem_of_mem_erase hv
  have hpair_le : ({u, v} : Multiset ℝ) ≤ s := by
    rw [← Multiset.cons_erase hu]
    exact Multiset.cons_le_cons u (Multiset.singleton_le.mpr hv)
  rw [Multiset.mem_filter] at hu hv_mem
  obtain ⟨hu_root, ⟨hau, hub⟩⟩ := hu
  obtain ⟨hv_root, ⟨hav, hvb⟩⟩ := hv_mem
  exact ⟨u, v, hau, hub, hav, hvb,
    (Polynomial.mem_roots hp_ne).mp hu_root,
    (Polynomial.mem_roots hp_ne).mp hv_root, hpair_le⟩

/-- Even nonzero root count in an open interval, plus one known interior root,
produces a two-element multiset inside the interval root multiset. -/
theorem exists_roots_pair_le_roots_filter_Ioo_of_even_card_roots_filter_Ioo_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b y : ℝ}
    (hy : p.IsRoot y) (hay : a < y) (hyb : y < b)
    (heven : Even (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    ∃ u v : ℝ,
      a < u ∧ u < b ∧ a < v ∧ v < b ∧ p.IsRoot u ∧ p.IsRoot v ∧
        ({u, v} : Multiset ℝ) ≤ p.roots.filter (fun r => a < r ∧ r < b) :=
  exists_roots_pair_le_roots_filter_Ioo_of_two_le_card_roots_filter_Ioo hp_ne
    (two_le_card_roots_filter_Ioo_of_even_of_isRoot hp_ne hy hay hyb heven)

/-- If two endpoint polynomials have the same nonzero sign at `x`, then every
member of their closed segment is nonzero at `x`. -/
theorem closedSegment_eval_ne_zero_of_eval_mul_pos
    {f g : ℝ[X]} {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hprod : 0 < f.eval x * g.eval x) :
    (C (1 - β) * f + C β * g).eval x ≠ 0 := by
  have hweight : 0 ≤ 1 - β := by linarith
  have hf_ne : f.eval x ≠ 0 := by
    intro hf0
    simp_all
  by_cases hf_pos : 0 < f.eval x
  · have hg_pos : 0 < g.eval x := by nlinarith
    have hpos_eval : 0 < (1 - β) * f.eval x + β * g.eval x := by
      by_cases hβ : β = 0
      · simp_all
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ)
        have hleft_nonneg : 0 ≤ (1 - β) * f.eval x :=
          mul_nonneg hweight (le_of_lt hf_pos)
        have hright_pos : 0 < β * g.eval x := mul_pos hβ_pos hg_pos
        linarith
    have hpos : 0 < (C (1 - β) * f + C β * g).eval x := by simp_all
    grind
  · have hf_neg : f.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hf_pos) hf_ne
    have hg_neg : g.eval x < 0 := by nlinarith
    have hneg_eval : (1 - β) * f.eval x + β * g.eval x < 0 := by
      by_cases hβ : β = 0
      · simp_all
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ)
        have hleft_nonpos : (1 - β) * f.eval x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hweight (le_of_lt hf_neg)
        have hright_neg : β * g.eval x < 0 := mul_neg_of_pos_of_neg hβ_pos hg_neg
        linarith
    have hneg : (C (1 - β) * f + C β * g).eval x < 0 := by simp_all
    grind

/-- `IsRoot`-form of `closedSegment_eval_ne_zero_of_eval_mul_pos`. -/
theorem closedSegment_not_isRoot_of_eval_mul_pos
    {f g : ℝ[X]} {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hprod : 0 < f.eval x * g.eval x) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x := by
  simpa [Polynomial.IsRoot.def] using
    closedSegment_eval_ne_zero_of_eval_mul_pos (f := f) (g := g)
      (β := β) (x := x) hβ0 hβ1 hprod

/-- If both endpoints of a closed interval are roots of the left endpoint
polynomial and the right endpoint polynomial has no roots on that interval,
then every nontrivial right-weighted closed-segment member has same-sign
values at the interval endpoints. -/
theorem closedSegment_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc
    {f g : ℝ[X]} {a b β : ℝ} (hab : a ≤ b)
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ x ∈ Set.Icc a b, ¬ g.IsRoot x) (hβ_pos : 0 < β) :
    0 < (C (1 - β) * f + C β * g).eval a *
        (C (1 - β) * f + C β * g).eval b := by
  have hgprod : 0 < g.eval a * g.eval b :=
    eval_mul_pos_of_forall_not_isRoot_Icc hab hg_no
  have hfa_eval : f.eval a = 0 := by
    simpa [Polynomial.IsRoot.def] using hfa
  have hfb_eval : f.eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hfb
  have ha : (C (1 - β) * f + C β * g).eval a = β * g.eval a := by
    simp [eval_add, eval_mul, eval_C, hfa_eval]
  have hb : (C (1 - β) * f + C β * g).eval b = β * g.eval b := by
    simp [eval_add, eval_mul, eval_C, hfb_eval]
  rw [ha, hb]
  have hβ_sq : 0 < β * β := mul_pos hβ_pos hβ_pos
  nlinarith [mul_pos hβ_sq hgprod]

/-- Right-family version of
`closedSegment_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc`. -/
theorem rightFamily_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc
    {f g : ℝ[X]} {a b μ : ℝ} (hab : a ≤ b)
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ x ∈ Set.Icc a b, ¬ g.IsRoot x) (hμ_pos : 0 < μ) :
    0 < (f + C μ * g).eval a * (f + C μ * g).eval b := by
  have hgprod : 0 < g.eval a * g.eval b :=
    eval_mul_pos_of_forall_not_isRoot_Icc hab hg_no
  have hfa_eval : f.eval a = 0 := by
    simpa [Polynomial.IsRoot.def] using hfa
  have hfb_eval : f.eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hfb
  have hμ_sq : 0 < μ * μ := mul_pos hμ_pos hμ_pos
  have htarget : 0 < (μ * g.eval a) * (μ * g.eval b) := by
    nlinarith [mul_pos hμ_sq hgprod]
  simpa [eval_add, eval_mul, eval_C, hfa_eval, hfb_eval] using htarget

/-- If two endpoint polynomials have the same nonzero sign at `x`, then every
nonnegative right-family member is nonzero at `x`. -/
theorem rightFamily_eval_ne_zero_of_eval_mul_pos
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ)
    (hprod : 0 < f.eval x * g.eval x) :
    (f + C μ * g).eval x ≠ 0 := by
  have hf_ne : f.eval x ≠ 0 := by
    intro hf0
    simp_all
  by_cases hf_pos : 0 < f.eval x
  · have hg_pos : 0 < g.eval x := by nlinarith
    have hpos_eval : 0 < f.eval x + μ * g.eval x := by
      have hright_nonneg : 0 ≤ μ * g.eval x := mul_nonneg hμ (le_of_lt hg_pos)
      linarith
    have hpos : 0 < (f + C μ * g).eval x := by simp_all
    grind
  · have hf_neg : f.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hf_pos) hf_ne
    have hg_neg : g.eval x < 0 := by nlinarith
    have hneg_eval : f.eval x + μ * g.eval x < 0 := by
      have hright_nonpos : μ * g.eval x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hμ (le_of_lt hg_neg)
      linarith
    have hneg : (f + C μ * g).eval x < 0 := by simp_all
    grind

/-- Move a real threshold strictly upward without crossing any element of a
finite multiset. -/
theorem exists_threshold_no_mem_Ioc (s : Multiset ℝ) (x : ℝ) :
    ∃ x' : ℝ, x < x' ∧ ∀ r ∈ s, r ≤ x ∨ x' < r := by
  classical
  set S : Finset ℝ := s.toFinset.filter (x < ·) with hS
  by_cases hSne : S.Nonempty
  · set m : ℝ := S.min' hSne with hm
    have hmS : m ∈ S := Finset.min'_mem S hSne
    have hxm : x < m := by
      simp_all
    refine ⟨(x + m) / 2, by linarith, ?_⟩
    intro r hr
    by_cases hxr : x < r
    · right
      have hrS : r ∈ S := by
        simp_all
      have : m ≤ r := Finset.min'_le S _ hrS
      linarith
    · simp_all
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    have hall : ∀ r ∈ s, ¬ x < r := by
      intro r hr hxr
      have : r ∈ S := by
        simp_all
      grind
    refine ⟨x + 1, by linarith, ?_⟩
    simp_all

/-- Least element of a finite multiset strictly above a threshold, provided one
such element exists. -/
theorem exists_least_mem_gt {α : Type*} [LinearOrder α]
    (s : Multiset α) {x c₀ : α} (hc₀ : c₀ ∈ s)
    (hx : x < c₀) :
    ∃ c ∈ s, x < c ∧ ∀ z ∈ s, x < z → c ≤ z := by
  classical
  set S : Finset α := s.toFinset.filter (x < ·) with hS
  have hSne : S.Nonempty := by
    refine ⟨c₀, ?_⟩
    rw [hS, Finset.mem_filter]
    exact ⟨Multiset.mem_toFinset.mpr hc₀, hx⟩
  refine ⟨S.min' hSne, ?_, ?_, ?_⟩
  · have hmem : S.min' hSne ∈ S := Finset.min'_mem S hSne
    exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp hmem).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
  · intro z hz hxz
    have hzS : z ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Multiset.mem_toFinset.mpr hz, hxz⟩
    exact Finset.min'_le S z hzS

/-- Least combined root of two nonzero polynomials strictly above a threshold,
provided one such root exists. -/
theorem exists_least_isRoot_or_isRoot_gt
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) {x c₀ : ℝ}
    (hc₀ : f.IsRoot c₀ ∨ g.IsRoot c₀) (hx : x < c₀) :
    ∃ c : ℝ, (f.IsRoot c ∨ g.IsRoot c) ∧ x < c ∧
      ∀ z : ℝ, x < z → (f.IsRoot z ∨ g.IsRoot z) → c ≤ z := by
  have hc₀_mem : c₀ ∈ f.roots + g.roots :=
    (mem_roots_add_iff_isRoot_or_isRoot hf hg).mpr hc₀
  obtain ⟨c, hc_mem, hxc, hleast⟩ :=
    exists_least_mem_gt (f.roots + g.roots) hc₀_mem hx
  refine ⟨c, ?_, hxc, ?_⟩
  · exact (mem_roots_add_iff_isRoot_or_isRoot hf hg).mp hc_mem
  · intro z hxz hz
    have hz_mem : z ∈ f.roots + g.roots :=
      (mem_roots_add_iff_isRoot_or_isRoot hf hg).mpr hz
    exact hleast z hz_mem hxz

/-- Push a threshold strictly upward to a common non-root for two polynomials
without crossing any root of either polynomial. -/
theorem exists_common_nonRoot_threshold_no_mem_Ioc
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x < x' ∧ ¬ f.IsRoot x' ∧ ¬ g.IsRoot x' ∧
      (∀ r ∈ f.roots, r ≤ x ∨ x' < r) ∧
      (∀ r ∈ g.roots, r ≤ x ∨ x' < r) := by
  obtain ⟨x', hxx', hgap⟩ := exists_threshold_no_mem_Ioc (f.roots + g.roots) x
  refine ⟨x', hxx', ?_, ?_, ?_, ?_⟩
  · intro hval
    have hroot : f.IsRoot x' ∨ g.IsRoot x' := Or.inl hval
    rcases hgap x' ((mem_roots_add_iff_isRoot_or_isRoot hf hg).mpr hroot) with hx' | hx' <;>
      linarith
  · intro hval
    have hroot : f.IsRoot x' ∨ g.IsRoot x' := Or.inr hval
    rcases hgap x' ((mem_roots_add_iff_isRoot_or_isRoot hf hg).mpr hroot) with hx' | hx' <;>
      linarith
  · intro r hr
    exact hgap r (Multiset.mem_add.mpr (Or.inl hr))
  · intro r hr
    exact hgap r (Multiset.mem_add.mpr (Or.inr hr))

/-- Push a threshold up to a common non-root without changing lower root
counts for either polynomial. -/
theorem exists_nonRoot_threshold_count_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (· ≤ x')).card = (f.roots.filter (· ≤ x)).card ∧
      (g.roots.filter (· ≤ x')).card = (g.roots.filter (· ≤ x)).card := by
  obtain ⟨x', hxx', hfx', hgx', hgap_f, hgap_g⟩ :=
    exists_common_nonRoot_threshold_no_mem_Ioc hf hg x
  refine ⟨x', le_of_lt hxx', ?_, ?_, ?_, ?_⟩
  · simpa [Polynomial.IsRoot.def] using hfx'
  · simpa [Polynomial.IsRoot.def] using hgx'
  · refine (card_filter_le_eq_of_no_mem_Ioc f.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap_f r hr
  · refine (card_filter_le_eq_of_no_mem_Ioc g.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap_g r hr

/-- Push a threshold up to a common non-root without changing upper root
counts for either polynomial. -/
theorem exists_nonRoot_threshold_count_gt_eq
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (x' < ·)).card = (f.roots.filter (x < ·)).card ∧
      (g.roots.filter (x' < ·)).card = (g.roots.filter (x < ·)).card := by
  obtain ⟨x', hxx', hfx', hgx', hgap_f, hgap_g⟩ :=
    exists_common_nonRoot_threshold_no_mem_Ioc hf hg x
  refine ⟨x', le_of_lt hxx', ?_, ?_, ?_, ?_⟩
  · simpa [Polynomial.IsRoot.def] using hfx'
  · simpa [Polynomial.IsRoot.def] using hgx'
  · refine (card_filter_lt_eq_of_no_mem_Ioc f.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap_f r hr
  · refine (card_filter_lt_eq_of_no_mem_Ioc g.roots (le_of_lt hxx') ?_).symm
    intro r hr
    exact hgap_g r hr

/-- Reduce a fixed-threshold lower root-count bound to thresholds that are
roots of neither polynomial. -/
theorem rootCount_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  intro x
  obtain ⟨x', -, hfx', hgx', hfc, hgc⟩ := exists_nonRoot_threshold_count_eq hf hg x
  grind

/-- Absolute-value form of `rootCount_diff_le_one_of_nonRoot`. -/
theorem rootCount_abs_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := rootCount_diff_le_one_of_nonRoot hf hg hbound x
  grind

/-- `IsRoot`-form wrapper for
`rootCount_diff_le_one_of_nonRoot`. -/
theorem rootCount_diff_le_one_of_nonRoot_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  rootCount_diff_le_one_of_nonRoot hf hg fun x hfx hgx =>
    hbound x
      (by simp_all)
      (by simp_all)

/-- Reduce a fixed-threshold upper root-count bound to thresholds that are
roots of neither polynomial. -/
theorem rootCountAbove_diff_le_one_of_nonRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  intro x
  obtain ⟨x', -, hfx', hgx', hfc, hgc⟩ := exists_nonRoot_threshold_count_gt_eq hf hg x
  grind

/-- `IsRoot`-form wrapper for
`rootCountAbove_diff_le_one_of_nonRoot`. -/
theorem rootCountAbove_diff_le_one_of_nonRoot_isRoot
    {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_nonRoot hf hg fun x hfx hgx =>
    hbound x
      (by simp_all)
      (by simp_all)

/-- Max-form projection from a bundled lower/upper root-count gap. -/
theorem rootCount_max_abs_diff_le_one_of_bundled
    {f g : ℝ[X]}
    (h : ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 ∧
      |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1) :
    ∀ x : ℝ,
      max
        |((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card|
        |((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card|
          ≤ 1 := by simp_all

end RealRooted
