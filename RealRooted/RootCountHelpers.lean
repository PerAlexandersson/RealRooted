import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic

/-!
# Generic filter-count helpers

This file records small combinatorial lemmas about cardinalities of
`Multiset.filter`.  They are intentionally polynomial-free so they can be
reused by root-count difference arguments.
-/

namespace RealRooted

/-- Monotonicity of filter count under implication of predicates on the
elements of a multiset. -/
theorem card_filter_le_card_filter_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x) :
    (s.filter p).card ≤ (s.filter q).card := by
  induction s using Quotient.inductionOn
  induction ‹List α› <;> simp_all +decide [List.filter_cons]
  grind

/-- Exact decomposition of the `q`-filter into the `p` part and the
`q ∧ ¬ p` remainder. -/
theorem card_filter_add_card_filter_and_not_eq
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x) :
    (s.filter p).card + (s.filter (fun x => q x ∧ ¬ p x)).card =
      (s.filter q).card := by
  induction s using Quotient.inductionOn
  induction ‹List α› <;> simp_all +decide [List.filter_cons]
  grind

/-- Integer-difference form of the filter-count decomposition. -/
theorem card_filter_sub_card_filter_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x) :
    ((s.filter q).card : ℤ) - (s.filter p).card =
      (s.filter (fun x => q x ∧ ¬ p x)).card := by
  rw [sub_eq_iff_eq_add']
  exact_mod_cast (RealRooted.card_filter_add_card_filter_and_not_eq s p q hpq).symm

/-- Signed nonnegativity form of filter-count monotonicity. -/
theorem int_card_filter_sub_card_filter_nonneg_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x) :
    0 ≤ ((s.filter q).card : ℤ) - (s.filter p).card := by
  have h : ((s.filter p).card : ℤ) ≤ (s.filter q).card :=
    Nat.cast_le.mpr (card_filter_le_card_filter_of_imp s p q hpq)
  linarith

/-- Zero-iff form of the signed filter-count gap under predicate implication. -/
theorem int_card_filter_sub_card_filter_eq_zero_iff_card_filter_eq_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (_hpq : ∀ x ∈ s, p x → q x) :
    (((s.filter q).card : ℤ) - (s.filter p).card = 0) ↔
      (s.filter q).card = (s.filter p).card := by
  rw [sub_eq_zero, Nat.cast_inj]

/-- Forward projection from a zero signed filter-count gap to equality of
filter counts. -/
theorem card_filter_eq_of_int_card_filter_sub_card_filter_eq_zero_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : ((s.filter q).card : ℤ) - (s.filter p).card = 0) :
    (s.filter q).card = (s.filter p).card :=
  (int_card_filter_sub_card_filter_eq_zero_iff_card_filter_eq_of_imp s p q hpq).mp h

/-- Converse projection from equality of filter counts to a zero signed gap. -/
theorem int_card_filter_sub_card_filter_eq_zero_of_card_filter_eq_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter q).card = (s.filter p).card) :
    ((s.filter q).card : ℤ) - (s.filter p).card = 0 :=
  (int_card_filter_sub_card_filter_eq_zero_iff_card_filter_eq_of_imp s p q hpq).mpr h

/-- Nonzero signed-gap form of equality of two nested filter counts. -/
theorem int_card_filter_sub_card_filter_ne_zero_iff_card_filter_ne_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≠ 0 ↔
      (s.filter q).card ≠ (s.filter p).card := by
  constructor
  · intro h hcard
    exact h (int_card_filter_sub_card_filter_eq_zero_of_card_filter_eq_of_imp
      s p q hpq hcard)
  · intro hcard hzero
    exact hcard (card_filter_eq_of_int_card_filter_sub_card_filter_eq_zero_of_imp
      s p q hpq hzero)

/-- Forward projection from a nonzero signed filter-count gap to distinct
filter counts. -/
theorem card_filter_ne_of_int_card_filter_sub_card_filter_ne_zero_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : ((s.filter q).card : ℤ) - (s.filter p).card ≠ 0) :
    (s.filter q).card ≠ (s.filter p).card :=
  (int_card_filter_sub_card_filter_ne_zero_iff_card_filter_ne_of_imp s p q hpq).mp h

/-- Converse projection from distinct filter counts to a nonzero signed gap. -/
theorem int_card_filter_sub_card_filter_ne_zero_of_card_filter_ne_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter q).card ≠ (s.filter p).card) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≠ 0 :=
  (int_card_filter_sub_card_filter_ne_zero_iff_card_filter_ne_of_imp s p q hpq).mpr h

/-- Symmetric remainder-count form of the gap between two filter counts. -/
theorem card_filter_sub_card_filter_symm
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] :
    ((s.filter p).card : ℤ) - (s.filter q).card =
      (s.filter (fun x => p x ∧ ¬ q x)).card -
        (s.filter (fun x => q x ∧ ¬ p x)).card := by
  induction s using Quotient.inductionOn
  induction ‹List α› <;> simp_all +decide [List.filter_cons]
  grind

/-- Bound a filtered-count increase by the size of the `q ∧ ¬ p` remainder. -/
theorem card_filter_le_card_filter_add_of_remainder_le
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] {n : ℕ}
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ n) :
    (s.filter q).card ≤ (s.filter p).card + n := by
  have hsub := RealRooted.card_filter_sub_card_filter_of_imp s p q hpq
  have hle : ((s.filter (fun x => q x ∧ ¬ p x)).card : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast h
  have hgap : ((s.filter q).card : ℤ) ≤ ((s.filter p).card : ℤ) + (n : ℤ) := by
    grind
  exact_mod_cast hgap

/-- The `≤ 1` specialization of `card_filter_le_card_filter_add_of_remainder_le`. -/
theorem card_filter_le_card_filter_succ_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    (s.filter q).card ≤ (s.filter p).card + 1 := by
  convert card_filter_le_card_filter_add_of_remainder_le s p q hpq h using 1

/-- The `q`-count cannot exceed the `p`-count by exactly two if the remainder
has size at most one. -/
theorem card_filter_ne_card_filter_add_two_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    (s.filter q).card ≠ (s.filter p).card + 2 := by
  linarith [card_filter_le_card_filter_add_of_remainder_le s p q hpq h]

/-- Exact "jump of at most one" description of two filter counts. -/
theorem card_filter_eq_or_eq_succ_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    (s.filter q).card = (s.filter p).card ∨
      (s.filter q).card = (s.filter p).card + 1 := by
  have hle := card_filter_le_card_filter_succ_of_remainder_le_one s p q hpq h
  have hge := card_filter_le_card_filter_of_imp s p q hpq
  rcases eq_or_lt_of_le hle with htop | hlt
  · exact Or.inr htop
  · exact Or.inl (le_antisymm (Nat.lt_succ_iff.mp hlt) hge)

/-- Absolute-value integer form of the "jump at most one" filter-count bound. -/
theorem abs_card_filter_sub_card_filter_le_one_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    |((s.filter q).card : ℤ) - (s.filter p).card| ≤ 1 := by
  rcases card_filter_eq_or_eq_succ_of_remainder_le_one s p q hpq h with hq | hq
  · rw [hq]
    norm_num
  · rw [hq]
    norm_num

/-- Signed integer projection of the "jump at most one" filter-count bound. -/
theorem int_card_filter_sub_card_filter_le_one_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≤ 1 :=
  le_of_abs_le
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-!
### Exact-gap-two exclusions

These lemmas turn an absolute gap bound of at most one into exclusions of
signed gaps of exactly `±2`.
-/

/-- Generic integer projection: an absolute gap of at most one rules out a
signed gap of exactly two. -/
theorem sub_ne_two_of_abs_sub_le_one {a b : ℤ} (h : |a - b| ≤ 1) :
    a - b ≠ 2 := by
  have h1 : a - b ≤ |a - b| := le_abs_self _
  intro hc
  rw [hc] at h1 h
  linarith

/-- Generic integer projection: an absolute gap of at most one rules out a
signed gap of negative two. -/
theorem sub_ne_neg_two_of_abs_sub_le_one {a b : ℤ} (h : |a - b| ≤ 1) :
    a - b ≠ -2 := by
  have h1 : -(a - b) ≤ |a - b| := neg_le_abs _
  intro hc
  rw [hc] at h1 h
  linarith

/-- The signed filter-count gap `q - p` is never exactly two when the
`q ∧ ¬ p` remainder has size at most one. -/
theorem int_card_filter_sub_card_filter_ne_two_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≠ 2 :=
  sub_ne_two_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-- The signed filter-count gap `q - p` is never negative two when the
`q ∧ ¬ p` remainder has size at most one. -/
theorem int_card_filter_sub_card_filter_ne_neg_two_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≠ -2 :=
  sub_ne_neg_two_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-- The reversed signed filter-count gap `p - q` is never exactly two when the
`q ∧ ¬ p` remainder has size at most one. -/
theorem int_card_filter_sub_card_filter_ne_two_symm_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter p).card : ℤ) - (s.filter q).card ≠ 2 := by
  have hne :=
    int_card_filter_sub_card_filter_ne_neg_two_of_remainder_le_one s p q hpq h
  intro hc
  exact hne (by linarith)

/-- The reversed signed filter-count gap `p - q` is never negative two when the
`q ∧ ¬ p` remainder has size at most one. -/
theorem int_card_filter_sub_card_filter_ne_neg_two_symm_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter p).card : ℤ) - (s.filter q).card ≠ -2 := by
  have hne :=
    int_card_filter_sub_card_filter_ne_two_of_remainder_le_one s p q hpq h
  intro hc
  exact hne (by linarith)

/-!
### Bundled exact-gap-two exclusions

These direct #42 wrappers bundle the two `±2` exclusions, and their symmetric
forms, so no-gap-two call sites do not have to invoke the one-sided lemmas
twice.
-/

/-- An absolute gap of at most one rules out signed gaps `2` and `-2`. -/
theorem sub_ne_two_and_neg_two_of_abs_sub_le_one {a b : ℤ} (h : |a - b| ≤ 1) :
    a - b ≠ 2 ∧ a - b ≠ -2 :=
  ⟨sub_ne_two_of_abs_sub_le_one h, sub_ne_neg_two_of_abs_sub_le_one h⟩

/-- An absolute gap of at most one rules out a signed gap of exactly two in
both orientations `a - b` and `b - a`. -/
theorem sub_ne_two_and_symm_sub_ne_two_of_abs_sub_le_one {a b : ℤ}
    (h : |a - b| ≤ 1) : a - b ≠ 2 ∧ b - a ≠ 2 := by
  constructor <;> intro H <;> linarith [abs_le.mp h]

/-- Bundled filter-count form: if the `q ∧ ¬ p` remainder has size at most
one, the signed gap `q - p` is neither two nor negative two. -/
theorem int_card_filter_sub_card_filter_ne_two_and_neg_two_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≠ 2 ∧
      ((s.filter q).card : ℤ) - (s.filter p).card ≠ -2 :=
  sub_ne_two_and_neg_two_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-- Bundled directional filter-count form matching the no-gap-two statements:
neither orientation of the signed count gap equals two. -/
theorem int_card_filter_sub_card_filter_ne_two_both_orientations_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≠ 2 ∧
      ((s.filter p).card : ℤ) - (s.filter q).card ≠ 2 :=
  sub_ne_two_and_symm_sub_ne_two_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-- Natural-number reversed form: the `p`-count never exceeds the `q`-count by
two.  This holds from monotonicity alone and complements
`card_filter_ne_card_filter_add_two_of_remainder_le_one`. -/
theorem card_filter_symm_ne_card_filter_add_two_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x) :
    (s.filter p).card ≠ (s.filter q).card + 2 := by
  have hle := card_filter_le_card_filter_of_imp s p q hpq
  intro hc
  rw [hc] at hle
  linarith

/-!
### Two-sided gap bounds and `|a - b| ≤ 1`

These wrappers move no-gap call sites between two one-sided signed bounds, an
absolute-value bound, and equality-or-successor alternatives.
-/

/-- Package two one-sided integer bounds as an absolute bound. -/
theorem abs_sub_le_one_of_sub_le_one_of_symm {a b : ℤ}
    (h1 : a - b ≤ 1) (h2 : b - a ≤ 1) :
    |a - b| ≤ 1 :=
  abs_le.mpr ⟨by linarith, h1⟩

/-- Unpackage an absolute bound into two one-sided integer bounds. -/
theorem sub_le_one_and_symm_sub_le_one_of_abs_sub_le_one {a b : ℤ}
    (h : |a - b| ≤ 1) :
    a - b ≤ 1 ∧ b - a ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  exact ⟨hhi, by linarith⟩

/-- Exclude signed gaps `±2` from two one-sided integer bounds. -/
theorem sub_ne_two_and_neg_two_of_sub_le_one_of_symm {a b : ℤ}
    (h1 : a - b ≤ 1) (h2 : b - a ≤ 1) :
    a - b ≠ 2 ∧ a - b ≠ -2 :=
  sub_ne_two_and_neg_two_of_abs_sub_le_one
    (abs_sub_le_one_of_sub_le_one_of_symm h1 h2)

/-- Exclude a gap of `2` in both orientations from two one-sided bounds. -/
theorem sub_ne_two_and_symm_sub_ne_two_of_sub_le_one_of_symm {a b : ℤ}
    (h1 : a - b ≤ 1) (h2 : b - a ≤ 1) :
    a - b ≠ 2 ∧ b - a ≠ 2 :=
  sub_ne_two_and_symm_sub_ne_two_of_abs_sub_le_one
    (abs_sub_le_one_of_sub_le_one_of_symm h1 h2)

/-- An absolute gap at most one forces equality or one-step offset. -/
theorem eq_or_eq_add_one_or_eq_sub_one_of_abs_sub_le_one {a b : ℤ}
    (h : |a - b| ≤ 1) :
    a = b ∨ a = b + 1 ∨ a = b - 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h1 : a + 1 ≤ b := Int.add_one_le_iff.mpr hlt
    exact Or.inr (Or.inr (le_antisymm (by linarith) (by linarith)))
  · exact Or.inl heq
  · have h1 : b + 1 ≤ a := Int.add_one_le_iff.mpr hgt
    exact Or.inr (Or.inl (le_antisymm (by linarith) (by linarith)))

/-- Equality-or-successor trichotomy from two one-sided integer bounds. -/
theorem eq_or_eq_add_one_or_eq_sub_one_of_sub_le_one_of_symm {a b : ℤ}
    (h1 : a - b ≤ 1) (h2 : b - a ≤ 1) :
    a = b ∨ a = b + 1 ∨ a = b - 1 :=
  eq_or_eq_add_one_or_eq_sub_one_of_abs_sub_le_one
    (abs_sub_le_one_of_sub_le_one_of_symm h1 h2)

/-- Remainder-driven two-sided filter-count bound. -/
theorem card_filter_sub_le_one_and_symm_sub_le_one_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) - (s.filter p).card ≤ 1 ∧
      ((s.filter p).card : ℤ) - (s.filter q).card ≤ 1 :=
  sub_le_one_and_symm_sub_le_one_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-- Equality-or-successor trichotomy at the filter-count level. -/
theorem card_filter_eq_or_eq_add_one_or_eq_sub_one_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    ((s.filter q).card : ℤ) = (s.filter p).card ∨
      ((s.filter q).card : ℤ) = (s.filter p).card + 1 ∨
      ((s.filter q).card : ℤ) = (s.filter p).card - 1 :=
  eq_or_eq_add_one_or_eq_sub_one_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-!
### Sharpening `≤ 2` to `≤ 1` and natAbs packaging

These wrappers turn a "gap at most two" bound together with an exclusion of an
exact gap of two into the sharp "gap at most one" bound, and repackage signed
gaps as `Int.natAbs` distances.  They let no-gap-two call sites avoid repeated
local integer case splits.
-/

/-- An integer bounded by two and different from two is bounded by one. -/
theorem int_le_one_of_le_two_of_ne_two {z : ℤ} (hle : z ≤ 2) (hne : z ≠ 2) :
    z ≤ 1 :=
  Int.lt_add_one_iff.mp (by simpa using lt_of_le_of_ne hle hne)

/-- Two-orientation form: paired `≤ 2` bounds with paired exclusions of an
exact gap of two yield paired `≤ 1` bounds.  This matches the shape produced by
the no-gap-two leaves. -/
theorem sub_le_one_and_symm_of_le_two_and_ne_two {a b : ℤ}
    (hle : a - b ≤ 2 ∧ b - a ≤ 2) (hne : a - b ≠ 2 ∧ b - a ≠ 2) :
    a - b ≤ 1 ∧ b - a ≤ 1 :=
  ⟨int_le_one_of_le_two_of_ne_two hle.1 hne.1,
    int_le_one_of_le_two_of_ne_two hle.2 hne.2⟩

/-- Absolute-value form of the sharpening: `|a - b| ≤ 2` with both exact gaps
`2` and `-2` excluded gives `|a - b| ≤ 1`. -/
theorem abs_sub_le_one_of_abs_le_two_of_ne_two_of_ne_neg_two {a b : ℤ}
    (hle : |a - b| ≤ 2) (hne : a - b ≠ 2) (hne' : a - b ≠ -2) :
    |a - b| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hle
  refine abs_le.mpr ⟨?_, int_le_one_of_le_two_of_ne_two hhi hne⟩
  have h : -(a - b) ≤ 1 :=
    int_le_one_of_le_two_of_ne_two (by linarith) (fun hc => hne' (by linarith))
  linarith

/-- `Int.natAbs` packaging of a signed gap of at most one. -/
theorem natAbs_sub_le_one_of_abs_sub_le_one {a b : ℤ} (h : |a - b| ≤ 1) :
    (a - b).natAbs ≤ 1 := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- Recover the two-sided integer gap bound from an `Int.natAbs` bound. -/
theorem abs_sub_le_one_of_natAbs_sub_le_one {a b : ℤ}
    (h : (a - b).natAbs ≤ 1) : |a - b| ≤ 1 := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

/-- `Int.natAbs` distance packaging of the "jump at most one" filter-count
bound. -/
theorem natAbs_card_filter_sub_card_filter_le_one_of_remainder_le_one
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x ∈ s, p x → q x)
    (h : (s.filter (fun x => q x ∧ ¬ p x)).card ≤ 1) :
    (((s.filter q).card : ℤ) - (s.filter p).card).natAbs ≤ 1 :=
  natAbs_sub_le_one_of_abs_sub_le_one
    (abs_card_filter_sub_card_filter_le_one_of_remainder_le_one s p q hpq h)

/-- Sharpened filter-count leaf: two-orientation `≤ 2` count bounds together
with exclusion of an exact gap of two collapse to the paired `≤ 1` bounds. -/
theorem card_filter_sub_le_one_and_symm_of_le_two_and_ne_two
    {α : Type*} (s t : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hle : ((s.filter p).card : ℤ) - (t.filter q).card ≤ 2 ∧
      ((t.filter q).card : ℤ) - (s.filter p).card ≤ 2)
    (hne : ((s.filter p).card : ℤ) - (t.filter q).card ≠ 2 ∧
      ((t.filter q).card : ℤ) - (s.filter p).card ≠ 2) :
    ((s.filter p).card : ℤ) - (t.filter q).card ≤ 1 ∧
      ((t.filter q).card : ℤ) - (s.filter p).card ≤ 1 :=
  sub_le_one_and_symm_of_le_two_and_ne_two hle hne

/-!
### Parity/evenness sharpening

When a signed gap is odd, both exact gaps `±2` are automatically excluded, so a
raw `≤ 2` or `|·| ≤ 2` bound sharpens to the `≤ 1` conclusion without any extra
exclusion hypotheses.  Conversely, an even gap with `|·| ≤ 1` must vanish.
-/

/-- An integer bounded by two that is odd is bounded by one. -/
theorem int_le_one_of_le_two_of_odd {z : ℤ} (hle : z ≤ 2) (hodd : Odd z) :
    z ≤ 1 := by
  have hne : z ≠ 2 := by
    rintro rfl
    exact (Int.not_odd_iff_even.mpr even_two) hodd
  exact int_le_one_of_le_two_of_ne_two hle hne

/-- An odd signed gap is never exactly two. -/
theorem sub_ne_two_of_odd_sub {a b : ℤ} (h : Odd (a - b)) : a - b ≠ 2 := by
  intro hc
  rw [hc] at h
  exact (Int.not_odd_iff_even.mpr even_two) h

/-- An odd signed gap is never negative two. -/
theorem sub_ne_neg_two_of_odd_sub {a b : ℤ} (h : Odd (a - b)) : a - b ≠ -2 := by
  intro hc
  rw [hc] at h
  exact (Int.not_odd_iff_even.mpr even_two.neg) h

/-- An odd signed gap excludes both exact gaps `2` and `-2`. -/
theorem sub_ne_two_and_neg_two_of_odd_sub {a b : ℤ} (h : Odd (a - b)) :
    a - b ≠ 2 ∧ a - b ≠ -2 :=
  ⟨sub_ne_two_of_odd_sub h, sub_ne_neg_two_of_odd_sub h⟩

/-- Parity sharpening: an absolute gap of at most two that is odd is an
absolute gap of at most one. -/
theorem abs_sub_le_one_of_abs_le_two_of_odd_sub {a b : ℤ}
    (hle : |a - b| ≤ 2) (h : Odd (a - b)) : |a - b| ≤ 1 :=
  abs_sub_le_one_of_abs_le_two_of_ne_two_of_ne_neg_two hle
    (sub_ne_two_of_odd_sub h) (sub_ne_neg_two_of_odd_sub h)

/-- `Int.natAbs` parity sharpening from an absolute gap bound. -/
theorem natAbs_sub_le_one_of_abs_le_two_of_odd_sub {a b : ℤ}
    (hle : |a - b| ≤ 2) (h : Odd (a - b)) : (a - b).natAbs ≤ 1 :=
  natAbs_sub_le_one_of_abs_sub_le_one
    (abs_sub_le_one_of_abs_le_two_of_odd_sub hle h)

/-- `Int.natAbs` parity sharpening from a `natAbs` gap bound. -/
theorem natAbs_sub_le_one_of_natAbs_le_two_of_odd_sub {a b : ℤ}
    (hle : (a - b).natAbs ≤ 2) (h : Odd (a - b)) : (a - b).natAbs ≤ 1 := by
  refine natAbs_sub_le_one_of_abs_le_two_of_odd_sub ?_ h
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

/-- An even signed gap of absolute value at most one must vanish. -/
theorem sub_eq_zero_of_abs_sub_le_one_of_even_sub {a b : ℤ}
    (h : |a - b| ≤ 1) (he : Even (a - b)) : a - b = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  obtain ⟨k, hk⟩ := he
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : k + 1 ≤ 0 := Int.add_one_le_iff.mpr hk0
    exfalso
    linarith
  · rw [hk, hk0]
    ring
  · have : (1 : ℤ) ≤ k := Int.add_one_le_iff.mpr hk0
    exfalso
    linarith

/-- Equality form of the even-gap collapse. -/
theorem eq_of_abs_sub_le_one_of_even_sub {a b : ℤ}
    (h : |a - b| ≤ 1) (he : Even (a - b)) : a = b := by
  have hz := sub_eq_zero_of_abs_sub_le_one_of_even_sub h he
  exact sub_eq_zero.mp hz

/-- `Int.natAbs` form of the exact-gap-two sharpening. -/
theorem natAbs_sub_le_one_of_abs_le_two_of_ne_two_of_ne_neg_two {a b : ℤ}
    (hle : |a - b| ≤ 2) (hne : a - b ≠ 2) (hne' : a - b ≠ -2) :
    (a - b).natAbs ≤ 1 :=
  natAbs_sub_le_one_of_abs_sub_le_one
    (abs_sub_le_one_of_abs_le_two_of_ne_two_of_ne_neg_two hle hne hne')

/-- Filter-count parity sharpening: an absolute count gap of at most two that
is odd is a count gap of at most one. -/
theorem abs_card_filter_sub_card_filter_le_one_of_abs_le_two_of_odd
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hle : |((s.filter q).card : ℤ) - (s.filter p).card| ≤ 2)
    (hodd : Odd (((s.filter q).card : ℤ) - (s.filter p).card)) :
    |((s.filter q).card : ℤ) - (s.filter p).card| ≤ 1 :=
  abs_sub_le_one_of_abs_le_two_of_odd_sub hle hodd

/-- `Int.natAbs` filter-count parity sharpening. -/
theorem natAbs_card_filter_sub_card_filter_le_one_of_abs_le_two_of_odd
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hle : |((s.filter q).card : ℤ) - (s.filter p).card| ≤ 2)
    (hodd : Odd (((s.filter q).card : ℤ) - (s.filter p).card)) :
    (((s.filter q).card : ℤ) - (s.filter p).card).natAbs ≤ 1 :=
  natAbs_sub_le_one_of_abs_le_two_of_odd_sub hle hodd

end RealRooted
