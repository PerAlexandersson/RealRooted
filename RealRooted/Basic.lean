import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import RealRooted.Mathlib.Data.Nat.Cast.Basic
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.Mathlib.Data.List.Interleave

/-!
# Real-rootedness and interlacing of polynomials

This file contains the foundational definitions for real-rootedness,
interlacing, proper position, and Sturm sequences of univariate real
polynomials.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma card_roots_of_splits {p : ℝ[X]} (h : p.Splits) : p.roots.card = p.natDegree :=
  splits_iff_card_roots.mp h

lemma splits_of_card_roots {p : ℝ[X]} (h : p.roots.card = p.natDegree) : p.Splits :=
  splits_iff_card_roots.mpr h

lemma ne_zero_and_splits_of_ne_zero_and_card_roots {p : ℝ[X]}
    (h_ne : p ≠ 0) (h_card : p.roots.card = p.natDegree) : p ≠ 0 ∧ p.Splits :=
  ⟨h_ne, splits_of_card_roots h_card⟩

lemma ne_zero_and_card_roots_of_ne_zero_and_splits {p : ℝ[X]}
    (h_ne : p ≠ 0) (h_splits : p.Splits) : p ≠ 0 ∧ p.roots.card = p.natDegree :=
  ⟨h_ne, card_roots_of_splits h_splits⟩

lemma eq_zero_or_ne_zero_and_splits_iff_eq_zero_or_ne_zero_and_card_roots (p : ℝ[X]) :
    (p = 0 ∨ (p ≠ 0 ∧ p.Splits)) ↔
      (p = 0 ∨ (p ≠ 0 ∧ p.roots.card = p.natDegree)) := by
  constructor <;> rintro (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr (ne_zero_and_card_roots_of_ne_zero_and_splits h.1 h.2)
  · exact Or.inl rfl
  · exact Or.inr (ne_zero_and_splits_of_ne_zero_and_card_roots h.1 h.2)

lemma natDegree_X_add_one_pow_le (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).natDegree ≤ n := by
  have hX1 : (X + 1 : ℝ[X]).natDegree ≤ 1 := by
    rw [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp, Polynomial.natDegree_X_add_C]
  simpa [one_mul] using Polynomial.natDegree_pow_le_of_le n hX1

lemma support_X_add_one_pow_eq_range (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).support = Finset.range (n + 1) := by
  ext k
  rw [mem_support_iff, coeff_X_add_one_pow, Finset.mem_range, Nat.lt_succ_iff]
  by_cases hk : k ≤ n
  · exact iff_of_true (Nat.cast_choose_ne_zero (R := ℝ) hk) hk
  · have hchoose_nat : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)
    have hchoose : (Nat.choose n k : ℝ) = 0 := by simp [hchoose_nat]
    exact iff_of_false (fun hne => hne hchoose) hk

/-! ## Root interleaving predicates on sorted lists -/

/-- **Differ-by-1 interleaving**: `ss` (length n−1) interleaves into `rs` (length n).
    Pattern: r₁ ≤ s₁ ≤ r₂ ≤ s₂ ≤ … ≤ sₙ₋₁ ≤ rₙ.
    The last element of `rs` is the rightmost root. -/
def ListInterlaces : List ℝ → List ℝ → Prop
  | [], [] => True
  | [], [_] => True
  | s :: ss, r₁ :: r₂ :: rs => r₁ ≤ s ∧ s ≤ r₂ ∧ ListInterlaces ss (r₂ :: rs)
  | _, _ => False

/-- **Same-degree interleaving**: `ss` (length n) alternates with `rs` (length n).
    Pattern: s₁ ≤ r₁ ≤ s₂ ≤ r₂ ≤ … ≤ sₙ ≤ rₙ.
    The last element of `rs` is the rightmost root. -/
def ListAlternates : List ℝ → List ℝ → Prop
  | [], [] => True
  | s :: ss, r :: rs => s ≤ r ∧ ListInterlaces ss (r :: rs)
  | _, _ => False

lemma listInterlaces_iff_interleaves_of_length :
    ∀ {ss rs : List ℝ}, ss.length + 1 = rs.length →
      (ListInterlaces ss rs ↔ List.Interleaves (fun x y : ℝ => x ≤ y) ss rs)
  | [], [], h => by lia
  | [], [_], _ => by simp [ListInterlaces]
  | [], _ :: _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, [_], h => by simp at h
  | s :: ss, r₁ :: r₂ :: rs, h => by
      have htail : ss.length + 1 = (r₂ :: rs).length := by simpa using h
      constructor
      · rintro ⟨hr₁s, hsr₂, htail_old⟩
        exact List.Interleaves.cons_symm
          (List.Interleaves.cons_symm
            ((listInterlaces_iff_interleaves_of_length htail).1 htail_old) hsr₂)
          hr₁s
      · intro hnew
        rw [List.interleaves_iff] at hnew
        rcases hnew with hbad | hbad | ⟨l₁, l₂, b, hmid, a, hab, hleft, hright⟩
        · lia
        · lia
        · simp only [List.cons.injEq] at hleft hright
          rcases hleft with ⟨rfl, rfl⟩
          rcases hright with ⟨rfl, rfl⟩
          rw [List.interleaves_iff] at hmid
          rcases hmid with hbad | hbad | ⟨l₁, l₂, b, htail_new, a, hsr₂, hleft, hright⟩
          · lia
          · lia
          · simp only [List.cons.injEq] at hleft hright
            rcases hleft with ⟨rfl, rfl⟩
            rcases hright with ⟨rfl, rfl⟩
            exact ⟨hab, hsr₂, (listInterlaces_iff_interleaves_of_length htail).2 htail_new⟩

lemma listAlternates_iff_interleaves_of_length :
    ∀ {ss rs : List ℝ}, ss.length = rs.length →
      (ListAlternates ss rs ↔ List.Interleaves (fun x y : ℝ => x ≤ y) rs ss)
  | [], [], _ => by simp [ListAlternates]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | s :: ss, r :: rs, h => by
      have htail : ss.length + 1 = (r :: rs).length := by simpa using h
      constructor
      · rintro ⟨hsr, htail_old⟩
        exact List.Interleaves.cons_symm
          ((listInterlaces_iff_interleaves_of_length htail).1 htail_old) hsr
      · intro hnew
        rw [List.interleaves_iff] at hnew
        rcases hnew with hbad | hbad | ⟨l₁, l₂, b, htail_new, a, hsr, hleft, hright⟩
        · lia
        · lia
        · simp only [List.cons.injEq] at hleft hright
          rcases hleft with ⟨rfl, rfl⟩
          rcases hright with ⟨rfl, rfl⟩
          exact ⟨hsr, (listInterlaces_iff_interleaves_of_length htail).2 htail_new⟩

lemma listInterlaces_of_interleaves_of_length {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (h : List.Interleaves (fun x y : ℝ => x ≤ y) ss rs) :
    ListInterlaces ss rs :=
  (listInterlaces_iff_interleaves_of_length hlen).2 h

lemma interleaves_of_listInterlaces_of_length {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length) (h : ListInterlaces ss rs) :
    List.Interleaves (fun x y : ℝ => x ≤ y) ss rs :=
  (listInterlaces_iff_interleaves_of_length hlen).1 h

lemma listAlternates_of_interleaves_of_length {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (h : List.Interleaves (fun x y : ℝ => x ≤ y) rs ss) :
    ListAlternates ss rs :=
  (listAlternates_iff_interleaves_of_length hlen).2 h

lemma interleaves_of_listAlternates_of_length {ss rs : List ℝ}
    (hlen : ss.length = rs.length) (h : ListAlternates ss rs) :
    List.Interleaves (fun x y : ℝ => x ≤ y) rs ss :=
  (listAlternates_iff_interleaves_of_length hlen).1 h

/-- In a nonempty right-hand list, each left entry of a weak interlacing is at
most the corresponding later right entry. -/
lemma listInterlaces_forall₂_le_tail :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) →
      List.Forall₂ (fun s t : ℝ => s ≤ t) ss rs
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp [ListInterlaces] at h
  | _ :: _, [], _, h => by simp [ListInterlaces] at h
  | s :: ss, r₂ :: rs, r₁, h => by
      rcases h with ⟨_, hsr₂, htail⟩
      exact List.Forall₂.cons hsr₂ (listInterlaces_forall₂_le_tail htail)

/-- Same-degree weak alternation gives pairwise coordinate inequalities. -/
lemma listAlternates_forall₂_le :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      List.Forall₂ (fun s t : ℝ => s ≤ t) ss rs
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [ListAlternates] at h
  | _ :: _, [], h => by simp [ListAlternates] at h
  | s :: ss, r :: rs, h => by
      rcases h with ⟨hsr, htail⟩
      exact List.Forall₂.cons hsr (listInterlaces_forall₂_le_tail htail)

private theorem getD_reverse_aux (l : List ℝ) (j : ℕ) (hj : j < l.length) :
    l.reverse.getD j 0 = l.getD (l.length - 1 - j) 0 := by
  have hj' : j < l.reverse.length := by simpa using hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj', List.getElem?_eq_getElem (by lia)]
  simp [List.getElem_reverse]

/-- Interior step bounds extracted from a differ-by-1 list interlacing. -/
theorem listInterlaces_getD_bounds :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ss.length + 1 = rs.length →
      (∀ i, i < ss.length → rs.getD i 0 ≤ ss.getD i 0) ∧
      (∀ i, i < ss.length → ss.getD i 0 ≤ rs.getD (i + 1) 0)
  | [], [], _, hlen => by simp at hlen
  | [], [_], _, _ => by refine ⟨?_, ?_⟩ <;> (intro i hi; simp at hi)
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _ => by simp [ListInterlaces] at h
  | _ :: ss', r₁ :: r₂ :: rs', h, hlen => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := h
      have hlen' : ss'.length + 1 = (r₂ :: rs').length := by simpa using hlen
      obtain ⟨ih1, ih2⟩ := listInterlaces_getD_bounds ss' (r₂ :: rs') htail hlen'
      refine ⟨?_, ?_⟩
      · intro i hi
        match i with
        | 0 => simpa using hr₁s
        | k + 1 =>
            have hk : k < ss'.length := by
              simp at hi
              lia
            simpa using ih1 k hk
      · intro i hi
        match i with
        | 0 => simpa using hsr₂
        | k + 1 =>
            have hk : k < ss'.length := by
              simp at hi
              lia
            simpa using ih2 k hk

/-- Interior step bounds extracted from a same-degree list alternation. -/
theorem listAlternates_getD_bounds :
    ∀ (ss rs : List ℝ), ListAlternates ss rs → ss.length = rs.length →
      (∀ i, i < ss.length → ss.getD i 0 ≤ rs.getD i 0) ∧
      (∀ i, i + 1 < ss.length → rs.getD i 0 ≤ ss.getD (i + 1) 0)
  | [], [], _, _ => by refine ⟨?_, ?_⟩ <;> (intro i hi; simp at hi)
  | [], _ :: _, h, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _ => by simp [ListAlternates] at h
  | _ :: ss', r :: rs', h, hlen => by
      obtain ⟨hsr, htail⟩ := h
      have hlen' : ss'.length + 1 = (r :: rs').length := by simpa using hlen
      obtain ⟨ih1, ih2⟩ := listInterlaces_getD_bounds ss' (r :: rs') htail hlen'
      refine ⟨?_, ?_⟩
      · intro i hi
        match i with
        | 0 => simpa using hsr
        | k + 1 =>
            have hk : k < ss'.length := by
              simp at hi
              lia
            simpa using ih2 k hk
      · intro i hi
        match i with
        | 0 =>
            have h0 : 0 < ss'.length := by
              simp at hi
              lia
            simpa using ih1 0 h0
        | k + 1 =>
            have hk : k + 1 < ss'.length := by
              simp at hi
              lia
            simpa using ih1 (k + 1) hk

/-- Same-degree alternation in either direction gives descending root crossing
inequalities for the reversed lists. -/
theorem rootCrossing_of_listAlternates_or {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs ∨ ListAlternates rs ss) :
    (∀ j, 1 ≤ j → j < ss.length →
        rs.reverse.getD j 0 ≤ ss.reverse.getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < ss.length →
        ss.reverse.getD j 0 ≤ rs.reverse.getD (j - 1) 0) := by
  rcases halt with halt | halt
  · obtain ⟨hA, hB⟩ := listAlternates_getD_bounds ss rs halt hlen
    refine ⟨?_, ?_⟩
    · intro j hj1 hj2
      rw [getD_reverse_aux rs j (by lia), getD_reverse_aux ss (j - 1) (by lia)]
      have e1 : rs.length - 1 - j = ss.length - 1 - j := by rw [hlen]
      have e2 : ss.length - 1 - (j - 1) = (ss.length - 1 - j) + 1 := by lia
      rw [e1, e2]
      exact hB (ss.length - 1 - j) (by lia)
    · intro j hj1 hj2
      rw [getD_reverse_aux ss j (by lia), getD_reverse_aux rs (j - 1) (by lia)]
      have e2 : rs.length - 1 - (j - 1) = (ss.length - 1 - j) + 1 := by lia
      rw [e2]
      exact le_trans
        (le_trans (hA (ss.length - 1 - j) (by lia)) (hB (ss.length - 1 - j) (by lia)))
        (hA (ss.length - 1 - j + 1) (by lia))
  · obtain ⟨hA, hB⟩ := listAlternates_getD_bounds rs ss halt hlen.symm
    refine ⟨?_, ?_⟩
    · intro j hj1 hj2
      rw [getD_reverse_aux rs j (by lia), getD_reverse_aux ss (j - 1) (by lia)]
      have e2 : ss.length - 1 - (j - 1) = (rs.length - 1 - j) + 1 := by lia
      rw [e2]
      exact le_trans
        (le_trans (hA (rs.length - 1 - j) (by lia)) (hB (rs.length - 1 - j) (by lia)))
        (hA (rs.length - 1 - j + 1) (by lia))
    · intro j hj1 hj2
      rw [getD_reverse_aux ss j (by lia), getD_reverse_aux rs (j - 1) (by lia)]
      have e1 : ss.length - 1 - j = rs.length - 1 - j := by rw [hlen]
      have e2 : rs.length - 1 - (j - 1) = (rs.length - 1 - j) + 1 := by lia
      rw [e1, e2]
      exact hB (rs.length - 1 - j) (by lia)

/-- Same-degree weak alternation orders the sums of the two root lists. -/
lemma listAlternates_sum_le {ss rs : List ℝ} (h : ListAlternates ss rs) :
    ss.sum ≤ rs.sum :=
  List.Forall₂.sum_le_sum (listAlternates_forall₂_le h)

/-- Coordinatewise inequalities between two real lists, together with the
opposite inequality on sums, force the two lists to be equal. -/
lemma list_eq_of_forall₂_le_of_sum_ge :
    ∀ {ss rs : List ℝ}, List.Forall₂ (fun s t : ℝ => s ≤ t) ss rs →
      rs.sum ≤ ss.sum → ss = rs
  | [], [], _, _ => rfl
  | s :: ss, r :: rs, hle, hsum => by
      cases hle with
      | cons hsr htail =>
          simp only [List.sum_cons] at hsum
          have htail_sum : ss.sum ≤ rs.sum := List.Forall₂.sum_le_sum htail
          have hrs : r ≤ s := by linarith
          have hs_eq : s = r := le_antisymm hsr hrs
          have htail_ge : rs.sum ≤ ss.sum := by linarith
          have htail_eq : ss = rs :=
            list_eq_of_forall₂_le_of_sum_ge htail htail_ge
          simp [hs_eq, htail_eq]

/-- If same-degree weak alternation has the opposite inequality on sums, then
the two lists are equal, so the alternation can be reversed. -/
lemma listAlternates_symm_of_sum_le {ss rs : List ℝ}
    (halt : ListAlternates ss rs) (hsum : rs.sum ≤ ss.sum) :
    ListAlternates rs ss := by
  have h_eq : ss = rs :=
    list_eq_of_forall₂_le_of_sum_ge (listAlternates_forall₂_le halt) hsum
  subst ss
  simpa using halt

lemma listInterlaces_left_le_of_right_le {ss rs : List ℝ} {c : ℝ}
    (hint : ListInterlaces ss rs)
    (hrs : ∀ r ∈ rs, r ≤ c) :
    ∀ s ∈ ss, s ≤ c := by
  induction ss generalizing rs with
  | nil =>
      simp
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp [ListInterlaces] at hint
      | cons r₁ rs' =>
          cases rs' with
          | nil =>
              simp [ListInterlaces] at hint
          | cons r₂ rs'' =>
              rcases hint with ⟨_, hs_r₂, htail⟩
              intro t ht
              simp only [List.mem_cons] at ht
              rcases ht with rfl | ht
              · exact le_trans hs_r₂ (hrs r₂ (by simp))
              · grind

lemma listInterlaces_all_le_getLast {ss rs : List ℝ}
    (hrs_ne : rs ≠ [])
    (hrs : rs.Pairwise (· ≤ ·))
    (hint : ListInterlaces ss rs) :
    ∀ s ∈ ss, s ≤ rs.getLast hrs_ne :=
  listInterlaces_left_le_of_right_le hint
    (fun _ hr => List.Pairwise.rel_getLast hrs hr)

lemma listAlternates_left_le_of_right_le {ss rs : List ℝ} {c : ℝ}
    (halt : ListAlternates ss rs)
    (hrs : ∀ r ∈ rs, r ≤ c) :
    ∀ s ∈ ss, s ≤ c := by
  induction ss generalizing rs with
  | nil =>
      simp
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp [ListAlternates] at halt
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact le_trans hsr (hrs r (by simp))
          · exact listInterlaces_left_le_of_right_le htail
              (fun x hx => hrs x (by lia)) t ht

lemma listAlternates_all_le_getLast {ss rs : List ℝ}
    (hrs_ne : rs ≠ [])
    (hrs : rs.Pairwise (· ≤ ·))
    (halt : ListAlternates ss rs) :
    ∀ s ∈ ss, s ≤ rs.getLast hrs_ne :=
  listAlternates_left_le_of_right_le halt
    (fun _ hr => List.Pairwise.rel_getLast hrs hr)

/-! ## Threshold counts for interlacing root lists

The pure combinatorial content behind issue #42: for a differ-by-one root
interlacing `ListInterlaces ss rs`, if the number of roots strictly above a
threshold `x` has the same parity on both sides, then those upper counts are
equal, and the number of roots at most `x` in `rs` is exactly one more than in
`ss`. -/

/-- Monotonicity of the strict-upper-threshold count under pointwise `≤`. -/
lemma filter_lt_length_le_of_forall₂_le {x : ℝ} {l₁ l₂ : List ℝ}
    (h : List.Forall₂ (· ≤ ·) l₁ l₂) :
    (l₁.filter (fun a => x < a)).length ≤ (l₂.filter (fun a => x < a)).length := by
  induction h with
  | nil =>
      simp
  | @cons a b l₁ l₂ hab _ ih =>
      by_cases hb : x < b
      · by_cases ha : x < a <;> simp [ha, hb] <;> lia
      · have ha : ¬ x < a := fun h' => hb (lt_of_lt_of_le h' hab)
        simpa [ha, hb] using ih

/-- The lower/upper strict-threshold counts of a list partition its length. -/
lemma filter_le_add_filter_lt_length {x : ℝ} (l : List ℝ) :
    (l.filter (fun a => a ≤ x)).length +
        (l.filter (fun a => x < a)).length = l.length := by
  rw [List.length_eq_length_filter_add (l := l) (f := fun a => a ≤ x)]
  congr 1
  exact congrArg List.length <| List.filter_congr (l := l) (by
    intro a _
    by_cases h : a ≤ x
    · simp [h, not_lt_of_ge h]
    · simp [h, not_le.mp h])

/-- In a differ-by-one interlacing, the reversed pairing `rₖ ≤ sₖ` holds:
each entry of `rs.dropLast` is bounded by the corresponding entry of `ss`. -/
lemma listInterlaces_dropLast_forall₂_le :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs → ss.length + 1 = rs.length →
      List.Forall₂ (· ≤ ·) rs.dropLast ss
  | [], [], _, hlen => by simp at hlen
  | [], [_], _, _ => by simp
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _ => by simp [ListInterlaces] at h
  | s :: ss', r₁ :: r₂ :: rs', h, hlen => by
      obtain ⟨hr₁s, _, htail⟩ := h
      have hlen' : ss'.length + 1 = (r₂ :: rs').length := by
        simpa using hlen
      have ih := listInterlaces_dropLast_forall₂_le htail hlen'
      simpa [List.dropLast] using List.Forall₂.cons hr₁s ih

/-- Upper-threshold count of `ss` is at most that of `rs` in a differ-by-one
interlacing. -/
lemma listInterlaces_filter_lt_le {x : ℝ} {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length) :
    (ss.filter (fun a => x < a)).length ≤ (rs.filter (fun a => x < a)).length := by
  cases rs with
  | nil =>
      simp at hlen
  | cons r rs' =>
      have hfa := listInterlaces_forall₂_le_tail h
      have hmono := filter_lt_length_le_of_forall₂_le (x := x) hfa
      by_cases hr : x < r <;> simp [hr] <;> lia

/-- Upper-threshold count of `rs` exceeds that of `ss` by at most one. -/
lemma listInterlaces_filter_lt_le_succ {x : ℝ} {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length) :
    (rs.filter (fun a => x < a)).length ≤
      (ss.filter (fun a => x < a)).length + 1 := by
  have hfa := listInterlaces_dropLast_forall₂_le h hlen
  have hmono := filter_lt_length_le_of_forall₂_le (x := x) hfa
  have hne : rs ≠ [] := fun hnil => by
    rw [hnil] at hlen
    simp at hlen
  have hsplit : (rs.filter (fun a => x < a)).length ≤
      (rs.dropLast.filter (fun a => x < a)).length + 1 := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.filter_append, List.length_append]
    have hlast : ([rs.getLast hne].filter (fun a => x < a)).length ≤ 1 := by
      simp [List.filter_cons]
      split <;> simp
    lia
  lia

/-- With equal parity, the upper-threshold counts of `ss` and `rs` coincide. -/
lemma listInterlaces_filter_lt_eq_of_parity {x : ℝ} {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length)
    (hpar :
      (ss.filter (fun a => x < a)).length % 2 =
        (rs.filter (fun a => x < a)).length % 2) :
    (ss.filter (fun a => x < a)).length =
      (rs.filter (fun a => x < a)).length := by
  have h1 := listInterlaces_filter_lt_le (x := x) h hlen
  have h2 := listInterlaces_filter_lt_le_succ (x := x) h hlen
  lia

/-- If an integer difference of two natural numbers is not odd, then the two
natural numbers have the same parity. -/
lemma nat_mod_two_eq_of_not_odd_int_sub {a b : ℕ}
    (h : ¬ Odd ((a : ℤ) - (b : ℤ))) :
    a % 2 = b % 2 := by
  have he : Even ((a : ℤ) - (b : ℤ)) := Int.not_odd_iff_even.mp h
  rw [Int.even_sub, Int.even_coe_nat, Int.even_coe_nat] at he
  by_cases ha : Even a
  · have hb : Even b := he.mp ha
    rw [Nat.even_iff] at ha hb
    rw [ha, hb]
  · have hb : ¬ Even b := fun hb => ha (he.mpr hb)
    rw [Nat.not_even_iff] at ha hb
    rw [ha, hb]

/-- Pure combinatorial core of issue #42, natural-number form: with a
differ-by-one interlacing and equal upper-count parity, the lower-threshold
count of `rs` is one more than that of `ss`. -/
lemma listInterlaces_filter_le_length_eq_succ {x : ℝ} {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length)
    (hpar :
      (ss.filter (fun a => x < a)).length % 2 =
        (rs.filter (fun a => x < a)).length % 2) :
    (rs.filter (fun a => a ≤ x)).length =
      (ss.filter (fun a => a ≤ x)).length + 1 := by
  have heq := listInterlaces_filter_lt_eq_of_parity (x := x) h hlen hpar
  have hcs := filter_le_add_filter_lt_length (x := x) ss
  have hcr := filter_le_add_filter_lt_length (x := x) rs
  lia

/-- Pure combinatorial core of issue #42, integer form: the lower-count
difference of `rs` minus `ss` is exactly one. -/
lemma listInterlaces_filter_le_sub_eq_one {x : ℝ} {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length)
    (hpar :
      (ss.filter (fun a => x < a)).length % 2 =
        (rs.filter (fun a => x < a)).length % 2) :
    ((rs.filter (fun a => a ≤ x)).length : ℤ) -
        (ss.filter (fun a => a ≤ x)).length = 1 := by
  have hnat := listInterlaces_filter_le_length_eq_succ (x := x) h hlen hpar
  rw [hnat]
  push_cast
  ring

/-- Pure bridge form for issue #42: in a differ-by-one interlacing, if the
strict-upper count difference is not odd, then the lower-count difference is
exactly one.  This matches the output of the succ-degree endpoint-sign parity
lemma. -/
lemma listInterlaces_filter_le_sub_eq_one_of_not_odd_filter_lt_sub
    {x : ℝ} {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length)
    (hnot :
      ¬ Odd (((ss.filter (fun a => x < a)).length : ℤ) -
        (rs.filter (fun a => x < a)).length)) :
    ((rs.filter (fun a => a ≤ x)).length : ℤ) -
        (ss.filter (fun a => a ≤ x)).length = 1 :=
  listInterlaces_filter_le_sub_eq_one h hlen
    (nat_mod_two_eq_of_not_odd_int_sub hnot)

/-! ## Polynomial interlacing -/

/-- `f ≪ g` (**f is interlaced by g**): both real-rooted, `g` has the rightmost root,
    and either:
    - **differ-by-1**: `deg f + 1 = deg g`, roots satisfy `ListInterlaces`
    - **same-degree**: `deg f = deg g`, roots satisfy `ListAlternates`

    Notation: we write `Prec f g` for `f ≪ g`. -/
def Prec (f g : ℝ[X]) : Prop := (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits) ∧
  ∃ (ss rs : List ℝ),
    ss.Pairwise (· ≤ ·) ∧ rs.Pairwise (· ≤ ·) ∧
    (↑ss : Multiset ℝ) = f.roots ∧ (↑rs : Multiset ℝ) = g.roots ∧
    ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs))

lemma natDegree_bounds_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1 := by
  rcases hfg with ⟨hf, hg, ss, rs, _, _, hss_eq, hrs_eq, _⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  lia

/-- The proper-position relation respects degree: `Prec f g` forces
`f.natDegree ≤ g.natDegree`. -/
theorem Prec.natDegree_le {f g : ℝ[X]} (h : Prec f g) :
    f.natDegree ≤ g.natDegree :=
  (natDegree_bounds_of_prec h).1

/-- The right endpoint in `Prec f g` has degree at most one more than the left
endpoint. -/
theorem Prec.natDegree_le_succ {f g : ℝ[X]} (h : Prec f g) :
    g.natDegree ≤ f.natDegree + 1 :=
  (natDegree_bounds_of_prec h).2

/-- A polynomial cannot be in `Prec` with a right endpoint of strictly lower
degree. -/
theorem not_prec_of_right_natDegree_lt_left {f g : ℝ[X]}
    (hdeg : g.natDegree < f.natDegree) :
    ¬ Prec f g := by
  intro hprec
  exact (not_le_of_gt hdeg) hprec.natDegree_le

/-- A polynomial cannot be in `Prec` with a right endpoint whose degree is more
than one larger. -/
theorem not_prec_of_left_natDegree_succ_lt_right {f g : ℝ[X]}
    (hdeg : f.natDegree + 1 < g.natDegree) :
    ¬ Prec f g := by
  intro hprec
  exact (not_le_of_gt hdeg) hprec.natDegree_le_succ

lemma prec_forward_of_orientation_of_succDegree
    {f g : ℝ[X]}
    (hsucc : g.natDegree = f.natDegree + 1)
    (hprec_or : Prec f g ∨ Prec g f) :
    Prec f g := by
  rcases hprec_or with hprec | hprec
  · exact hprec
  · exact (not_prec_of_right_natDegree_lt_left (by lia) hprec).elim

/-- Every root of the left-hand polynomial is bounded by any common upper bound
for the roots of the right-hand polynomial in a `Prec` witness. -/
theorem roots_le_of_prec_right {f g : ℝ[X]} {c : ℝ}
    (h : Prec f g)
    (hg_le : ∀ r ∈ g.roots, r ≤ c) :
    ∀ r ∈ f.roots, r ≤ c := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hrs_le : ∀ r ∈ rs, r ≤ c :=
    fun r hr => hg_le r (by simpa [hrs_eq] using Multiset.mem_coe.mpr hr)
  intro r hr
  have hr' : r ∈ ss := by
    have : r ∈ (↑ss : Multiset ℝ) := by lia
    exact Multiset.mem_coe.mp this
  rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
  · exact listInterlaces_left_le_of_right_le hint hrs_le r hr'
  · exact listAlternates_left_le_of_right_le halt hrs_le r hr'

/-- In the same-degree case, `Prec f g` orders the sums of the roots. -/
theorem roots_sum_le_of_prec_sameDegree {f g : ℝ[X]}
    (h : Prec f g) (hdeg : f.natDegree = g.natDegree) :
    f.roots.sum ≤ g.roots.sum := by
  rcases h with ⟨hf, hg, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hsum_ss : ss.sum = f.roots.sum := by
    rw [← Multiset.sum_coe, hss_eq]
  have hsum_rs : rs.sum = g.roots.sum := by
    rw [← Multiset.sum_coe, hrs_eq]
  rcases hshape with ⟨hlen, _⟩ | ⟨_, halt⟩
  · exfalso
    lia
  · have hle : ss.sum ≤ rs.sum := listAlternates_sum_le halt
    linarith

/-- For monic polynomials in same-degree proper position, the next
coefficients are ordered opposite to the root sums. -/
theorem nextCoeff_le_of_prec_sameDegree_monic {f g : ℝ[X]}
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (h : Prec f g) (hdeg : f.natDegree = g.natDegree) :
    g.nextCoeff ≤ f.nextCoeff := by
  have hsum : f.roots.sum ≤ g.roots.sum :=
    roots_sum_le_of_prec_sameDegree h hdeg
  have hf_next : f.nextCoeff = -f.roots.sum :=
    h.1.2.nextCoeff_eq_neg_sum_roots_of_monic hf_monic
  have hg_next : g.nextCoeff = -g.roots.sum :=
    h.2.1.2.nextCoeff_eq_neg_sum_roots_of_monic hg_monic
  linarith

/-- In the same-degree case, a reverse `Prec g f` can be flipped back to
`Prec f g` once the root sums have the forward order. -/
theorem prec_of_reverse_prec_of_roots_sum_le {f g : ℝ[X]}
    (hgf : Prec g f) (hdeg : f.natDegree = g.natDegree)
    (hsum : f.roots.sum ≤ g.roots.sum) :
    Prec f g := by
  rcases hgf with ⟨hg, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hsum_ss : ss.sum = g.roots.sum := by
    rw [← Multiset.sum_coe, hss_eq]
  have hsum_rs : rs.sum = f.roots.sum := by
    rw [← Multiset.sum_coe, hrs_eq]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
  · exfalso
    lia
  · refine ⟨hf, hg, rs, ss, hrs, hss, hrs_eq, hss_eq, Or.inr ⟨?_, ?_⟩⟩
    · lia
    · apply listAlternates_symm_of_sum_le halt
      linarith

/-- Relaxed interlacing convention used in some recursive arguments:
`Prec0 f g` holds if either side is zero, or if `Prec f g` holds in the
strict nonzero sense. -/
def Prec0 (f g : ℝ[X]) : Prop :=
  f = 0 ∨ g = 0 ∨ Prec f g

/-- Backward-compatible alias: differ-by-1 interlacing. -/
def Interlaces (g f : ℝ[X]) : Prop := (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits) ∧
  g.natDegree + 1 = f.natDegree ∧
  ∃ (rs ss : List ℝ),
    rs.Pairwise (· ≤ ·) ∧ ss.Pairwise (· ≤ ·) ∧
    (↑rs : Multiset ℝ) = f.roots ∧
    (↑ss : Multiset ℝ) = g.roots ∧
    ListInterlaces ss rs

namespace Interlaces

/-- Differ-by-one interlacing for a quadratic whose roots lie between the
ordered roots of a cubic. -/
theorem of_quadratic_cubic_root_lists
    {g f : ℝ[X]} {a b c u v : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2)
    (hf_roots : f.roots = (↑[a, b, c] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v) (hvc : v ≤ c) :
    Interlaces g f := by
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, ?_, [a, b, c], [u, v],
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgdeg, hfdeg]
  · simp [hab, hbc, hab.trans hbc]
  · simp [huv]
  · rw [hf_roots]
  · rw [hg_roots]
  · simp [ListInterlaces, hau, hub, hbv, hvc]

/-- Differ-by-one interlacing for a cubic whose roots lie between the ordered
roots of a quartic. -/
theorem of_cubic_quartic_root_lists
    {g f : ℝ[X]} {a b c d u v w : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 4) (hgdeg : g.natDegree = 3)
    (hf_roots : f.roots = (↑[a, b, c, d] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d) :
    Interlaces g f := by
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, ?_, [a, b, c, d], [u, v, w],
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgdeg, hfdeg]
  · simp [hab, hbc, hcd, hab.trans hbc, hbc.trans hcd,
      hab.trans (hbc.trans hcd)]
  · simp [huv, hvw, huv.trans hvw]
  · rw [hf_roots]
  · rw [hg_roots]
  · simp [ListInterlaces, hau, hub, hbv, hvc, hcw, hwd]

end Interlaces

/-- A **Sturm sequence** is a list of polynomials where each consecutive
    pair interlaces (differ-by-1). -/
def IsSturmSeq : List ℝ[X] → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Interlaces q p ∧ IsSturmSeq (q :: rest)

/-- A **generalized Sturm sequence** is a list of polynomials where each
    consecutive pair satisfies the weak interlacing relation `≪`, i.e. `Prec`.

    This allows either differ-by-1 interlacing or same-degree alternation at
    each step. -/
def IsGeneralizedSturmSeq : List ℝ[X] → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Prec q p ∧ IsGeneralizedSturmSeq (q :: rest)

/-! ## Interlaces → Prec -/

lemma Interlaces.toPrec {g f : ℝ[X]} (h : Interlaces g f) : Prec g f := by
  obtain ⟨hf, hg, _, rs, ss, hrs, hss, hrs_eq, hss_eq, hint⟩ := h
  refine ⟨hg, hf, _, _, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨?_, hint⟩⟩
  have : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, (card_roots_of_splits hg.2)]
  have : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, (card_roots_of_splits hf.2)]
  lia

lemma Prec.toInterlaces {g f : ℝ[X]} (h : Prec g f)
    (hdeg : g.natDegree + 1 = f.natDegree) : Interlaces g f := by
  rcases h with ⟨hg, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, _⟩
  refine ⟨hf, hg, hdeg, _, _, hrs, hss, hrs_eq, hss_eq, ?_⟩
  have : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, (card_roots_of_splits hg.2)]
  have : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, (card_roots_of_splits hf.2)]
  lia

/-- Multiplying the left polynomial in a proper-position relation by a nonzero
real scalar preserves proper position. -/
lemma Prec.C_mul_left {f g : ℝ[X]} (h : Prec f g) {a : ℝ} (ha : a ≠ 0) :
    Prec (C a * f) g := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  refine ⟨?_, hg, ss, rs, hss, hrs, ?_, hrs_eq, hshape⟩
  · exact ⟨mul_ne_zero (C_ne_zero.mpr ha) hf.1, hf.2.C_mul a⟩
  · rw [roots_C_mul _ ha]
    exact hss_eq

/-- Multiplying the right polynomial in a proper-position relation by a nonzero
real scalar preserves proper position. -/
lemma Prec.C_mul_right {f g : ℝ[X]} (h : Prec f g) {a : ℝ} (ha : a ≠ 0) :
    Prec f (C a * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  refine ⟨hf, ?_, ss, rs, hss, hrs, hss_eq, ?_, hshape⟩
  · exact ⟨mul_ne_zero (C_ne_zero.mpr ha) hg.1, hg.2.C_mul a⟩
  · rw [roots_C_mul _ ha]
    exact hrs_eq

lemma IsSturmSeq.toGeneralizedSturmSeq {ps : List ℝ[X]} (h : IsSturmSeq ps) :
    IsGeneralizedSturmSeq ps := by
  induction ps with grind [IsGeneralizedSturmSeq, eq_def, Interlaces.toPrec]

-- ============================================================
-- Basic lemmas
-- ============================================================

lemma Prec.toPrec0 {f g : ℝ[X]} (h : Prec f g) : Prec0 f g :=
  Or.inr (Or.inr h)

lemma Prec0.toPrec_of_ne {f g : ℝ[X]} (h : Prec0 f g)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    Prec f g := by
  grind [Prec0]

lemma prec0_zero_left (f : ℝ[X]) : Prec0 0 f :=
  Or.inl rfl

lemma prec0_zero_right (f : ℝ[X]) : Prec0 f 0 :=
  Or.inr (Or.inl rfl)

lemma prec0_zero_zero : Prec0 (0 : ℝ[X]) 0 :=
  prec0_zero_left 0

/-- The product of two real-rooted polynomials is real-rooted. -/
lemma isRealRooted_mul {p q : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hq_ne : q ≠ 0) (hq_splits : q.Splits) : (p * q ≠ 0 ∧ (p * q).Splits) :=
  ⟨mul_ne_zero hp_ne hq_ne, hp_splits.mul hq_splits⟩

/-- Non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

/-- Positive leading coefficient. -/
def HasPosLeadingCoeff (p : ℝ[X]) : Prop := 0 < p.leadingCoeff

@[simp] lemma not_hasPosLeadingCoeff_zero : ¬ HasPosLeadingCoeff (0 : ℝ[X]) := by
  simp [HasPosLeadingCoeff]

lemma HasPosLeadingCoeff.ne_zero {p : ℝ[X]} (hp : HasPosLeadingCoeff p) : p ≠ 0 := by
  rintro rfl; simp at hp

lemma HasNonnegCoeffs.pos_leadingCoeff {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) : HasPosLeadingCoeff p := by
  unfold HasPosLeadingCoeff
  exact lt_of_le_of_ne (hp p.natDegree) (Ne.symm (leadingCoeff_ne_zero.mpr hp0))

/-- A nonzero polynomial with nonnegative coefficients is strictly positive at
every strictly positive real argument. -/
theorem eval_pos_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) {t : ℝ} (ht : 0 < t) : 0 < p.eval t := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_pos
  · intro n hn
    have hcoeff : 0 < p.coeff n :=
      lt_of_le_of_ne (hp n) (Ne.symm (Polynomial.mem_support_iff.mp hn))
    positivity
  · exact Polynomial.support_nonempty.mpr hp0

/-- A real polynomial with nonnegative coefficients has no positive real roots. -/
theorem roots_nonpos_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    ∀ r ∈ p.roots, r ≤ 0 := fun r hr => by
  by_contra hr_nonpos
  have hp0 : p ≠ 0 := fun hp0 => by
    simp [hp0] at hr
  have hr_pos : 0 < r := lt_of_not_ge hr_nonpos
  have hroot : p.IsRoot r := (Polynomial.mem_roots hp0).mp hr
  have heval_pos : 0 < p.eval r := eval_pos_of_hasNonnegCoeffs hp hp0 hr_pos
  rw [Polynomial.IsRoot.def] at hroot
  linarith

lemma hasPosLeadingCoeff_of_monic {p : ℝ[X]} (hp : p.Monic) :
    HasPosLeadingCoeff p := by
  simp [HasPosLeadingCoeff, hp.leadingCoeff]

lemma hasPosLeadingCoeff_one : HasPosLeadingCoeff (1 : ℝ[X]) :=
  hasPosLeadingCoeff_of_monic monic_one

lemma hasPosLeadingCoeff_C_mul {a : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (C a * p) := by
  simpa [HasPosLeadingCoeff, leadingCoeff_mul] using mul_pos ha hp

lemma HasPosLeadingCoeff.mul {p q : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p * q) := by
  simpa [HasPosLeadingCoeff, leadingCoeff_mul] using mul_pos hp hq

lemma hasPosLeadingCoeff_neg {p : ℝ[X]} (hp : p.leadingCoeff < 0) :
    HasPosLeadingCoeff (-p) := by
  simpa [HasPosLeadingCoeff] using hp

lemma HasPosLeadingCoeff.X_mul {p : ℝ[X]} (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (X * p) := by
  simpa [HasPosLeadingCoeff, leadingCoeff_mul, leadingCoeff_X] using hp

/-! ## Elementary interval inequalities -/

lemma quadratic_nonneg_on_unit_interval_of_coeffs_nonneg
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ A + B * β + C * β ^ 2 := by
  positivity

lemma quadratic_nonneg_on_unit_interval_of_endpoint_nonneg_of_c_nonneg
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hEnd : 0 ≤ A + B + C)
    (hC : 0 ≤ C) (hBneg : B < 0 → C = 0) :
    0 ≤ A + B * β + C * β ^ 2 := by
  by_cases hB : 0 ≤ B
  · exact quadratic_nonneg_on_unit_interval_of_coeffs_nonneg hβ0 hA hB hC
  · have hEnd' : 0 ≤ A + B := by simp_all
    have : 0 ≤ (1 - β) * A + β * (A + B) :=
      add_nonneg (mul_nonneg (sub_nonneg_of_le hβ1) hA) (mul_nonneg hβ0 hEnd')
    have : A + B * β + C * β ^ 2 = (1 - β) * A + β * (A + B) := by
      rw [hBneg (lt_of_not_ge hB)]
      ring_nf
    lia

lemma quadratic_nonneg_on_unit_interval_of_endpoint_nonneg_of_vertex_or_discriminant
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hEnd : 0 ≤ A + B + C)
    (hC : 0 ≤ C)
    (hBneg : B < 0 → 2 * C ≤ -B ∨ B ^ 2 ≤ 4 * C * A) :
    0 ≤ A + B * β + C * β ^ 2 := by
  by_cases hB : 0 ≤ B
  · exact quadratic_nonneg_on_unit_interval_of_coeffs_nonneg hβ0 hA hB hC
  · cases hBneg (lt_of_not_ge hB)
    · have hβm1 : β - 1 ≤ 0 := tsub_nonpos.mpr hβ1
      have hβp1 : β + 1 ≤ 2 := by linarith
      have : C * (β + 1) ≤ C * 2 := mul_le_mul_of_nonneg_left hβp1 hC
      have hfactor : B + C * (β + 1) ≤ 0 := by linarith
      have : 0 ≤ (β - 1) * (B + C * (β + 1)) := mul_nonneg_of_nonpos_of_nonpos hβm1 hfactor
      grind
    · have : 0 < C := lt_of_le_of_ne hC (by intro rfl; simp_all)
      have : 0 ≤ (2 * C * β + B) ^ 2 := sq_nonneg _
      have : 0 ≤ 4 * C * (A + B * β + C * β ^ 2) := by grind
      simp_all

lemma coeff_X_sub_C_mul (r : ℝ) (q : ℝ[X]) (n : ℕ) :
    ((X - C r) * q).coeff n =
      (if n = 0 then 0 else q.coeff (n - 1)) - r * q.coeff n := by
  simp only [sub_mul, coeff_sub, coeff_C_mul]
  cases n with
  | zero => simp
  | succ m => simp [coeff_X_mul]

/-- A nonconstant real-rooted polynomial has a rightmost root. -/
lemma exists_rightmost_root_of_isRealRooted
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hdeg : 1 ≤ p.natDegree) :
    ∃ r, p.IsRoot r ∧ ∀ s ∈ p.roots, s ≤ r := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = p.natDegree := by simp [rs, card_roots_of_splits hp_splits]
  have hrs_ne : rs ≠ [] := by grind
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      simp
    simp_all
  · intro s hs
    have hs_mem : s ∈ rs := by
      apply Multiset.mem_coe.mp
      lia
    exact hrs_sorted.rel_getLast hs_mem

/-- For a nonempty right-hand list, `ListInterlaces` forces the expected length
relation. -/
lemma listInterlaces_cons_length_eq :
    ∀ {ss rest : List ℝ} {r : ℝ},
      ListInterlaces ss (r :: rest) → ss.length = rest.length
  | [], [], _, _ => by lia
  | _ :: _, [], _, h => by simp [ListInterlaces] at h
  | s :: ss, r₂ :: rest, r₁, h => by
      obtain ⟨_, _, htail⟩ := h
      simpa [List.length_cons] using
          listInterlaces_cons_length_eq htail

/-- Every polynomial has an upper bound for its roots. -/
lemma exists_root_upper_bound (p : ℝ[X]) :
    ∃ c, ∀ r ∈ p.roots, r ≤ c := by
  let rs := p.roots.sort (· ≤ ·)
  by_cases hrs_nil : rs = []
  · refine ⟨0, ?_⟩
    intro r hr
    have hroots_nil : p.roots = 0 := by
      simpa [rs, hrs_nil] using (Multiset.sort_eq (s := p.roots) (r := (· ≤ ·))).symm
    simp_all
  · refine ⟨rs.getLast hrs_nil, ?_⟩
    have hrs_sorted : rs.Pairwise (· ≤ ·) := by simp [rs]
    intro r hr
    have hr_mem : r ∈ rs := by
      apply Multiset.mem_coe.mp
      simpa [rs] using hr
    exact hrs_sorted.rel_getLast hr_mem

end RealRooted
