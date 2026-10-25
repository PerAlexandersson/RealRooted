module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Splits
public import RealRooted.Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Basic.Real.Basic
public import RealRooted.Mathlib.Data.Nat.Cast.Basic
public import RealRooted.Mathlib.Data.Nat.Choose.Cast
public import RealRooted.Mathlib.Data.List.Interleave

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

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

/-- If a list is sorted, then its tail interlaces into it. -/
lemma listInterlaces_tail_of_pairwise :
    ∀ rs : List ℝ, rs.Pairwise (· ≤ ·) → ListInterlaces rs.tail rs
  | [], _ => by simp [ListInterlaces]
  | [_], _ => by simp [ListInterlaces]
  | r₁ :: r₂ :: rs, hrs => by
      have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs (.head _)
      have htail : (r₂ :: rs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hrs).2
      simpa [List.tail, ListInterlaces, hr₁r₂] using
        listInterlaces_tail_of_pairwise (r₂ :: rs) htail

/-- Any sorted list alternates with itself. -/
lemma listAlternates_self_of_pairwise :
    ∀ rs : List ℝ, rs.Pairwise (· ≤ ·) → ListAlternates rs rs
  | [], _ => by simp [ListAlternates]
  | r :: rs, hrs => by
      refine ⟨le_rfl, ?_⟩
      simpa [List.tail] using listInterlaces_tail_of_pairwise (r :: rs) hrs

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
      simp [ListInterlaces, listInterlaces_iff_interleaves_of_length htail]

lemma listAlternates_iff_interleaves_of_length :
    ∀ {ss rs : List ℝ}, ss.length = rs.length →
      (ListAlternates ss rs ↔ List.Interleaves (fun x y : ℝ => x ≤ y) rs ss)
  | [], [], _ => by simp [ListAlternates]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | s :: ss, r :: rs, h => by
      have htail : ss.length + 1 = (r :: rs).length := by simpa using h
      simp [ListAlternates, listInterlaces_iff_interleaves_of_length htail]

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
private lemma listInterlaces_forall₂_le_tail :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) →
      List.Forall₂ (fun s t : ℝ => s ≤ t) ss rs
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp [ListInterlaces] at h
  | _ :: _, [], _, h => by simp [ListInterlaces] at h
  | s :: ss, r₂ :: rs, r₁, h => by
      rcases h with ⟨_, hsr₂, htail⟩
      exact List.Forall₂.cons hsr₂ (listInterlaces_forall₂_le_tail htail)

/-- Every element of `ss` is at least the first element of the right-hand
list in a `ListInterlaces` relation. -/
lemma listInterlaces_all_ge :
    ∀ (ss rs : List ℝ) (r : ℝ),
      ListInterlaces ss (r :: rs) →
      ∀ s ∈ ss, r ≤ s
  | [], _, _, _ => by simp
  | [s], [], r, hint => by simp [ListInterlaces] at hint
  | s :: ss', r₁ :: rs', r, hint => by
      obtain ⟨hr, hsr₁, htail⟩ := hint
      intro s' hs'
      rcases List.mem_cons.mp hs' with rfl | hs''
      · lia
      · exact le_trans (le_trans hr hsr₁)
          (listInterlaces_all_ge ss' rs' r₁ htail s' hs'')
  | _ :: _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-- The left-hand list in a `ListInterlaces` relation is sorted. -/
lemma pairwise_le_of_listInterlaces :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ss.Pairwise (· ≤ ·)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | s₁ :: s₂ :: ss', r₁ :: r₂ :: rs', h => by
      obtain ⟨_, hs₁r₂, htail⟩ := h
      refine List.pairwise_cons.mpr ⟨?_, pairwise_le_of_listInterlaces _ _ htail⟩
      intro s hs
      exact le_trans hs₁r₂
        (listInterlaces_all_ge (s₂ :: ss') rs' r₂ htail s hs)
  | _ :: _ :: _, [], h => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h => by simp [ListInterlaces] at h

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

/-- Read an in-range `getD` index from the corresponding end of a reversed list. -/
lemma getD_reverse_eq (l : List ℝ) (j : ℕ) (hj : j < l.length) :
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
            simpa using ih1 k (by simpa using hi)
      · intro i hi
        match i with
        | 0 => simpa using hsr₂
        | k + 1 =>
            simpa using ih2 k (by simpa using hi)

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
            simpa using ih2 k (by simpa using hi)
      · intro i hi
        match i with
        | 0 => simpa using ih1 0 (by simpa using hi)
        | k + 1 =>
            simpa using ih1 (k + 1) (by simpa using hi)

/-- A pair of coordinate bounds constructs a differ-by-one list interlacing. -/
theorem listInterlaces_of_getD_bounds :
    ∀ (ss rs : List ℝ), ss.length + 1 = rs.length →
      (∀ i, i < ss.length → rs.getD i 0 ≤ ss.getD i 0) →
      (∀ i, i < ss.length → ss.getD i 0 ≤ rs.getD (i + 1) 0) →
      ListInterlaces ss rs
  | [], [], hlen, _, _ => by simp at hlen
  | [], [_], _, _, _ => trivial
  | [], _ :: _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | _ :: _, [_], hlen, _, _ => by simp at hlen
  | _ :: ss', _ :: _ :: rs', hlen, h1, h2 => by
      refine ⟨by simpa using h1 0 (by simp), by simpa using h2 0 (by simp), ?_⟩
      refine listInterlaces_of_getD_bounds ss' _ (by simpa using hlen) ?_ ?_
      · intro i hi
        simpa using h1 (i + 1) (by simpa using hi)
      · intro i hi
        simpa using h2 (i + 1) (by simpa using hi)

/-- A pair of coordinate bounds constructs a same-degree list alternation. -/
theorem listAlternates_of_getD_bounds :
    ∀ (ss rs : List ℝ), ss.length = rs.length →
      (∀ i, i < ss.length → ss.getD i 0 ≤ rs.getD i 0) →
      (∀ i, i + 1 < ss.length → rs.getD i 0 ≤ ss.getD (i + 1) 0) →
      ListAlternates ss rs
  | [], [], _, _, _ => trivial
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | _ :: ss', _ :: _, hlen, h1, h2 => by
      refine ⟨by simpa using h1 0 (by simp), ?_⟩
      refine listInterlaces_of_getD_bounds ss' _ (by simpa using hlen) ?_ ?_
      · intro i hi
        simpa using h2 i (by simpa using hi)
      · intro i hi
        simpa using h1 (i + 1) (by simpa using hi)

/-- Same-degree weak alternation orders the sums of the two root lists. -/
lemma listAlternates_sum_le {ss rs : List ℝ} (h : ListAlternates ss rs) :
    ss.sum ≤ rs.sum :=
  List.Forall₂.sum_le_sum (listAlternates_forall₂_le h)

/-- Coordinatewise comparison of positive real lists reverses after inversion
and summation. Positivity of the lower list forces positivity of the upper
list, so no separate hypothesis on the latter is needed. -/
lemma sum_map_inv_le_sum_map_inv_of_forall₂_le
    {xs ys : List ℝ}
    (hxy : List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys)
    (hxs : ∀ x ∈ xs, 0 < x) :
    (ys.map fun y => y⁻¹).sum ≤ (xs.map fun x => x⁻¹).sum := by
  induction hxy with
  | nil => simp
  | @cons x y l₁ l₂ h _ ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (inv_anti₀ (hxs x (List.mem_cons_self ..)) h)
        (ih (fun a ha => hxs a (List.mem_cons_of_mem _ ha)))

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
          have hrs : r ≤ s := by linarith [List.Forall₂.sum_le_sum htail]
          congr
          · exact le_antisymm hsr hrs
          · exact list_eq_of_forall₂_le_of_sum_ge htail (by linarith)

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
      have hlen' : ss'.length + 1 = (r₂ :: rs').length := by simpa using hlen
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


/-- For a nonempty right-hand list, `ListInterlaces` forces the expected length
relation. -/
lemma listInterlaces_cons_length_eq :
    ∀ {ss rest : List ℝ} {r : ℝ},
      ListInterlaces ss (r :: rest) → ss.length = rest.length
  | [], [], _, _ => by lia
  | _ :: _, [], _, h => by simp [ListInterlaces] at h
  | _ :: _, _ :: _, _, ⟨_, _, htail⟩ => by
      simpa using listInterlaces_cons_length_eq htail
end RealRooted
