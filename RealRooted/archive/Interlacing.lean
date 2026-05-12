/-!
# List-level interlacing lemmas

Combinatorial lemmas about `ListInterlaces` and `ListAlternates` operating on lists of reals.
These are extracted from `Wagner.lean` and provide the core list-level reasoning
used by the Wagner lemma proofs and other interlacing results.
-/

import RealRooted.Basic

open Polynomial

noncomputable section

namespace RealRooted

/-! ## List-level lemmas for interlacing -/

/-- Every element of `ss` is `≥` the first element of `rs` in a ListInterlaces. -/
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
    · exact hr
    · exact le_trans (le_trans hr hsr₁) (listInterlaces_all_ge ss' rs' r₁ htail s' hs'')
  | _ :: _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-- All elements of `rs` in a `ListInterlaces ss (r :: rs)` are `≥ r`. -/
lemma listInterlaces_rs_all_ge :
    ∀ (ss rs : List ℝ) (r : ℝ),
    ListInterlaces ss (r :: rs) →
    ∀ r' ∈ rs, r ≤ r'
  | [], [], _, _ => by intro r' hr'; exact nomatch hr'
  | [], _ :: _, _, hint => by simp [ListInterlaces] at hint
  | s :: ss', r₂ :: rs', r, hint => by
    obtain ⟨hr, hsr₂, htail⟩ := hint
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · exact le_trans hr hsr₂
    · exact le_trans (le_trans hr hsr₂) (listInterlaces_rs_all_ge ss' rs' r₂ htail r' hr'')
  | _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-- Every element of the tail of `ss` is `≥ b` in a ListInterlaces ss (a :: b :: rest). -/
lemma listInterlaces_tail_ge :
    ∀ (ss : List ℝ) (a b : ℝ) (rest : List ℝ),
    ListInterlaces ss (a :: b :: rest) →
    ∀ s ∈ ss.tail, b ≤ s
  | [], _, _, _, _ => by simp
  | [_], _, _, _, _ => by simp
  | _ :: ss', a, b, rest, hint => by
    obtain ⟨_, _, htail⟩ := hint
    exact fun s hs => listInterlaces_all_ge ss' rest b htail s hs

/-- A list satisfying `ListInterlaces ss rs` is sorted (pairwise ≤). -/
lemma pairwise_le_of_listInterlaces :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ss.Pairwise (· ≤ ·)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | s₁ :: s₂ :: ss', r₁ :: r₂ :: rs', h => by
      obtain ⟨_, hs₁r₂, htail⟩ := h
      have hs₁s₂ : s₁ ≤ s₂ :=
        le_trans hs₁r₂
          (listInterlaces_all_ge (s₂ :: ss') rs' r₂ htail s₂ (by simp))
      have ih : (s₂ :: ss').Pairwise (· ≤ ·) :=
        pairwise_le_of_listInterlaces (s₂ :: ss') (r₂ :: rs') htail
      rw [List.pairwise_cons]
      constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hs₁s₂
        · exact le_trans hs₁s₂ ((List.pairwise_cons.mp ih).1 x hx')
      · exact ih
  | _ :: _ :: _, [], h => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h => by simp [ListInterlaces] at h

/-! ## List-level lemmas for Wagner (3) -/

lemma listAlternates_append_zero :
    ∀ (ss rs : List ℝ),
    ss.length + 1 = rs.length →
    ListInterlaces ss rs →
    (∀ r ∈ rs, r ≤ 0) →
    ListAlternates rs (ss ++ [0])
  | [], [r₁], _, _, hrs => by
    simp only [ListAlternates, List.nil_append, ListInterlaces]
    exact ⟨hrs r₁ (.head _), trivial⟩
  | s :: _, _ :: [], hlen, _, _ => by simp at hlen
  | s :: ss', r₁ :: r₂ :: rs', hlen, hint, hrs => by
    obtain ⟨hr₁s, hsr₂, htail⟩ := hint
    simp only [ListAlternates, List.cons_append]
    refine ⟨hr₁s, ?_⟩
    have hrs_tail : ∀ r ∈ r₂ :: rs', r ≤ 0 := fun r hr => hrs r (.tail _ hr)
    have hlen_tail : ss'.length + 1 = (r₂ :: rs').length := by simp at hlen ⊢; omega
    have ih := listAlternates_append_zero ss' (r₂ :: rs') hlen_tail htail hrs_tail
    match ss', rs' with
    | [], [] =>
      simp only [ListInterlaces, List.nil_append]
      exact ⟨hsr₂, hrs r₂ (.tail _ (.head _)), trivial⟩
    | s' :: ss'', _ =>
      simp only [ListInterlaces, List.cons_append]
      simp only [ListAlternates, List.cons_append] at ih
      exact ⟨hsr₂, ih.1, ih.2⟩

lemma listInterlaces_of_listAlternates_append_zero :
    ∀ (ss rs : List ℝ),
    ss.length + 1 = rs.length →
    ListAlternates rs (ss ++ [0]) →
    ListInterlaces ss rs
  | [], [_], _, halt => by
    simp only [ListAlternates, List.nil_append, ListInterlaces] at halt ⊢
  | s :: _, _ :: [], hlen, _ => by simp at hlen
  | s :: ss', r₁ :: r₂ :: rs', hlen, halt => by
    simp only [ListAlternates, List.cons_append] at halt
    obtain ⟨hr₁s, htail_inter⟩ := halt
    match ss', rs' with
    | [], [] =>
      simp only [ListInterlaces, List.nil_append] at htail_inter ⊢
      exact ⟨hr₁s, htail_inter.1, trivial⟩
    | s' :: ss'', rs'' =>
      simp only [ListInterlaces, List.cons_append] at htail_inter
      obtain ⟨hsr₂, hr₂s', htail'⟩ := htail_inter
      refine ⟨hr₁s, hsr₂, ?_⟩
      have halt' : ListAlternates (r₂ :: rs'') ((s' :: ss'') ++ [0]) := by
        simp only [ListAlternates, List.cons_append]; exact ⟨hr₂s', htail'⟩
      have hlen' : (s' :: ss'').length + 1 = (r₂ :: rs'').length := by
        simp only [List.length_cons] at hlen ⊢; omega
      exact listInterlaces_of_listAlternates_append_zero (s' :: ss'') (r₂ :: rs'') hlen' halt'

end RealRooted
