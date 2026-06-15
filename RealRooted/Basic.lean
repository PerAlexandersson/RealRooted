import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
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
    (h : p ≠ 0 ∧ p.roots.card = p.natDegree) : p ≠ 0 ∧ p.Splits :=
  ⟨h.1, splits_of_card_roots h.2⟩

lemma ne_zero_and_card_roots_of_ne_zero_and_splits {p : ℝ[X]}
    (h : p ≠ 0 ∧ p.Splits) : p ≠ 0 ∧ p.roots.card = p.natDegree :=
  ⟨h.1, card_roots_of_splits h.2⟩

lemma eq_zero_or_ne_zero_and_splits_iff_eq_zero_or_ne_zero_and_card_roots (p : ℝ[X]) :
    (p = 0 ∨ (p ≠ 0 ∧ p.Splits)) ↔
      (p = 0 ∨ (p ≠ 0 ∧ p.roots.card = p.natDegree)) := by
  constructor
  · intro h
    rcases h with rfl | h
    · lia
    · exact Or.inr (ne_zero_and_card_roots_of_ne_zero_and_splits h)
  · intro h
    rcases h with rfl | h
    · lia
    · exact Or.inr (ne_zero_and_splits_of_ne_zero_and_card_roots h)

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
      have htail : ss.length + 1 = (r₂ :: rs).length := by
        simp_all
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
      have htail : ss.length + 1 = (r :: rs).length := by
        simp_all
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
      rcases h with ⟨_hr₁s, hsr₂, htail⟩
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

/-- Every root of the left-hand polynomial is bounded by any common upper bound
for the roots of the right-hand polynomial in a `Prec` witness. -/
theorem roots_le_of_prec_right {f g : ℝ[X]} {c : ℝ}
    (h : Prec f g)
    (hg_le : ∀ r ∈ g.roots, r ≤ c) :
    ∀ r ∈ f.roots, r ≤ c := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hrs_le : ∀ r ∈ rs, r ≤ c := by
    intro r hr
    exact hg_le r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
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
  rcases h with ⟨hf, hg, ss, rs, _hss, _hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hsum_ss : ss.sum = f.roots.sum := by
    rw [← Multiset.sum_coe, hss_eq]
  have hsum_rs : rs.sum = g.roots.sum := by
    rw [← Multiset.sum_coe, hrs_eq]
  rcases hshape with ⟨hlen, _hint⟩ | ⟨_hlen, halt⟩
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
  rcases hshape with ⟨hlen, _hint⟩ | ⟨hlen, halt⟩
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
lemma isRealRooted_mul {p q : ℝ[X]} (hp : p ≠ 0 ∧
  p.Splits) (hq : q ≠ 0 ∧
  q.Splits) : (p * q ≠ 0 ∧ (p * q).Splits) := by
  simp_all

/-- Non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

/-- Positive leading coefficient. -/
def HasPosLeadingCoeff (p : ℝ[X]) : Prop := 0 < p.leadingCoeff

@[simp] lemma not_hasPosLeadingCoeff_zero : ¬ HasPosLeadingCoeff (0 : ℝ[X]) := by
  simp [HasPosLeadingCoeff]

lemma HasPosLeadingCoeff.ne_zero {p : ℝ[X]} (hp : HasPosLeadingCoeff p) : p ≠ 0 := by
  rintro rfl; simp at hp

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
    have : A + B * β + C * β ^ 2 = (1 - β) * A + β * (A + B) := by grind
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
      have hβp1 : β + 1 ≤ 2 := by grind
      have : C * (β + 1) ≤ C * 2 := mul_le_mul_of_nonneg_left hβp1 hC
      have hfactor : B + C * (β + 1) ≤ 0 := by grind
      have : 0 ≤ (β - 1) * (B + C * (β + 1)) := mul_nonneg_of_nonpos_of_nonpos hβm1 hfactor
      grind
    · have : 0 < C := lt_of_le_of_ne hC (by intro rfl; simp_all)
      have : 0 ≤ (2 * C * β + B) ^ 2 := sq_nonneg _
      have : 0 ≤ 4 * C * (A + B * β + C * β ^ 2) := by grind
      simp_all

lemma coeff_X_sub_C_mul (r : ℝ) (q : ℝ[X]) (n : ℕ) :
    ((X - C r) * q).coeff n = (if n = 0 then 0 else q.coeff (n - 1)) - r * q.coeff n := by
  simp only [sub_mul, coeff_sub, coeff_C_mul]
  cases n with
  | zero => simp
  | succ m => simp [coeff_X_mul]

end RealRooted
