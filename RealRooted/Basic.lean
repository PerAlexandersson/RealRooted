import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Interleave
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic

/-!
# Real-rootedness and interlacing of polynomials

This file contains the foundational definitions for real-rootedness,
interlacing, proper position, and Sturm sequences of univariate real
polynomials.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A nonzero polynomial `p ∈ ℝ[X]` is **real-rooted** if
    the number of real roots (counted with multiplicity) equals its degree. -/
lemma isRealRooted_iff_ne_zero_and_splits (p : ℝ[X]) :
    (p ≠ 0 ∧ p.roots.card = p.natDegree) ↔ p ≠ 0 ∧ p.Splits := by
  grind [splits_iff_card_roots]

/-- Zero-aware real-rootedness.  This is the convention often used for
closure statements, while `p ≠ 0 ∧ p.roots.card = p.natDegree` remains the
strict nonzero predicate
used by root-list and interlacing proofs. -/
def IsRealRootedOrZero (p : ℝ[X]) : Prop :=
  p = 0 ∨ (p ≠ 0 ∧ p.roots.card = p.natDegree)

lemma isRealRootedOrZero_iff_eq_zero_or_splits (p : ℝ[X]) :
    IsRealRootedOrZero p ↔ p = 0 ∨ p.Splits := by
  grind [IsRealRootedOrZero, isRealRooted_iff_ne_zero_and_splits]

namespace IsRealRooted

lemma toOrZero {p : ℝ[X]} (hp : p ≠ 0 ∧ p.roots.card = p.natDegree) :
    IsRealRootedOrZero p :=
  Or.inr hp

end IsRealRooted

lemma isRealRootedOrZero_zero : IsRealRootedOrZero (0 : ℝ[X]) :=
  Or.inl rfl

lemma IsRealRootedOrZero.of_ne_zero {p : ℝ[X]}
    (hp : IsRealRootedOrZero p) (hp0 : p ≠ 0) :
    p ≠ 0 ∧ p.roots.card = p.natDegree :=
  Or.resolve_left hp hp0

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
  | [], [], h => by simp at h
  | [], [_], _ => by simp [ListInterlaces]
  | [], _ :: _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, [_], h => by simp at h
  | s :: ss, r₁ :: r₂ :: rs, h => by
      have htail : ss.length + 1 = (r₂ :: rs).length := by
        simpa using Nat.succ.inj h
      constructor
      · rintro ⟨hr₁s, hsr₂, htail_old⟩
        exact List.Interleaves.cons_symm
          (List.Interleaves.cons_symm
            ((listInterlaces_iff_interleaves_of_length htail).1 htail_old) hsr₂)
          hr₁s
      · intro hnew
        rw [List.interleaves_iff] at hnew
        rcases hnew with hbad | hbad | ⟨l₁, l₂, b, hmid, a, hab, hleft, hright⟩
        · simp at hbad
        · simp at hbad
        · simp only [List.cons.injEq] at hleft hright
          rcases hleft with ⟨rfl, rfl⟩
          rcases hright with ⟨rfl, rfl⟩
          rw [List.interleaves_iff] at hmid
          rcases hmid with hbad | hbad | ⟨l₁, l₂, b, htail_new, a, hsr₂, hleft, hright⟩
          · simp at hbad
          · simp at hbad
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
        simpa using Nat.succ.inj h
      constructor
      · rintro ⟨hsr, htail_old⟩
        exact List.Interleaves.cons_symm
          ((listInterlaces_iff_interleaves_of_length htail).1 htail_old) hsr
      · intro hnew
        rw [List.interleaves_iff] at hnew
        rcases hnew with hbad | hbad | ⟨l₁, l₂, b, htail_new, a, hsr, hleft, hright⟩
        · simp at hbad
        · simp at hbad
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

lemma listInterlaces_left_le_of_right_le {ss rs : List ℝ} {c : ℝ}
    (hint : ListInterlaces ss rs)
    (hrs : ∀ r ∈ rs, r ≤ c) :
    ∀ s ∈ ss, s ≤ c := by
  induction ss generalizing rs with
  | nil =>
      intro s hs
      simp at hs
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
              · exact ih htail (fun r hr => hrs r (by simp [hr])) t ht

lemma listAlternates_left_le_of_right_le {ss rs : List ℝ} {c : ℝ}
    (halt : ListAlternates ss rs)
    (hrs : ∀ r ∈ rs, r ≤ c) :
    ∀ s ∈ ss, s ≤ c := by
  induction ss generalizing rs with
  | nil =>
      intro s hs
      simp at hs
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
              (fun x hx => hrs x (by simp [hx])) t ht

/-! ## Polynomial interlacing -/

/-- `f ≪ g` (**f is interlaced by g**): both real-rooted, `g` has the rightmost root,
    and either:
    - **differ-by-1**: `deg f + 1 = deg g`, roots satisfy `ListInterlaces`
    - **same-degree**: `deg f = deg g`, roots satisfy `ListAlternates`

    Notation: we write `Prec f g` for `f ≪ g`. -/
def Prec (f g : ℝ[X]) : Prop :=
  (f ≠ 0 ∧ f.roots.card = f.natDegree) ∧ (g ≠ 0 ∧ g.roots.card = g.natDegree) ∧
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
    have : r ∈ (↑ss : Multiset ℝ) := by simpa [hss_eq] using hr
    exact Multiset.mem_coe.mp this
  rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
  · exact listInterlaces_left_le_of_right_le hint hrs_le r hr'
  · exact listAlternates_left_le_of_right_le halt hrs_le r hr'

/-- Relaxed interlacing convention used in some recursive arguments:
`Prec0 f g` holds if either side is zero, or if `Prec f g` holds in the
strict nonzero sense. -/
def Prec0 (f g : ℝ[X]) : Prop :=
  f = 0 ∨ g = 0 ∨ Prec f g

/-- Backward-compatible alias: differ-by-1 interlacing. -/
def Interlaces (g f : ℝ[X]) : Prop :=
  (f ≠ 0 ∧ f.roots.card = f.natDegree) ∧ (g ≠ 0 ∧ g.roots.card = g.natDegree) ∧
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
    rw [← Multiset.coe_card, hss_eq, hg.2]
  have : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  lia

lemma Prec.toInterlaces {g f : ℝ[X]} (h : Prec g f)
    (hdeg : g.natDegree + 1 = f.natDegree) : Interlaces g f := by
  rcases h with ⟨hg, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, _⟩
  refine ⟨hf, hg, hdeg, _, _, hrs, hss, hrs_eq, hss_eq, ?_⟩
  have : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hg.2]
  have : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  lia

lemma IsSturmSeq.toGeneralizedSturmSeq {ps : List ℝ[X]} (h : IsSturmSeq ps) :
    IsGeneralizedSturmSeq ps := by
  induction ps with grind [IsGeneralizedSturmSeq, eq_def, Interlaces.toPrec]

-- ============================================================
-- Basic lemmas
-- ============================================================

lemma isRealRooted_of_deg_zero {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree = 0) :
    (p ≠ 0 ∧ p.roots.card = p.natDegree) := ⟨hp, by grind [card_roots']⟩

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
lemma isRealRooted_mul {p q : ℝ[X]} (hp : p ≠ 0 ∧ p.roots.card = p.natDegree) (hq : q ≠ 0 ∧ q.roots.card = q.natDegree) :
    ((p * q) ≠ 0 ∧ (p * q).roots.card = (p * q).natDegree) := ⟨mul_ne_zero hp.1 hq.1,
      by grind [natDegree_mul, roots_mul (mul_ne_zero hp.1 _), Multiset.card_add]⟩

/-- Non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

/-- Positive leading coefficient. -/
def HasPosLeadingCoeff (p : ℝ[X]) : Prop := 0 < p.leadingCoeff

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
  · have hEnd' : 0 ≤ A + B := by grind
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

end RealRooted
