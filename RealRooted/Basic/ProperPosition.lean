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
import RealRooted.Basic.PolynomialFacts
import RealRooted.Basic.RootLists

open Polynomial

noncomputable section

namespace RealRooted

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

private lemma listInterlaces_right_tail_ge :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) → ∀ x ∈ rs, r ≤ x
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp [ListInterlaces] at h
  | _ :: _, [], _, _ => by simp
  | s :: ss, r₂ :: rs, r, h => by
      rcases h with ⟨hr_s, hs_r₂, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans hr_s hs_r₂
      · exact le_trans (le_trans hr_s hs_r₂)
          (listInterlaces_right_tail_ge htail x hx)

private lemma listInterlaces_left_ge_head :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) → ∀ x ∈ ss, r ≤ x
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => by simp [ListInterlaces] at h
  | s :: ss, r₂ :: rs, r, h => by
      rcases h with ⟨hr_s, hs_r₂, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr_s
      · exact le_trans (le_trans hr_s hs_r₂)
          (listInterlaces_left_ge_head htail x hx)

private lemma listInterlaces_count_left_le_right_of_head (u : ℝ) :
    ∀ {ss rs : List ℝ}, ListInterlaces ss (u :: rs) →
      ss.count u ≤ (u :: rs).count u
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [ListInterlaces] at h
  | s :: ss, r₂ :: rs, h => by
      rcases h with ⟨hus, hs_r₂, htail⟩
      by_cases hs : s = u
      · subst s
        by_cases hr₂ : r₂ = u
        · subst r₂
          have ih := listInterlaces_count_left_le_right_of_head u htail
          simp at ih ⊢
          lia
        · have hu_lt_r₂ : u < r₂ := lt_of_le_of_ne hs_r₂ (Ne.symm hr₂)
          have htail_no_mem : u ∉ r₂ :: rs := by
            intro hu_mem
            rcases List.mem_cons.mp hu_mem with hu_eq | hu_rs
            · exact hr₂ hu_eq.symm
            · have hge := listInterlaces_right_tail_ge htail u hu_rs
              linarith
          have hss_no_mem : u ∉ ss := by
            intro hu_mem
            have hge := listInterlaces_left_ge_head htail u hu_mem
            linarith
          simp [List.count_eq_zero.mpr htail_no_mem,
            List.count_eq_zero.mpr hss_no_mem]
      · have hu_lt_s : u < s := lt_of_le_of_ne hus (Ne.symm hs)
        have hu_lt_r₂ : u < r₂ := lt_of_lt_of_le hu_lt_s hs_r₂
        have htail_no_mem : u ∉ r₂ :: rs := by
          intro hu_mem
          rcases List.mem_cons.mp hu_mem with hu_eq | hu_rs
          · exact ne_of_gt hu_lt_r₂ hu_eq.symm
          · have hge := listInterlaces_right_tail_ge htail u hu_rs
            linarith
        have hss_no_mem : u ∉ ss := by
          intro hu_mem
          have hge := listInterlaces_left_ge_head htail u hu_mem
          linarith
        simp [hs, List.count_eq_zero.mpr htail_no_mem,
          List.count_eq_zero.mpr hss_no_mem]

private lemma listInterlaces_count_right_le_left_add_one (u : ℝ) :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs → rs.count u ≤ ss.count u + 1
  | [], [], _ => by simp
  | [], [r], _ => by
      by_cases hr : r = u <;> simp [hr]
  | [], _ :: _ :: _, h => by simp [ListInterlaces] at h
  | _ :: _, [], h => by simp [ListInterlaces] at h
  | _ :: _, [_], h => by simp [ListInterlaces] at h
  | s :: ss, r₁ :: r₂ :: rs, h => by
      rcases h with ⟨hr₁s, hs_r₂, htail⟩
      by_cases hr₁ : r₁ = u
      · by_cases hs : s = u
        · subst r₁
          subst s
          have ih := listInterlaces_count_right_le_left_add_one u htail
          simp [List.count_cons] at ih ⊢
          lia
        · subst r₁
          have hu_lt_s : u < s := lt_of_le_of_ne hr₁s (by simpa [eq_comm] using hs)
          have hu_lt_r₂ : u < r₂ := lt_of_lt_of_le hu_lt_s hs_r₂
          have htail_no_mem : u ∉ r₂ :: rs := by
            intro hu_mem
            rcases List.mem_cons.mp hu_mem with hu_eq | hu_rs
            · exact ne_of_gt hu_lt_r₂ hu_eq.symm
            · have hge := listInterlaces_right_tail_ge htail u hu_rs
              linarith
          have htail_count : (r₂ :: rs).count u = 0 :=
            List.count_eq_zero.mpr htail_no_mem
          have hss_no_mem : u ∉ ss := by
            intro hu_mem
            have hge := listInterlaces_left_ge_head htail u hu_mem
            linarith
          have hss_count : ss.count u = 0 := List.count_eq_zero.mpr hss_no_mem
          simp [htail_count, hss_count, hs]
      · have ih := listInterlaces_count_right_le_left_add_one u htail
        by_cases hs : s = u
        · simp [hr₁, hs] at ih ⊢
          lia
        · simpa [hr₁, hs] using ih

private lemma listInterlaces_count_left_le_right_add_one (u : ℝ) :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs → ss.count u ≤ rs.count u + 1
  | [], [], _ => by simp
  | [], [_], _ => by simp
  | [], _ :: _ :: _, h => by simp [ListInterlaces] at h
  | _ :: _, [], h => by simp [ListInterlaces] at h
  | _ :: _, [_], h => by simp [ListInterlaces] at h
  | s :: ss, r₁ :: r₂ :: rs, h => by
      rcases h with ⟨hr₁s, hs_r₂, htail⟩
      have ih := listInterlaces_count_left_le_right_add_one u htail
      by_cases hs : s = u
      · by_cases hr₁ : r₁ = u
        · simp [hs, hr₁] at ih ⊢
          lia
        · by_cases hr₂ : r₂ = u
          · subst r₂
            have hstrong := listInterlaces_count_left_le_right_of_head u htail
            simp [hs, hr₁] at hstrong ⊢
            lia
          · have hu_lt_r₂ : u < r₂ := by
              rw [hs] at hs_r₂
              exact lt_of_le_of_ne hs_r₂ (Ne.symm hr₂)
            have htail_no_mem : u ∉ r₂ :: rs := by
              intro hu_mem
              rcases List.mem_cons.mp hu_mem with hu_eq | hu_rs
              · exact hr₂ hu_eq.symm
              · have hge := listInterlaces_right_tail_ge htail u hu_rs
                linarith
            have hss_no_mem : u ∉ ss := by
              intro hu_mem
              have hge := listInterlaces_left_ge_head htail u hu_mem
              linarith
            have htail_count : (r₂ :: rs).count u = 0 :=
              List.count_eq_zero.mpr htail_no_mem
            have hss_count : ss.count u = 0 := List.count_eq_zero.mpr hss_no_mem
            simp [hs, hr₁, htail_count, hss_count]
      · by_cases hr₁ : r₁ = u <;> simp [hs, hr₁] at ih ⊢ <;> lia

private lemma listAlternates_count_bounds (u : ℝ) :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      ss.count u ≤ rs.count u + 1 ∧ rs.count u ≤ ss.count u + 1
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [ListAlternates] at h
  | _ :: _, [], h => by simp [ListAlternates] at h
  | s :: ss, r :: rs, h => by
      rcases h with ⟨hsr, htail⟩
      constructor
      · have ih := listInterlaces_count_left_le_right_add_one u htail
        by_cases hs : s = u
        · by_cases hr : r = u
          · subst r
            have hstrong := listInterlaces_count_left_le_right_of_head u htail
            simp [hs] at hstrong ⊢
            lia
          · have hu_lt_r : u < r := by
              rw [hs] at hsr
              exact lt_of_le_of_ne hsr (Ne.symm hr)
            have hss_no_mem : u ∉ ss := by
              intro hu_mem
              have hge := listInterlaces_left_ge_head htail u hu_mem
              linarith
            have hss_count : ss.count u = 0 := List.count_eq_zero.mpr hss_no_mem
            simp [hs, hr, hss_count]
        · simpa [hs] using ih
      · have ih := listInterlaces_count_right_le_left_add_one u htail
        by_cases hs : s = u
        · simp [hs] at ih ⊢
          lia
        · simpa [hs] using ih

/-- In proper position, the multiplicities of every real root differ by at
most one. -/
theorem rootMultiplicity_bounds_of_prec {f g : ℝ[X]} (h : Prec f g) (u : ℝ) :
    f.rootMultiplicity u - 1 ≤ g.rootMultiplicity u ∧
      g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u := by
  rcases h with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
  have hcount : ss.count u ≤ rs.count u + 1 ∧ rs.count u ≤ ss.count u + 1 := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
    · exact ⟨listInterlaces_count_left_le_right_add_one u hint,
        listInterlaces_count_right_le_left_add_one u hint⟩
    · exact listAlternates_count_bounds u halt
  have hrs_count : rs.count u = g.rootMultiplicity u := by
    rw [← count_roots g, ← hrs_eq]
    exact (Multiset.coe_count u rs).symm
  have hss_count : ss.count u = f.rootMultiplicity u := by
    rw [← count_roots f, ← hss_eq]
    exact (Multiset.coe_count u ss).symm
  rw [hss_count, hrs_count] at hcount
  lia

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

/-- Proper position forces equal natural degrees or a one-degree increase. -/
theorem Prec.natDegree_eq_or_eq_succ {f g : ℝ[X]} (h : Prec f g) :
    g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by
  have hle := h.natDegree_le
  have hle_succ := h.natDegree_le_succ
  lia

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
  have hsum_ss : ss.sum = f.roots.sum := by rw [← Multiset.sum_coe, hss_eq]
  have hsum_rs : rs.sum = g.roots.sum := by rw [← Multiset.sum_coe, hrs_eq]
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
  have hsum_ss : ss.sum = g.roots.sum := by rw [← Multiset.sum_coe, hss_eq]
  have hsum_rs : rs.sum = f.roots.sum := by rw [← Multiset.sum_coe, hrs_eq]
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

/-- Differ-by-one interlacing for a quartic whose roots lie between the
ordered roots of a quintic. -/
theorem of_quartic_quintic_root_lists
    {g f : ℝ[X]} {a b c d e u v w z : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 5) (hgdeg : g.natDegree = 4)
    (hf_roots : f.roots = (↑[a, b, c, d, e] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w, z] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d)
    (hdz : d ≤ z) (hze : z ≤ e) :
    Interlaces g f := by
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, ?_, [a, b, c, d, e],
    [u, v, w, z], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgdeg, hfdeg]
  · simp [hab, hbc, hcd, hde, hab.trans hbc, hbc.trans hcd, hcd.trans hde,
      hab.trans (hbc.trans hcd), hbc.trans (hcd.trans hde),
      hab.trans (hbc.trans (hcd.trans hde))]
  · simp [huv, hvw, hwz, huv.trans hvw, hvw.trans hwz,
      huv.trans (hvw.trans hwz)]
  · rw [hf_roots]
  · rw [hg_roots]
  · simp [ListInterlaces, hau, hub, hbv, hvc, hcw, hwd, hdz, hze]

/-- Differ-by-one interlacing for a quintic whose roots lie between the ordered
roots of a sextic. -/
theorem of_quintic_sextic_root_lists
    {g f : ℝ[X]} {a b c d e r u v w z y : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 6) (hgdeg : g.natDegree = 5)
    (hf_roots : f.roots = (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w, z, y] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z) (hzy : z ≤ y)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d)
    (hdz : d ≤ z) (hze : z ≤ e) (hey : e ≤ y) (hyr : y ≤ r) :
    Interlaces g f := by
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, ?_,
    [a, b, c, d, e, r], [u, v, w, z, y], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgdeg, hfdeg]
  · simp [hab, hbc, hcd, hde, her, hab.trans hbc, hbc.trans hcd,
      hcd.trans hde, hde.trans her, hab.trans (hbc.trans hcd),
      hbc.trans (hcd.trans hde), hcd.trans (hde.trans her),
      hab.trans (hbc.trans (hcd.trans hde)),
      hbc.trans (hcd.trans (hde.trans her)),
      hab.trans (hbc.trans (hcd.trans (hde.trans her)))]
  · simp [huv, hvw, hwz, hzy, huv.trans hvw, hvw.trans hwz,
      hwz.trans hzy, huv.trans (hvw.trans hwz), hvw.trans (hwz.trans hzy),
      huv.trans (hvw.trans (hwz.trans hzy))]
  · rw [hf_roots]
  · rw [hg_roots]
  · simp [ListInterlaces, hau, hub, hbv, hvc, hcw, hwd, hdz, hze, hey, hyr]

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
end RealRooted
