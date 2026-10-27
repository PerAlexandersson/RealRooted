module

public import RealRooted.HermiteBiehler.StablePencil
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# Mesh of a real-rooted polynomial

This module formalizes the root-separation convention used by Brändén, Krasikov, and
Shapiro, *Elements of Pólya--Schur theory in finite difference setting*, Proc. AMS 144
(2016), Theorem 2.  See also RealRooted issue #2070.

Rather than taking an infimum in `ℝ≥0∞`, we use the predicate `Polynomial.MeshGE p α`.
It says that `p` splits and consecutive entries of its increasing root list are separated
by at least `α`.  This avoids arithmetic with `∞` and is exactly the form consumed by the
finite-difference theorem.
-/

@[expose] public section

open RealRooted

noncomputable section

namespace Polynomial

/-- `MeshGE p α` says that `p` is real-rooted and consecutive roots, counted with
multiplicity and listed increasingly, differ by at least `α`. -/
def MeshGE (p : ℝ[X]) (α : ℝ) : Prop :=
  p.Splits ∧ 0 ≤ α ∧
    ∀ i, i + 1 < (p.roots.sort (· ≤ ·)).length →
      (p.roots.sort (· ≤ ·)).getD i 0 + α ≤
        (p.roots.sort (· ≤ ·)).getD (i + 1) 0

namespace MeshGE

/-- Decreasing the requested separation preserves `MeshGE`. -/
theorem antitone {p : ℝ[X]} {α β : ℝ} (h : p.MeshGE β) (hα : 0 ≤ α) (hαβ : α ≤ β) :
    p.MeshGE α := by
  refine ⟨h.1, hα, fun i hi => ?_⟩
  linarith [h.2.2 i hi]

/-- Every splitting polynomial has mesh at least zero. -/
theorem zero {p : ℝ[X]} (h : p.Splits) : p.MeshGE 0 := by
  refine ⟨h, le_rfl, fun i hi => ?_⟩
  have hs := Multiset.pairwise_sort p.roots (· ≤ ·)
  have hi0 : i < (p.roots.sort (· ≤ ·)).length := by lia
  have hi1 : i + 1 < (p.roots.sort (· ≤ ·)).length := hi
  rw [add_zero]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi1]
  simp only [Option.getD_some]
  exact List.pairwise_iff_getElem.mp hs i (i + 1) hi0 hi1 (by lia)

/-- A polynomial of degree at most one has mesh at least every nonnegative number.
This realizes the convention that its mesh is `+∞`. -/
theorem of_natDegree_le_one {p : ℝ[X]} (hp : p.Splits) (hdeg : p.natDegree ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) : p.MeshGE α := by
  refine ⟨hp, hα, fun i hi => ?_⟩
  have hlen : (p.roots.sort (· ≤ ·)).length ≤ 1 := by
    rw [Multiset.length_sort]
    exact (card_roots' p).trans hdeg
  lia

/-- A positive mesh bound excludes repeated roots.  This realizes the convention that
a polynomial with a multiple root has mesh zero. -/
theorem roots_nodup {p : ℝ[X]} {α : ℝ} (h : p.MeshGE α) (hα : 0 < α) :
    p.roots.Nodup := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort p.roots (· ≤ ·)
  have hrslt : rs.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi1 : i + 1 < rs.length := by lia
    have hgap := h.2.2 i hi1
    have hadj : rs[i] < rs[i + 1] := by
      have : rs[i] + α ≤ rs[i + 1] := by
        simpa [rs, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi1,
          Option.getD_some] using hgap
      linarith
    have htail : rs[i + 1] ≤ rs[j] :=
      hrs.rel_get_of_le (a := ⟨i + 1, hi1⟩) (b := ⟨j, hj⟩) (by simp; lia)
    exact hadj.trans_le htail
  have hrs_nodup : rs.Nodup := hrslt.imp fun hlt => ne_of_lt hlt
  have hcoe_nodup : (↑rs : Multiset ℝ).Nodup := Multiset.coe_nodup.mpr hrs_nodup
  simpa [rs, Multiset.sort_eq] using hcoe_nodup

/-- For a positive bound, `MeshGE` is equivalent to splitting with simple roots whose
pairwise distances are at least the bound. -/
theorem iff_roots_nodup_pairwise_gap {p : ℝ[X]} {α : ℝ} (hα : 0 < α) :
    p.MeshGE α ↔ p.Splits ∧ p.roots.Nodup ∧
      ∀ r ∈ p.roots, ∀ s ∈ p.roots, r ≠ s → α ≤ |r - s| := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort p.roots (· ≤ ·)
  constructor
  · intro h
    refine ⟨h.1, h.roots_nodup hα, ?_⟩
    have hchain : rs.IsChain (fun a b : ℝ => a + α ≤ b) := by
      rw [List.isChain_iff_getElem]
      intro i hi
      have hgap := h.2.2 i (by simpa [rs] using hi)
      simpa [rs, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by lia : i < rs.length),
        List.getElem?_eq_getElem hi, Option.getD_some] using hgap
    have htrans : Trans (fun a b : ℝ => a + α ≤ b)
        (fun a b : ℝ => a + α ≤ b) (fun a b : ℝ => a + α ≤ b) :=
      ⟨by intro a b c hab hbc; linarith⟩
    have hpair : rs.Pairwise (fun a b : ℝ => a + α ≤ b) :=
      @List.IsChain.pairwise ℝ (fun a b : ℝ => a + α ≤ b) rs htrans hchain
    intro r hr s hs hrs_ne
    have hr' : r ∈ rs := by simpa [rs] using hr
    have hs' : s ∈ rs := by simpa [rs] using hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs'
    have hij_ne : i ≠ j := by
      intro hij
      subst j
      exact hrs_ne rfl
    rcases lt_or_gt_of_ne hij_ne with hij | hji
    · have hgap := List.pairwise_iff_getElem.mp hpair i j hi hj hij
      rw [abs_of_nonpos]
      · linarith
      · linarith
    · have hgap := List.pairwise_iff_getElem.mp hpair j i hj hi hji
      rw [abs_of_nonneg]
      · linarith
      · linarith
  · rintro ⟨hp, hnodup, hgap⟩
    refine ⟨hp, hα.le, ?_⟩
    have hrs_nodup : rs.Nodup := by
      rw [← Multiset.coe_nodup, show (↑rs : Multiset ℝ) = p.roots by simp [rs]]
      exact hnodup
    intro i hi
    have hi0 : i < rs.length := by lia
    have hne : rs[i] ≠ rs[i + 1] := by
      intro heq
      have hij : (⟨i, hi0⟩ : Fin rs.length) = ⟨i + 1, hi⟩ :=
        hrs_nodup.injective_get heq
      have := congrArg Fin.val hij
      simp at this
    have hmem0 : rs[i] ∈ p.roots := by
      have hmem : rs[i] ∈ (↑rs : Multiset ℝ) := by
        simp
      rwa [show (↑rs : Multiset ℝ) = p.roots by simp [rs]] at hmem
    have hmem1 : rs[i + 1] ∈ p.roots := by
      have hmem : rs[i + 1] ∈ (↑rs : Multiset ℝ) := by
        simp
      rwa [show (↑rs : Multiset ℝ) = p.roots by simp [rs]] at hmem
    have hdist := hgap rs[i] hmem0 rs[i + 1] hmem1 hne
    have hle := List.pairwise_iff_getElem.mp hrs i (i + 1) hi0 hi (by lia)
    have habs : |rs[i] - rs[i + 1]| = rs[i + 1] - rs[i] := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    rw [habs] at hdist
    simpa [rs, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi,
      Option.getD_some] using (show rs[i] + α ≤ rs[i + 1] by linarith)

/-- A polynomial with a repeated root cannot have a positive mesh bound. -/
theorem not_of_roots_not_nodup {p : ℝ[X]} (hdup : ¬p.roots.Nodup) {α : ℝ}
    (hα : 0 < α) : ¬p.MeshGE α :=
  fun h => hdup (h.roots_nodup hα)

private theorem sorted_root_list_eq {p : ℝ[X]} {rs : List ℝ}
    (hrs : rs.Pairwise (· ≤ ·)) (hroots : (↑rs : Multiset ℝ) = p.roots) :
    p.roots.sort (· ≤ ·) = rs := by
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hrs
  exact Multiset.coe_eq_coe.mp ((Multiset.sort_eq p.roots (· ≤ ·)).trans hroots.symm)

private theorem roots_shift_eq_map (p : ℝ[X]) (α : ℝ) :
    (p.comp (X - C α)).roots = p.roots.map (· + α) := by
  rw [show X - C α = X + C (-α) by simp [sub_eq_add_neg], roots_comp_X_add_C]
  simp only [sub_neg_eq_add]

private theorem comp_shift_ne_zero_iff (p : ℝ[X]) (α : ℝ) :
    p.comp (X - C α) ≠ 0 ↔ p ≠ 0 := by
  rw [show X - C α = X + C (-α) by simp [sub_eq_add_neg],
    comp_X_add_C_ne_zero_iff]

private theorem splits_comp_shift (p : ℝ[X]) (hp : p.Splits) (α : ℝ) :
    (p.comp (X - C α)).Splits := by
  rw [show X - C α = X + C (-α) by simp [sub_eq_add_neg]]
  exact hp.comp_X_add_C (-α)

/-- The root-oriented BKS mesh criterion: for a positive step, `p` has mesh at
least `α` exactly when `p(x)` interlaces `p(x - α)` in the repository's
zero-aware root orientation.  See `iff_eq_zero_or_stablePencil` below for the
paper's coefficient-sensitive proper-position orientation. -/
theorem iff_interl_comp_sub {p : ℝ[X]} {α : ℝ} (hα : 0 < α) :
    p.MeshGE α ↔ RealRooted.Interl p (p.comp (X - C α)) := by
  constructor
  · intro hmesh
    by_cases hp0 : p = 0
    · simp [hp0, RealRooted.interl_zero_left]
    have hp : p ≠ 0 ∧ p.Splits := ⟨hp0, hmesh.1⟩
    let rs := p.roots.sort (· ≤ ·)
    have hrs : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort p.roots (· ≤ ·)
    have hmap : (rs.map (· + α)).Pairwise (· ≤ ·) := by
      rw [List.pairwise_map]
      exact hrs.imp_of_mem fun _ _ hab => by linarith
    have hroots : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq _ _
    have hshift_roots : (↑(rs.map (· + α)) : Multiset ℝ) =
        (p.comp (X - C α)).roots := by
      change (↑rs : Multiset ℝ).map (· + α) = _
      rw [hroots, roots_shift_eq_map]
    have halt : RealRooted.ListAlternates rs (rs.map (· + α)) := by
      apply RealRooted.listAlternates_of_getD_bounds
      · simp
      · intro i hi
        have hi0 : i < rs.length := by lia
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_getElem hi0]
        simp only [Option.map_some, Option.getD_some]
        linarith
      · intro i hi
        have hgap := hmesh.2.2 i (by simpa [rs] using hi)
        have hi0 : i < rs.length := by lia
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi]
        simp only [Option.map_some, Option.getD_some]
        simp only [List.getD_eq_getElem?_getD] at hgap
        rw [List.getElem?_eq_getElem (by simpa [rs] using hi0),
          List.getElem?_eq_getElem (by simpa [rs] using hi)] at hgap
        simp only [Option.getD_some] at hgap
        simpa [rs] using hgap
    exact (show RealRooted.StrictInterl p (p.comp (X - C α)) from
      ⟨hp, ⟨(comp_shift_ne_zero_iff p α).2 hp0, splits_comp_shift p hp.2 α⟩,
        rs, rs.map (· + α), hrs, hmap, hroots, hshift_roots,
        Or.inr ⟨by simp, halt⟩⟩).toInterl
  · intro hinterl
    refine ⟨?_, hα.le, ?_⟩
    · by_cases hp0 : p = 0
      · simp [hp0]
      exact (hinterl.toStrictInterl_of_ne hp0
        ((comp_shift_ne_zero_iff p α).2 hp0)).1.2
    · intro i hi
      by_cases hp0 : p = 0
      · simp [hp0] at hi
      have hstrict := hinterl.toStrictInterl_of_ne hp0
        ((comp_shift_ne_zero_iff p α).2 hp0)
      rcases hstrict with ⟨hp, hq, ss, rs, hss, hrs, hssroots, hrsroots, hshape⟩
      have hss_len : ss.length = p.natDegree :=
        hp.2.length_eq_natDegree_of_coe_eq_roots hssroots
      have hrs_len : rs.length = (p.comp (X - C α)).natDegree :=
        hq.2.length_eq_natDegree_of_coe_eq_roots hrsroots
      have hdeg : (p.comp (X - C α)).natDegree = p.natDegree := by
        rw [natDegree_comp_eq_of_mul_ne_zero (by simp [hp0])]
        simp
      obtain ⟨_, halt⟩ := hshape.resolve_left (by lia)
      have hss_sort := sorted_root_list_eq hss hssroots
      have hrs_eq_map : rs = ss.map (· + α) := by
        have hmap_ss : (ss.map (· + α)).Pairwise (· ≤ ·) := by
          rw [List.pairwise_map]
          exact hss.imp_of_mem fun _ _ hab => by linarith
        apply List.Perm.eq_of_pairwise' hrs hmap_ss
        apply Multiset.coe_eq_coe.mp
        change (↑rs : Multiset ℝ) = (↑ss : Multiset ℝ).map (· + α)
        rw [hrsroots, roots_shift_eq_map, ← hssroots]
      have hbounds := RealRooted.listAlternates_getD_bounds ss rs halt (by lia)
      have hgap := hbounds.2 i (by simpa [hss_sort] using hi)
      rw [hss_sort]
      have hi0 : i < ss.length := by simpa [hss_sort] using (show i < _ by lia)
      have hi1 : i + 1 < ss.length := by simpa [hss_sort] using hi
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi1]
      simp only [Option.getD_some]
      rw [hrs_eq_map] at hgap
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hgap
      rw [List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi1] at hgap
      simp only [Option.map_some, Option.getD_some] at hgap
      exact hgap

/-- Translation of the variable does not change a mesh bound. -/
theorem comp_X_add_C_iff (p : ℝ[X]) (α r : ℝ) :
    (p.comp (X + C r)).MeshGE α ↔ p.MeshGE α := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · constructor <;> intro h <;> linarith [h.2.1]
  · constructor <;> intro h
    · have hs : p.Splits := by
        have hs := (show (p.comp (X + C r)).Splits from h.1).comp_X_add_C (-r)
        simpa [comp_assoc, add_assoc] using hs
      exact zero hs
    · exact zero (h.1.comp_X_add_C r)
  · rw [iff_interl_comp_sub hα, iff_interl_comp_sub hα]
    have hcomp :
        (p.comp (X - C α)).comp (X + C r) =
          (p.comp (X + C r)).comp (X - C α) := by
      simp only [comp_assoc, sub_comp, add_comp, X_comp, C_comp]
      congr 1
      ring
    rw [← hcomp, RealRooted.Interl.comp_X_add_C_iff]

/-- Multiplication by a nonzero scalar does not change a mesh bound. -/
theorem C_mul_iff (p : ℝ[X]) (α : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (C c * p).MeshGE α ↔ p.MeshGE α := by
  simp only [MeshGE, roots_C_mul p hc]
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    by_cases hp0 : p = 0
    · simp [hp0]
    · exact h.1.of_dvd (mul_ne_zero (C_ne_zero.mpr hc) hp0) (dvd_mul_left p (C c))
  · intro h
    exact ⟨h.1.C_mul c, h.2⟩

/-- Positive scaling of the variable divides the mesh parameter by the scale. -/
theorem comp_C_mul_X {p : ℝ[X]} {α a : ℝ} (h : p.MeshGE α) (ha : 0 < a) :
    (p.comp (C a * X)).MeshGE (α / a) := by
  by_cases hα0 : α = 0
  · subst α
    simpa only [zero_div] using zero (p := p.comp (C a * X)) (by
      by_cases hp0 : p = 0
      · simp [hp0]
      · exact h.1.comp_of_natDegree_le_one (by simp [ha.ne']))
  · have hα : 0 < α := lt_of_le_of_ne h.2.1 (Ne.symm hα0)
    rw [iff_interl_comp_sub (div_pos hα ha)]
    have hinterl := (iff_interl_comp_sub hα).1 h
    have hscaled := hinterl.comp_C_mul_X ha
    have hcomp :
        (p.comp (X - C α)).comp (C a * X) =
          (p.comp (C a * X)).comp (X - C (α / a)) := by
      simp only [comp_assoc, sub_comp, mul_comp, X_comp, C_comp]
      congr 1
      rw [mul_sub, ← C_mul]
      congr 1
      field_simp
    rwa [hcomp] at hscaled

/-- The coefficient-sensitive form of the BKS mesh criterion.  The repository's
stable-pencil predicate is the paper's proper-position orientation: the base is
`p(x - α)` and the pencil direction is `p(x)`.  The disjunction records the
paper's convention that the zero polynomial is in proper position with itself. -/
theorem iff_eq_zero_or_stablePencil {p : ℝ[X]} {α : ℝ} (hα : 0 < α) :
    p.MeshGE α ↔
      p = 0 ∨
        RealRooted.IsUpperHalfPlaneStablePencil (p.comp (X - C α)) p := by
  constructor
  · intro hmesh
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      have hstrict := ((iff_interl_comp_sub hα).1 hmesh).toStrictInterl_of_ne
        hp0 ((comp_shift_ne_zero_iff p α).2 hp0)
      have hlc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
      rcases lt_or_gt_of_ne hlc0 with hlc | hlc
      · have hp_pos : RealRooted.HasPosLeadingCoeff (-p) := by
          simpa [RealRooted.HasPosLeadingCoeff] using neg_pos.mpr hlc
        have hq_pos : RealRooted.HasPosLeadingCoeff (-(p.comp (X - C α))) := by
          have hlead : (p.comp (X - C α)).leadingCoeff = p.leadingCoeff := by
            rw [Polynomial.leadingCoeff_comp (by simp), leadingCoeff_X_sub_C,
              one_pow, mul_one]
          simpa [RealRooted.HasPosLeadingCoeff, hlead] using neg_pos.mpr hlc
        have hneg : RealRooted.StrictInterl (-p) (-(p.comp (X - C α))) := by
          have hleft := hstrict.C_mul_left (a := -1) (by norm_num)
          have hboth := hleft.C_mul_right (a := -1) (by norm_num)
          simpa using hboth
        simpa using
          (RealRooted.isUpperHalfPlaneStablePencil_of_strictInterl
            hq_pos hp_pos hneg).neg_neg
      · have hp_pos : RealRooted.HasPosLeadingCoeff p := hlc
        have hq_pos : RealRooted.HasPosLeadingCoeff (p.comp (X - C α)) := by
          have hlead : (p.comp (X - C α)).leadingCoeff = p.leadingCoeff := by
            rw [Polynomial.leadingCoeff_comp (by simp), leadingCoeff_X_sub_C,
              one_pow, mul_one]
          simpa [RealRooted.HasPosLeadingCoeff, hlead]
        exact RealRooted.isUpperHalfPlaneStablePencil_of_strictInterl
          hq_pos hp_pos hstrict
  · rintro (rfl | hstable)
    · simp [MeshGE, hα.le]
    · by_cases hp0 : p = 0
      · simp [hp0, MeshGE, hα.le]
      · rw [iff_interl_comp_sub hα]
        have hq0 : p.comp (X - C α) ≠ 0 := (comp_shift_ne_zero_iff p α).2 hp0
        have hlc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
        by_cases hdeg : p.natDegree = 0
        · have hp : p.Splits := Polynomial.Splits.of_natDegree_eq_zero hdeg
          have hqp : p.comp (X - C α) = p := by
            rw [eq_C_of_natDegree_eq_zero hdeg]
            simp
          rw [hqp]
          exact (RealRooted.StrictInterl.refl hp0 hp).toInterl
        · have hqdeg : (p.comp (X - C α)).natDegree ≠ 0 := by
            rw [natDegree_comp_eq_of_mul_ne_zero (by simp [hp0])]
            simpa using hdeg
          rcases lt_or_gt_of_ne hlc0 with hlc | hlc
          · have hp_pos : RealRooted.HasPosLeadingCoeff (-p) := by
              simpa [RealRooted.HasPosLeadingCoeff] using neg_pos.mpr hlc
            have hq_pos : RealRooted.HasPosLeadingCoeff (-(p.comp (X - C α))) := by
              have hlead : (p.comp (X - C α)).leadingCoeff = p.leadingCoeff := by
                rw [Polynomial.leadingCoeff_comp (by simp), leadingCoeff_X_sub_C,
                  one_pow, mul_one]
              simpa [RealRooted.HasPosLeadingCoeff, hlead] using neg_pos.mpr hlc
            have hnegstable :
                RealRooted.IsUpperHalfPlaneStablePencil
                  (-(p.comp (X - C α))) (-p) := hstable.neg_neg
            have hnegdeg : (-(p.comp (X - C α))).natDegree ≠ 0 := by
              simpa using hqdeg
            have hneg := (RealRooted.isUpperHalfPlaneStablePencil_iff_strictInterl
              hq_pos hp_pos hnegdeg).1 hnegstable
            have hstrict : RealRooted.StrictInterl p (p.comp (X - C α)) := by
              have hleft := hneg.C_mul_left (a := -1) (by norm_num)
              have hboth := hleft.C_mul_right (a := -1) (by norm_num)
              simpa using hboth
            exact hstrict.toInterl
          · have hp_pos : RealRooted.HasPosLeadingCoeff p := hlc
            have hq_pos : RealRooted.HasPosLeadingCoeff (p.comp (X - C α)) := by
              have hlead : (p.comp (X - C α)).leadingCoeff = p.leadingCoeff := by
                rw [Polynomial.leadingCoeff_comp (by simp), leadingCoeff_X_sub_C,
                  one_pow, mul_one]
              simpa [RealRooted.HasPosLeadingCoeff, hlead]
            exact ((RealRooted.isUpperHalfPlaneStablePencil_iff_strictInterl
              hq_pos hp_pos hqdeg).1 hstable).toInterl

end MeshGE

end Polynomial
