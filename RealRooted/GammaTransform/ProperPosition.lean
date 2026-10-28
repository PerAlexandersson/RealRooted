module

import RealRooted.GammaTransform.RootLists
import RealRooted.GammaTransform.Preservation
public import RealRooted.GammaTransform.Basic
public import RealRooted.Basic.ProperPosition

/-!
# Gamma-transform interlacing

The adjacent-ambient-degree interlacing equivalence for gamma transforms.
-/

@[expose] public section

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

open GammaTransform

private lemma roots_neg_of_nonnegCoeffs_of_coeff_zero_ne
    {p : ℝ[X]} (hnn : HasNonnegCoeffs p) (hzero : p.coeff 0 ≠ 0) :
    ∀ x ∈ p.roots, x < 0 := by
  intro x hx
  have hxle := roots_nonpos_of_hasNonnegCoeffs hnn x hx
  have hxne : x ≠ 0 := by
    intro hxeq
    subst x
    have hroot : p.eval 0 = 0 := isRoot_of_mem_roots hx
    apply hzero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact hroot
  exact lt_of_le_of_ne hxle hxne

private noncomputable def preferredRoots (d : ℕ) (γ : ℝ[X]) : List ℝ :=
  ((gammaTransform d γ).roots.filter
    (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).sort (· ≤ ·)

private lemma preferredRoots_pairwise (d : ℕ) (γ : ℝ[X]) :
    (preferredRoots d γ).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

private lemma mem_preferredRoots {d : ℕ} {γ : ℝ[X]} {x : ℝ}
    (hx : x ∈ preferredRoots d γ) : x ∈ Set.Ioo (-1 : ℝ) 0 := by
  rw [preferredRoots, Multiset.mem_sort] at hx
  exact (Multiset.mem_filter.mp hx).2

private lemma coe_map_gammaRootMap_preferredRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hγneg : ∀ x ∈ γ.roots, x < 0) :
    (↑((preferredRoots d γ).map gammaRootMap) : Multiset ℝ) = γ.roots := by
  change Multiset.map gammaRootMap (↑(preferredRoots d γ) : Multiset ℝ) = γ.roots
  rw [show (↑(preferredRoots d γ) : Multiset ℝ) =
    (gammaTransform d γ).roots.filter
      (fun x => x ∈ Set.Ioo (-1 : ℝ) 0) by simp [preferredRoots]]
  exact (roots_eq_map_filter_roots_gammaTransform hγdeg hγ hγneg).symm

private lemma length_preferredRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hγsplits : γ.Splits)
    (hγneg : ∀ x ∈ γ.roots, x < 0) :
    (preferredRoots d γ).length = γ.natDegree := by
  have hcoe := coe_map_gammaRootMap_preferredRoots hγdeg hγ hγneg
  have hcard := congrArg Multiset.card hcoe
  simpa [Polynomial.splits_iff_card_roots.mp hγsplits] using hcard

private lemma map_gammaRootMap_preferredRoots_pairwise (d : ℕ) (γ : ℝ[X]) :
    ((preferredRoots d γ).map gammaRootMap).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact (preferredRoots_pairwise d γ).imp_of_mem fun hx hy hxy =>
    strictMonoOn_gammaRootMap.monotoneOn
      (mem_preferredRoots hx) (mem_preferredRoots hy) hxy

private lemma StrictInterl.sorted_roots_shape {f g : ℝ[X]} (h : StrictInterl f g) :
    let ss := f.roots.sort (· ≤ ·)
    let rs := g.roots.sort (· ≤ ·)
    ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs)) := by
  rcases h with ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_sort : ss = f.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hss (Multiset.pairwise_sort _ _)
    exact Multiset.coe_eq_coe.mp (hss_eq.trans (Multiset.sort_eq _ _).symm)
  have hrs_sort : rs = g.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs (Multiset.pairwise_sort _ _)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq _ _).symm)
  simpa [hss_sort, hrs_sort] using hshape

private lemma sort_roots_eq_map_gammaRootMap_preferredRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hγneg : ∀ x ∈ γ.roots, x < 0) :
    γ.roots.sort (· ≤ ·) = (preferredRoots d γ).map gammaRootMap := by
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
    (map_gammaRootMap_preferredRoots_pairwise d γ)
  exact Multiset.coe_eq_coe.mp
    ((Multiset.sort_eq _ _).trans
      (coe_map_gammaRootMap_preferredRoots hγdeg hγ hγneg).symm)

private lemma reciprocalCenterRoots_pairwise
    {s : List ℝ} (m : ℕ) (hs : s.Pairwise (· ≤ ·))
    (hsmem : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0) :
    (reciprocalCenterRoots m s).Pairwise (· ≤ ·) := by
  let a := s.reverse.map fun x => x⁻¹
  let c := List.replicate m (-1 : ℝ)
  have ha : a.Pairwise (· ≤ ·) := by
    dsimp [a]
    rw [List.pairwise_map, List.pairwise_reverse]
    exact hs.imp_of_mem fun hx hy hxy =>
      inv_antitoneOn_Iio (hsmem _ hx).2 (hsmem _ hy).2 hxy
  have hc : c.Pairwise (· ≤ ·) := by simp [c]
  have hac : (a ++ c).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨ha, hc, ?_⟩
    intro x hx y hy
    dsimp [a] at hx
    rw [List.mem_map] at hx
    rcases hx with ⟨z, hz, rfl⟩
    have hzmem : z ∈ s := List.mem_reverse.mp hz
    have hzlt : z⁻¹ < -1 := by
      rw [inv_eq_one_div]
      exact (div_lt_iff_of_neg (hsmem z hzmem).2).2
        (by nlinarith [(hsmem z hzmem).1])
    have hy' : y = -1 := by
      dsimp [c] at hy
      exact (List.mem_replicate.mp hy).2
    linarith
  have hacs : ((a ++ c) ++ s).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨hac, hs, ?_⟩
    intro x hx y hy
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · dsimp [a] at hx
      rw [List.mem_map] at hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzmem : z ∈ s := List.mem_reverse.mp hz
      have hzlt : z⁻¹ < -1 := by
        rw [inv_eq_one_div]
        exact (div_lt_iff_of_neg (hsmem z hzmem).2).2
          (by nlinarith [(hsmem z hzmem).1])
      linarith [(hsmem y hy).1]
    · have hx' : x = -1 := by
        dsimp [c] at hx
        exact (List.mem_replicate.mp hx).2
      linarith [(hsmem y hy).1]
  simpa [reciprocalCenterRoots, a, c, List.append_assoc] using hacs

private lemma coe_reciprocalCenterRoots_eq_roots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0) :
    (↑(reciprocalCenterRoots (d - 2 * γ.natDegree)
      (preferredRoots d γ)) : Multiset ℝ) = (gammaTransform d γ).roots := by
  let s := preferredRoots d γ
  unfold reciprocalCenterRoots
  calc
    (↑((s.map fun x => x⁻¹).reverse ++
        (List.replicate (d - 2 * γ.natDegree) (-1 : ℝ) ++ s)) : Multiset ℝ) =
        (↑((s.map fun x => x⁻¹).reverse) : Multiset ℝ) +
          ((↑(List.replicate (d - 2 * γ.natDegree) (-1 : ℝ)) : Multiset ℝ) +
            (↑s : Multiset ℝ)) := by
      rfl
    _ = Multiset.map (fun x : ℝ => x⁻¹) (↑s : Multiset ℝ) +
          (Multiset.replicate (d - 2 * γ.natDegree) (-1) +
            (↑s : Multiset ℝ)) := by
      rw [Multiset.coe_reverse, Multiset.coe_replicate]
      rfl
    _ = (gammaTransform d γ).roots := by
      rw [show (↑s : Multiset ℝ) =
        (gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : ℝ) 0) by simp [s, preferredRoots]]
      simpa only [add_assoc] using
        (roots_gammaTransform_eq_reciprocal_add_neg_one_add hγdeg hγ hneg).symm

private lemma sort_roots_gammaTransform_eq_reciprocalCenterRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0) :
    (gammaTransform d γ).roots.sort (· ≤ ·) =
      reciprocalCenterRoots (d - 2 * γ.natDegree) (preferredRoots d γ) := by
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
    (reciprocalCenterRoots_pairwise _ (preferredRoots_pairwise d γ)
      (fun _ hx => mem_preferredRoots hx))
  exact Multiset.coe_eq_coe.mp
    ((Multiset.sort_eq _ _).trans
      (coe_reciprocalCenterRoots_eq_roots hγdeg hγ hneg).symm)

/-- Transformed interlacing restricts to the corresponding preferred-root shape. -/
private lemma preferredRoots_shape_of_strictInterl_gammaTransform
    {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hγneg : ∀ x ∈ γ.roots, x < 0) (hδneg : ∀ x ∈ δ.roots, x < 0)
    (hTγneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0)
    (hTδneg : ∀ x ∈ (gammaTransform (d + 1) δ).roots, x < 0)
    (hTstrictInterl : StrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ)) :
    (γ ≠ 0 ∧ γ.Splits) ∧ (δ ≠ 0 ∧ δ.Splits) ∧
      (((preferredRoots d γ).length + 1 = (preferredRoots (d + 1) δ).length ∧
          ListInterlaces (preferredRoots d γ) (preferredRoots (d + 1) δ)) ∨
        ((preferredRoots d γ).length = (preferredRoots (d + 1) δ).length ∧
          ListAlternates (preferredRoots d γ) (preferredRoots (d + 1) δ))) := by
  let ss := preferredRoots d γ
  let rs := preferredRoots (d + 1) δ
  have hγrr :=
    isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
      hγdeg hTstrictInterl.1.1 hTstrictInterl.1.2
      (fun x hx ↦ (hTγneg x hx).le)
  have hδrr :=
    isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
      hδdeg hTstrictInterl.2.1.1 hTstrictInterl.2.1.2
      (fun x hx ↦ (hTδneg x hx).le)
  have hsslen : ss.length = γ.natDegree :=
    length_preferredRoots hγdeg hγ hγrr.1.2 hγneg
  have hrslen : rs.length = δ.natDegree :=
    length_preferredRoots hδdeg hδ hδrr.1.2 hδneg
  have hmult := hTstrictInterl.rootMultiplicity_bounds (-1)
  rw [rootMultiplicity_neg_one_gammaTransform hγdeg hγ,
    rootMultiplicity_neg_one_gammaTransform hδdeg hδ] at hmult
  have hdegcases : γ.natDegree = δ.natDegree ∨
      γ.natDegree + 1 = δ.natDegree := by
    have hγmul : γ.natDegree * 2 ≤ d := Nat.mul_le_of_le_div 2 _ _ hγdeg
    have hδmul : δ.natDegree * 2 ≤ d + 1 := Nat.mul_le_of_le_div 2 _ _ hδdeg
    lia
  have hsorted := hTstrictInterl.sorted_roots_shape
  rw [sort_roots_gammaTransform_eq_reciprocalCenterRoots hγdeg hγ hTγneg,
    sort_roots_gammaTransform_eq_reciprocalCenterRoots hδdeg hδ hTδneg] at hsorted
  have hfull :
      ListInterlaces (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
        (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
    rcases hsorted with hsorted | hsorted
    · exact hsorted.2
    · exfalso
      simp [reciprocalCenterRoots] at hsorted
      lia
  refine ⟨hγrr.1, hδrr.1, ?_⟩
  rcases hdegcases with hsame | hsucc
  · right
    have hlen : ss.length = rs.length := by lia
    refine ⟨hlen, ?_⟩
    have hcenter : d + 1 - 2 * δ.natDegree = (d - 2 * γ.natDegree) + 1 := by lia
    rw [hcenter] at hfull
    exact (listInterlaces_reciprocalCenterRoots_same_iff
      (d - 2 * γ.natDegree) (fun _ hx ↦ mem_preferredRoots hx)
      (fun _ hx ↦ mem_preferredRoots hx) hlen).1 hfull
  · left
    have hlen : ss.length + 1 = rs.length := by lia
    refine ⟨hlen, ?_⟩
    have hcenter : d - 2 * γ.natDegree = (d + 1 - 2 * δ.natDegree) + 1 := by lia
    rw [hcenter] at hfull
    exact (listInterlaces_reciprocalCenterRoots_succ_iff
      (d + 1 - 2 * δ.natDegree) (fun _ hx ↦ mem_preferredRoots hx)
      (fun _ hx ↦ mem_preferredRoots hx) hlen).1 hfull

/-- A preferred-root shape assembles the original gamma polynomials' interlacing. -/
private lemma strictInterl_of_preferredRoots_shape {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγrr : γ ≠ 0 ∧ γ.Splits) (hδrr : δ ≠ 0 ∧ δ.Splits)
    (hγneg : ∀ x ∈ γ.roots, x < 0) (hδneg : ∀ x ∈ δ.roots, x < 0)
    (hpreferred :
      (((preferredRoots d γ).length + 1 = (preferredRoots (d + 1) δ).length ∧
          ListInterlaces (preferredRoots d γ) (preferredRoots (d + 1) δ)) ∨
        ((preferredRoots d γ).length = (preferredRoots (d + 1) δ).length ∧
          ListAlternates (preferredRoots d γ) (preferredRoots (d + 1) δ)))) :
    StrictInterl γ δ := by
  let ss := preferredRoots d γ
  let rs := preferredRoots (d + 1) δ
  refine ⟨hγrr, hδrr, ss.map gammaRootMap, rs.map gammaRootMap,
    map_gammaRootMap_preferredRoots_pairwise d γ,
    map_gammaRootMap_preferredRoots_pairwise (d + 1) δ,
    coe_map_gammaRootMap_preferredRoots hγdeg hγrr.1 hγneg,
    coe_map_gammaRootMap_preferredRoots hδdeg hδrr.1 hδneg, ?_⟩
  rcases hpreferred with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · left
    refine ⟨by simpa using hlen, ?_⟩
    apply (listInterlaces_iff_interleaves_of_length (by simpa using hlen)).2
    apply (interleaves_map_gammaRootMap_iff
      (fun _ hx ↦ mem_preferredRoots hx) (fun _ hx ↦ mem_preferredRoots hx)).2
    exact (listInterlaces_iff_interleaves_of_length hlen).1 hint
  · right
    refine ⟨by simpa using hlen, ?_⟩
    apply (listAlternates_iff_interleaves_of_length (by simpa using hlen)).2
    apply (interleaves_map_gammaRootMap_iff
      (fun _ hx ↦ mem_preferredRoots hx) (fun _ hx ↦ mem_preferredRoots hx)).2
    exact (listAlternates_iff_interleaves_of_length hlen).1 halt

/-- Original interlacing transports to the preferred roots of both transforms. -/
private lemma preferredRoots_shape_of_strictInterl {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hγneg : ∀ x ∈ γ.roots, x < 0) (hδneg : ∀ x ∈ δ.roots, x < 0)
    (hstrictInterl : StrictInterl γ δ) :
    (((preferredRoots d γ).length + 1 = (preferredRoots (d + 1) δ).length ∧
        ListInterlaces (preferredRoots d γ) (preferredRoots (d + 1) δ)) ∨
      ((preferredRoots d γ).length = (preferredRoots (d + 1) δ).length ∧
        ListAlternates (preferredRoots d γ) (preferredRoots (d + 1) δ))) := by
  let ss := preferredRoots d γ
  let rs := preferredRoots (d + 1) δ
  have hsorted := hstrictInterl.sorted_roots_shape
  rw [sort_roots_eq_map_gammaRootMap_preferredRoots hγdeg hγ hγneg,
    sort_roots_eq_map_gammaRootMap_preferredRoots hδdeg hδ hδneg] at hsorted
  rcases hsorted with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · left
    have hlen' : ss.length + 1 = rs.length := by simpa using hlen
    refine ⟨hlen', ?_⟩
    apply (listInterlaces_iff_interleaves_of_length hlen').2
    apply (interleaves_map_gammaRootMap_iff
      (fun _ hx ↦ mem_preferredRoots hx) (fun _ hx ↦ mem_preferredRoots hx)).1
    exact (listInterlaces_iff_interleaves_of_length hlen).1 hint
  · right
    have hlen' : ss.length = rs.length := by simpa using hlen
    refine ⟨hlen', ?_⟩
    apply (listAlternates_iff_interleaves_of_length hlen').2
    apply (interleaves_map_gammaRootMap_iff
      (fun _ hx ↦ mem_preferredRoots hx) (fun _ hx ↦ mem_preferredRoots hx)).1
    exact (listAlternates_iff_interleaves_of_length hlen).1 halt

/-- A preferred-root shape expands to interlacing of adjacent gamma transforms. -/
private lemma strictInterl_gammaTransform_of_preferredRoots_shape
    {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hTγrr : gammaTransform d γ ≠ 0 ∧ (gammaTransform d γ).Splits)
    (hTδrr : gammaTransform (d + 1) δ ≠ 0 ∧ (gammaTransform (d + 1) δ).Splits)
    (hTγneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0)
    (hTδneg : ∀ x ∈ (gammaTransform (d + 1) δ).roots, x < 0)
    (hsslen : (preferredRoots d γ).length = γ.natDegree)
    (hrslen : (preferredRoots (d + 1) δ).length = δ.natDegree)
    (hpreferred :
      (((preferredRoots d γ).length + 1 = (preferredRoots (d + 1) δ).length ∧
          ListInterlaces (preferredRoots d γ) (preferredRoots (d + 1) δ)) ∨
        ((preferredRoots d γ).length = (preferredRoots (d + 1) δ).length ∧
          ListAlternates (preferredRoots d γ) (preferredRoots (d + 1) δ)))) :
    StrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) := by
  let ss := preferredRoots d γ
  let rs := preferredRoots (d + 1) δ
  rcases hpreferred with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · have hcenter : d - 2 * γ.natDegree =
        (d + 1 - 2 * δ.natDegree) + 1 := by
      rw [← hsslen, ← hrslen]
      have hγmul : γ.natDegree * 2 ≤ d := Nat.mul_le_of_le_div 2 _ _ hγdeg
      lia
    have hfull := (listInterlaces_reciprocalCenterRoots_succ_iff
      (d + 1 - 2 * δ.natDegree) (fun _ hx ↦ mem_preferredRoots hx)
      (fun _ hx ↦ mem_preferredRoots hx) hlen).2 hint
    rw [← hcenter] at hfull
    have hfull_len :
        (reciprocalCenterRoots (d - 2 * γ.natDegree) ss).length + 1 =
          (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs).length := by
      simp [reciprocalCenterRoots]
      lia
    have hi := (listInterlaces_iff_interleaves_of_length hfull_len).1 hfull
    exact ⟨hTγrr, hTδrr, _, _, hi.pairwise_left, hi.pairwise_right,
      coe_reciprocalCenterRoots_eq_roots hγdeg hγ hTγneg,
      coe_reciprocalCenterRoots_eq_roots hδdeg hδ hTδneg,
      Or.inl ⟨hfull_len, hfull⟩⟩
  · have hcenter : d + 1 - 2 * δ.natDegree =
        (d - 2 * γ.natDegree) + 1 := by
      rw [← hsslen, ← hrslen]
      have hδmul : δ.natDegree * 2 ≤ d + 1 := Nat.mul_le_of_le_div 2 _ _ hδdeg
      lia
    have hfull := (listInterlaces_reciprocalCenterRoots_same_iff
      (d - 2 * γ.natDegree) (fun _ hx ↦ mem_preferredRoots hx)
      (fun _ hx ↦ mem_preferredRoots hx) hlen).2 halt
    rw [← hcenter] at hfull
    have hfull_len :
        (reciprocalCenterRoots (d - 2 * γ.natDegree) ss).length + 1 =
          (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs).length := by
      simp [reciprocalCenterRoots]
      lia
    have hi := (listInterlaces_iff_interleaves_of_length hfull_len).1 hfull
    exact ⟨hTγrr, hTδrr, _, _, hi.pairwise_left, hi.pairwise_right,
      coe_reciprocalCenterRoots_eq_roots hγdeg hγ hTγneg,
      coe_reciprocalCenterRoots_eq_roots hδdeg hδ hTδneg,
      Or.inl ⟨hfull_len, hfull⟩⟩

/-- Hoster--Stump, Proposition 2.5: interlacing is equivalent before and
after applying adjacent-degree gamma transforms. -/
theorem strictInterl_gammaTransform_succ_iff
    {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2)
    (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγnn : HasNonnegCoeffs γ)
    (hδnn : HasNonnegCoeffs δ)
    (hγ0 : γ.coeff 0 ≠ 0)
    (hδ0 : δ.coeff 0 ≠ 0) :
    StrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) ↔
      StrictInterl γ δ := by
  have hγ : γ ≠ 0 := by
    intro hzero
    apply hγ0
    simp [hzero]
  have hδ : δ ≠ 0 := by
    intro hzero
    apply hδ0
    simp [hzero]
  have hγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0
  have hδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0
  have hTγnn : HasNonnegCoeffs (gammaTransform d γ) :=
    hasNonnegCoeffs_gammaTransform hγnn
  have hTδnn : HasNonnegCoeffs (gammaTransform (d + 1) δ) :=
    hasNonnegCoeffs_gammaTransform hδnn
  have hTγ0 : (gammaTransform d γ).coeff 0 ≠ 0 := by
    simpa [coeff_zero_gammaTransform] using hγ0
  have hTδ0 : (gammaTransform (d + 1) δ).coeff 0 ≠ 0 := by
    simpa [coeff_zero_gammaTransform] using hδ0
  have hTγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hTγnn hTγ0
  have hTδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hTδnn hTδ0
  constructor
  · intro hTstrictInterl
    obtain ⟨hγrr, hδrr, hpreferred⟩ :=
      preferredRoots_shape_of_strictInterl_gammaTransform hγdeg hδdeg hγ hδ
        hγneg hδneg hTγneg hTδneg hTstrictInterl
    exact strictInterl_of_preferredRoots_shape hγdeg hδdeg hγrr hδrr
      hγneg hδneg hpreferred
  · intro hstrictInterl
    have hpreferred :=
      preferredRoots_shape_of_strictInterl hγdeg hδdeg hγ hδ hγneg hδneg hstrictInterl
    have hsslen :=
      length_preferredRoots hγdeg hγ hstrictInterl.1.2 hγneg
    have hrslen :=
      length_preferredRoots hδdeg hδ hstrictInterl.2.1.2 hδneg
    have hTγrr :=
      isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
        hγdeg hγ hstrictInterl.1.2 hγnn
    have hTδrr :=
      isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
        hδdeg hδ hstrictInterl.2.1.2 hδnn
    exact strictInterl_gammaTransform_of_preferredRoots_shape hγdeg hδdeg hγ hδ
      hTγrr hTδrr hTγneg hTδneg hsslen hrslen hpreferred

end RealRooted
