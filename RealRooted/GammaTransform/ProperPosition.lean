import RealRooted.GammaTransform.RootLists
import RealRooted.GammaTransform.Preservation

/-!
# Gamma-transform proper position

The adjacent-ambient-degree proper-position equivalence for gamma transforms.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

open GammaTransformInternal

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
    (preferredRoots d γ).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

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
  simpa [card_roots_of_splits hγsplits] using hcard

private lemma map_gammaRootMap_preferredRoots_pairwise (d : ℕ) (γ : ℝ[X]) :
    ((preferredRoots d γ).map gammaRootMap).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact (preferredRoots_pairwise d γ).imp_of_mem fun hx hy hxy =>
    strictMonoOn_gammaRootMap.monotoneOn
      (mem_preferredRoots hx) (mem_preferredRoots hy) hxy

private lemma Prec.sorted_roots_shape {f g : ℝ[X]} (h : Prec f g) :
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

/-- Hoster--Stump, Proposition 2.5: proper position is equivalent before and
after applying adjacent-degree gamma transforms. -/
theorem prec_gammaTransform_succ_iff
    {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2)
    (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγnn : HasNonnegCoeffs γ)
    (hδnn : HasNonnegCoeffs δ)
    (hγ0 : γ.coeff 0 ≠ 0)
    (hδ0 : δ.coeff 0 ≠ 0) :
    Prec (gammaTransform d γ) (gammaTransform (d + 1) δ) ↔
      Prec γ δ := by
  have hγ : γ ≠ 0 := by
    intro hzero
    apply hγ0
    simp [hzero]
  have hδ : δ ≠ 0 := by
    intro hzero
    apply hδ0
    simp [hzero]
  have hγmul : γ.natDegree * 2 ≤ d := Nat.mul_le_of_le_div 2 _ _ hγdeg
  have hδmul : δ.natDegree * 2 ≤ d + 1 := Nat.mul_le_of_le_div 2 _ _ hδdeg
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
  let ss := preferredRoots d γ
  let rs := preferredRoots (d + 1) δ
  have hss : ∀ x ∈ ss, x ∈ Set.Ioo (-1 : ℝ) 0 := by exact fun _ hx => mem_preferredRoots hx
  have hrs : ∀ x ∈ rs, x ∈ Set.Ioo (-1 : ℝ) 0 := by exact fun _ hx => mem_preferredRoots hx
  constructor
  · intro hTprec
    have hγrr :=
      isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
        hγdeg hTprec.1.1 hTprec.1.2
        (roots_nonpos_of_hasNonnegCoeffs hTγnn)
    have hδrr :=
      isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
        hδdeg hTprec.2.1.1 hTprec.2.1.2
        (roots_nonpos_of_hasNonnegCoeffs hTδnn)
    have hsslen : ss.length = γ.natDegree := by
      exact length_preferredRoots hγdeg hγ hγrr.1.2
        (roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0)
    have hrslen : rs.length = δ.natDegree := by
      exact length_preferredRoots hδdeg hδ hδrr.1.2
        (roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0)
    have hmult := rootMultiplicity_bounds_of_prec hTprec (-1)
    rw [rootMultiplicity_neg_one_gammaTransform hγdeg hγ,
      rootMultiplicity_neg_one_gammaTransform hδdeg hδ] at hmult
    have hdegcases : γ.natDegree = δ.natDegree ∨
        γ.natDegree + 1 = δ.natDegree := by
      lia
    have hsorted := hTprec.sorted_roots_shape
    rw [sort_roots_gammaTransform_eq_reciprocalCenterRoots hγdeg hγ hTγneg,
      sort_roots_gammaTransform_eq_reciprocalCenterRoots hδdeg hδ hTδneg] at hsorted
    have hfull :
        ListInterlaces
          (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
          (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
      rcases hsorted with hsorted | hsorted
      · exact hsorted.2
      · exfalso
        simp [reciprocalCenterRoots] at hsorted
        lia
    have hpreferred :
        ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
          (ss.length = rs.length ∧ ListAlternates ss rs)) := by
      rcases hdegcases with hsame | hsucc
      · right
        have hlen : ss.length = rs.length := by lia
        refine ⟨hlen, ?_⟩
        have hcenter : d + 1 - 2 * δ.natDegree =
            (d - 2 * γ.natDegree) + 1 := by
          lia
        rw [hcenter] at hfull
        exact (listInterlaces_reciprocalCenterRoots_same_iff
          (d - 2 * γ.natDegree) hss hrs hlen).1 hfull
      · left
        have hlen : ss.length + 1 = rs.length := by lia
        refine ⟨hlen, ?_⟩
        have hcenter : d - 2 * γ.natDegree =
            (d + 1 - 2 * δ.natDegree) + 1 := by
          lia
        rw [hcenter] at hfull
        exact (listInterlaces_reciprocalCenterRoots_succ_iff
          (d + 1 - 2 * δ.natDegree) hss hrs hlen).1 hfull
    have hγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0
    have hδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0
    refine ⟨hγrr.1, hδrr.1, ss.map gammaRootMap, rs.map gammaRootMap,
      ?_, ?_, coe_map_gammaRootMap_preferredRoots hγdeg hγ hγneg,
      coe_map_gammaRootMap_preferredRoots hδdeg hδ hδneg, ?_⟩
    · exact map_gammaRootMap_preferredRoots_pairwise d γ
    · exact map_gammaRootMap_preferredRoots_pairwise (d + 1) δ
    · rcases hpreferred with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
      · left
        refine ⟨by simpa using hlen, ?_⟩
        apply (listInterlaces_iff_interleaves_of_length (by simpa using hlen)).2
        apply (interleaves_map_gammaRootMap_iff hss hrs).2
        exact (listInterlaces_iff_interleaves_of_length hlen).1 hint
      · right
        refine ⟨by simpa using hlen, ?_⟩
        apply (listAlternates_iff_interleaves_of_length (by simpa using hlen)).2
        apply (interleaves_map_gammaRootMap_iff hrs hss).2
        exact (listAlternates_iff_interleaves_of_length hlen).1 halt
  · intro hprec
    have hγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0
    have hδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0
    have hsslen : ss.length = γ.natDegree :=
      length_preferredRoots hγdeg hγ hprec.1.2 hγneg
    have hrslen : rs.length = δ.natDegree :=
      length_preferredRoots hδdeg hδ hprec.2.1.2 hδneg
    have hsorted := hprec.sorted_roots_shape
    rw [sort_roots_eq_map_gammaRootMap_preferredRoots hγdeg hγ hγneg,
      sort_roots_eq_map_gammaRootMap_preferredRoots hδdeg hδ hδneg] at hsorted
    have hpreferred :
        ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
          (ss.length = rs.length ∧ ListAlternates ss rs)) := by
      rcases hsorted with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
      · left
        have hlen' : ss.length + 1 = rs.length := by simpa using hlen
        refine ⟨hlen', ?_⟩
        apply (listInterlaces_iff_interleaves_of_length hlen').2
        apply (interleaves_map_gammaRootMap_iff hss hrs).1
        exact (listInterlaces_iff_interleaves_of_length hlen).1 hint
      · right
        have hlen' : ss.length = rs.length := by simpa using hlen
        refine ⟨hlen', ?_⟩
        apply (listAlternates_iff_interleaves_of_length hlen').2
        apply (interleaves_map_gammaRootMap_iff hrs hss).1
        exact (listAlternates_iff_interleaves_of_length hlen).1 halt
    have hTγrr :=
      isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
        hγdeg hγ hprec.1.2 hγnn
    have hTδrr :=
      isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
        hδdeg hδ hprec.2.1.2 hδnn
    rcases hpreferred with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · have hcenter : d - 2 * γ.natDegree =
          (d + 1 - 2 * δ.natDegree) + 1 := by
        rw [hsslen, hrslen] at hlen
        lia
      have hfull :
          ListInterlaces
            (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
        rw [hcenter]
        exact (listInterlaces_reciprocalCenterRoots_succ_iff
          (d + 1 - 2 * δ.natDegree) hss hrs hlen).2 hint
      have hfull_len :
          (reciprocalCenterRoots (d - 2 * γ.natDegree) ss).length + 1 =
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs).length := by
        simp [reciprocalCenterRoots, hsslen, hrslen]
        lia
      have hi := (listInterlaces_iff_interleaves_of_length hfull_len).1 hfull
      refine ⟨hTγrr, hTδrr,
        reciprocalCenterRoots (d - 2 * γ.natDegree) ss,
        reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs,
        hi.pairwise_left, hi.pairwise_right,
        coe_reciprocalCenterRoots_eq_roots hγdeg hγ hTγneg,
        coe_reciprocalCenterRoots_eq_roots hδdeg hδ hTδneg,
        Or.inl ⟨hfull_len, hfull⟩⟩
    · have hcenter : d + 1 - 2 * δ.natDegree =
          (d - 2 * γ.natDegree) + 1 := by
        rw [hsslen, hrslen] at hlen
        lia
      have hfull :
          ListInterlaces
            (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
        rw [hcenter]
        exact (listInterlaces_reciprocalCenterRoots_same_iff
          (d - 2 * γ.natDegree) hss hrs hlen).2 halt
      have hfull_len :
          (reciprocalCenterRoots (d - 2 * γ.natDegree) ss).length + 1 =
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs).length := by
        simp [reciprocalCenterRoots, hsslen, hrslen]
        lia
      have hi := (listInterlaces_iff_interleaves_of_length hfull_len).1 hfull
      refine ⟨hTγrr, hTδrr,
        reciprocalCenterRoots (d - 2 * γ.natDegree) ss,
        reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs,
        hi.pairwise_left, hi.pairwise_right,
        coe_reciprocalCenterRoots_eq_roots hγdeg hγ hTγneg,
        coe_reciprocalCenterRoots_eq_roots hδdeg hδ hTδneg,
        Or.inl ⟨hfull_len, hfull⟩⟩



end RealRooted
