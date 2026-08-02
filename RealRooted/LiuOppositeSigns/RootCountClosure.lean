import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.LiuOppositeSigns.RootCountRelStability
import RealRooted.RootMatchingSort

/-!
# Closure of Liu root-count compatibility

This file closes finite same-degree and successor-degree root inequalities
under arbitrarily small pointwise perturbations.  It is the ordered-root limit
step used after derivative-shift regularization.
-/

namespace RealRooted
namespace LiuOppositeSigns

open Polynomial

/-- Same-degree root-count compatibility is closed under close finite crossings. -/
theorem RootCountCompatible.of_forall_pos_exists_close_sameDegreeCrossing
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits) (hdeg : g.natDegree = f.natDegree)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ rf rg : List ℝ,
        List.Forall₂ (fun x x' : ℝ => |x' - x| < ρ) (rootSeqDesc f) rf ∧
        List.Forall₂ (fun y y' : ℝ => |y' - y| < ρ) (rootSeqDesc g) rg ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
          rg.getD j 0 ≤ rf.getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
          rf.getD j 0 ≤ rg.getD (j - 1) 0)) :
    RootCountCompatible f g := by
  have hcross :
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤
          (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤
          (rootSeqDesc g).getD (j - 1) 0) := by
    constructor
    · intro j hj1 hj
      apply le_of_forall_pos_exists_close_le
      intro ρ hρ
      obtain ⟨rf, rg, hff, hgg, hfg⟩ := hclose ρ hρ
      have hjg : j < (rootSeqDesc g).length := by
        simpa only [rootSeqDesc_length hg, hdeg] using hj
      have hjf : j - 1 < (rootSeqDesc f).length := by
        rw [rootSeqDesc_length hf]
        lia
      have hjrg : j < rg.length := by simpa only [hgg.length_eq] using hjg
      have hjrf : j - 1 < rf.length := by
        simpa only [hff.length_eq] using hjf
      exact ⟨rg.getD j 0, rf.getD (j - 1) 0,
        by simpa using hgg.get hjg hjrg,
        by simpa using hff.get hjf hjrf, hfg.1 j hj1 hj⟩
    · intro j hj1 hj
      apply le_of_forall_pos_exists_close_le
      intro ρ hρ
      obtain ⟨rf, rg, hff, hgg, hfg⟩ := hclose ρ hρ
      have hjf : j < (rootSeqDesc f).length := by
        simpa only [rootSeqDesc_length hf] using hj
      have hjg : j - 1 < (rootSeqDesc g).length := by
        rw [rootSeqDesc_length hg, hdeg]
        lia
      have hjrf : j < rf.length := by simpa only [hff.length_eq] using hjf
      have hjrg : j - 1 < rg.length := by
        simpa only [hgg.length_eq] using hjg
      exact ⟨rf.getD j 0, rg.getD (j - 1) 0,
        by simpa using hff.get hjf hjrf,
        by simpa using hgg.get hjg hjrg, hfg.2 j hj1 hj⟩
  have hlower := sameDegreeRootCount_of_rootCrossing hf hg hdeg hcross
  have hupper := sameDegreeRootCountAbove_of_rootCount hf hg hdeg hlower
  exact RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hf_ne hg_ne (fun x _ _ => hupper x)

/-- Successor-degree root-count compatibility is closed under close finite crossings. -/
theorem RootCountCompatible.of_forall_pos_exists_close_succDegreeCrossing
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ rf rg : List ℝ,
        List.Forall₂ (fun x x' : ℝ => |x' - x| < ρ) (rootSeqDesc f) rf ∧
        List.Forall₂ (fun y y' : ℝ => |y' - y| < ρ) (rootSeqDesc g) rg ∧
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
          rg.getD j 0 ≤ rf.getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
          rf.getD j 0 ≤ rg.getD (j - 1) 0)) :
    RootCountCompatible f g := by
  have hcross :
      (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤
          (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤
          (rootSeqDesc g).getD (j - 1) 0) := by
    constructor
    · intro j hj1 hj
      apply le_of_forall_pos_exists_close_le
      intro ρ hρ
      obtain ⟨rf, rg, hff, hgg, hfg⟩ := hclose ρ hρ
      have hjg : j < (rootSeqDesc g).length := by
        rw [rootSeqDesc_length hg, hdeg]
        lia
      have hjf : j - 1 < (rootSeqDesc f).length := by
        rw [rootSeqDesc_length hf]
        lia
      have hjrg : j < rg.length := by simpa only [hgg.length_eq] using hjg
      have hjrf : j - 1 < rf.length := by
        simpa only [hff.length_eq] using hjf
      exact ⟨rg.getD j 0, rf.getD (j - 1) 0,
        by simpa using hgg.get hjg hjrg,
        by simpa using hff.get hjf hjrf, hfg.1 j hj1 hj⟩
    · intro j hj1 hj
      apply le_of_forall_pos_exists_close_le
      intro ρ hρ
      obtain ⟨rf, rg, hff, hgg, hfg⟩ := hclose ρ hρ
      have hjf : j < (rootSeqDesc f).length := by
        simpa only [rootSeqDesc_length hf] using hj
      have hjg : j - 1 < (rootSeqDesc g).length := by
        rw [rootSeqDesc_length hg, hdeg]
        lia
      have hjrf : j < rf.length := by simpa only [hff.length_eq] using hjf
      have hjrg : j - 1 < rg.length := by
        simpa only [hgg.length_eq] using hjg
      exact ⟨rf.getD j 0, rg.getD (j - 1) 0,
        by simpa using hff.get hjf hjrf,
        by simpa using hgg.get hjg hjrg, hfg.2 j hj1 hj⟩
  have hlower := succDegreeRootCount_of_rootCrossing hf hg hdeg hcross
  have hupper := succDegreeRootCountAbove_of_rootCount hf hg hdeg hlower
  exact RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hf_ne hg_ne (fun x _ _ => hupper x)

/-- Same-degree root-count compatibility is closed under close compatible pairs. -/
theorem RootCountCompatible.of_forall_pos_exists_close_sameDegreeCompatible
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hp : p.Splits) (hq : q.Splits)
    (hdeg : q.natDegree = p.natDegree)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ p' q' : ℝ[X],
        p' ≠ 0 ∧
        q' ≠ 0 ∧
        p'.Splits ∧
        q'.Splits ∧
        List.Forall₂
          (fun x x' : ℝ => |x' - x| < ρ)
          (rootSeqDesc p) (rootSeqDesc p') ∧
        List.Forall₂
          (fun y y' : ℝ => |y' - y| < ρ)
          (rootSeqDesc q) (rootSeqDesc q') ∧
        RootCountCompatible p' q') :
    RootCountCompatible p q := by
  refine RootCountCompatible.of_forall_pos_exists_close_sameDegreeCrossing
    hp_ne hq_ne hp hq hdeg ?_
  intro ρ hρ
  obtain ⟨p', q', hp'_ne, hq'_ne, hp'_split, hq'_split,
      hpp', hqq', hcompat'⟩ :=
    hclose ρ hρ
  have hpdeg : p'.natDegree = p.natDegree := by
    rw [← rootSeqDesc_length hp'_split, ← rootSeqDesc_length hp]
    exact hpp'.length_eq.symm
  have hqdeg : q'.natDegree = q.natDegree := by
    rw [← rootSeqDesc_length hq'_split, ← rootSeqDesc_length hq]
    exact hqq'.length_eq.symm
  have hdeg' : q'.natDegree = p'.natDegree := by
    rw [hqdeg, hpdeg, hdeg]
  have hcount' :=
    sameDegreeRootCountAbove_of_nonRoot_bound hp'_ne hq'_ne
      (hcompat'.rootCountAbove_bounds_of_nonRoot hp'_ne hq'_ne)
  exact ⟨rootSeqDesc p', rootSeqDesc q', hpp', hqq',
    rootCrossing_of_rootCountAbove_diff_le_one
      hp'_split hq'_split hdeg' hcount'⟩

/-- Successor-degree root-count compatibility is closed under close compatible pairs. -/
theorem RootCountCompatible.of_forall_pos_exists_close_succDegreeCompatible
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hp : p.Splits) (hq : q.Splits)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ p' q' : ℝ[X],
        p' ≠ 0 ∧
        q' ≠ 0 ∧
        p'.Splits ∧
        q'.Splits ∧
        List.Forall₂
          (fun x x' : ℝ => |x' - x| < ρ)
          (rootSeqDesc p) (rootSeqDesc p') ∧
        List.Forall₂
          (fun y y' : ℝ => |y' - y| < ρ)
          (rootSeqDesc q) (rootSeqDesc q') ∧
        RootCountCompatible p' q') :
    RootCountCompatible p q := by
  refine RootCountCompatible.of_forall_pos_exists_close_succDegreeCrossing
    hp_ne hq_ne hp hq hdeg ?_
  intro ρ hρ
  obtain ⟨p', q', hp'_ne, hq'_ne, hp'_split, hq'_split,
      hpp', hqq', hcompat'⟩ :=
    hclose ρ hρ
  have hpdeg : p'.natDegree = p.natDegree := by
    rw [← rootSeqDesc_length hp'_split, ← rootSeqDesc_length hp]
    exact hpp'.length_eq.symm
  have hqdeg : q'.natDegree = q.natDegree := by
    rw [← rootSeqDesc_length hq'_split, ← rootSeqDesc_length hq]
    exact hqq'.length_eq.symm
  have hdeg' : q'.natDegree = p'.natDegree + 1 := by
    rw [hqdeg, hpdeg, hdeg]
  have hcount' :=
    sameDegreeRootCountAbove_of_nonRoot_bound hp'_ne hq'_ne
      (hcompat'.rootCountAbove_bounds_of_nonRoot hp'_ne hq'_ne)
  exact ⟨rootSeqDesc p', rootSeqDesc q', hpp', hqq',
    succDegreeRootCrossing_of_rootCountAbove
      hp'_split hq'_split hdeg' hcount'⟩

/-- A fixed left branch is closed under close same-degree approximations. -/
theorem LeftRootCountBranch.of_forall_pos_exists_close_of_sameDegree
    {f g : ℝ[X]} {r s : ℝ}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hdeg : f.natDegree = g.natDegree)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ f' g' : ℝ[X], ∃ r' s' : ℝ,
        f' ≠ 0 ∧
        g' ≠ 0 ∧
        f'.Splits ∧
        g'.Splits ∧
        Multiset.Rel
          (fun x x' : ℝ => |x' - x| < ρ)
          f.roots f'.roots ∧
        Multiset.Rel
          (fun y y' : ℝ => |y' - y| < ρ)
          g.roots g'.roots ∧
        LeftRootCountBranch f' g' r' s') :
    LeftRootCountBranch f g r s := by
  have hlargest : s ≤ r := by
    apply le_of_forall_pos_exists_close_le
    intro ρ hρ
    obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranch'⟩ := hclose ρ hρ
    exact ⟨s', r',
      hs.abs_sub_lt_of_roots_rel hg_ne hg'_ne hbranch'.g_largest hgg',
      hr.abs_sub_lt_of_roots_rel hf_ne hf'_ne hbranch'.f_largest hff',
      hbranch'.largest_ge⟩
  have hdelete_degree :
      g.natDegree = (deleteRootFactor f r).natDegree + 1 := by
    rw [natDegree_deleteRootFactor]
    have hf_degree_pos := hr.natDegree_pos hf_ne
    lia
  have hcount : RootCountCompatible (deleteRootFactor f r) g := by
    refine RootCountCompatible.of_forall_pos_exists_close_succDegreeCompatible
      (hr.deleteRootFactor_ne_zero hf_ne) hg_ne
      (hr.deleteRootFactor_splits hf) hg hdelete_degree ?_
    intro ρ hρ
    obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranch'⟩ := hclose ρ hρ
    refine ⟨deleteRootFactor f' r', g',
      hbranch'.f_largest.deleteRootFactor_ne_zero hf'_ne,
      hg'_ne,
      hbranch'.f_largest.deleteRootFactor_splits hf'_split,
      hg'_split, ?_, ?_, hbranch'.count⟩
    · simpa only [rootSeqDesc_eq_sort_ge] using
        (forall₂_sort_ge_deleteRootFactor_of_roots_rel
          hf_ne hf'_ne hr hbranch'.f_largest hff')
    · simpa only [rootSeqDesc_eq_sort_ge] using
        (forall₂_sort_ge_of_rel_abs_sub_lt hgg')
  exact ⟨hr, hs, hlargest, hcount⟩

/-- A fixed left branch is closed when the first degree is one larger. -/
theorem LeftRootCountBranch.of_forall_pos_exists_close_of_degree_eq_succ
    {f g : ℝ[X]} {r s : ℝ}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ f' g' : ℝ[X], ∃ r' s' : ℝ,
        f' ≠ 0 ∧
        g' ≠ 0 ∧
        f'.Splits ∧
        g'.Splits ∧
        Multiset.Rel
          (fun x x' : ℝ => |x' - x| < ρ)
          f.roots f'.roots ∧
        Multiset.Rel
          (fun y y' : ℝ => |y' - y| < ρ)
          g.roots g'.roots ∧
        LeftRootCountBranch f' g' r' s') :
    LeftRootCountBranch f g r s := by
  have hlargest : s ≤ r := by
    apply le_of_forall_pos_exists_close_le
    intro ρ hρ
    obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranch'⟩ := hclose ρ hρ
    exact ⟨s', r',
      hs.abs_sub_lt_of_roots_rel hg_ne hg'_ne hbranch'.g_largest hgg',
      hr.abs_sub_lt_of_roots_rel hf_ne hf'_ne hbranch'.f_largest hff',
      hbranch'.largest_ge⟩
  have hdelete_degree :
      g.natDegree = (deleteRootFactor f r).natDegree := by
    rw [natDegree_deleteRootFactor]
    have hf_degree_pos := hr.natDegree_pos hf_ne
    lia
  have hcount : RootCountCompatible (deleteRootFactor f r) g := by
    refine RootCountCompatible.of_forall_pos_exists_close_sameDegreeCompatible
      (hr.deleteRootFactor_ne_zero hf_ne) hg_ne
      (hr.deleteRootFactor_splits hf) hg hdelete_degree ?_
    intro ρ hρ
    obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranch'⟩ := hclose ρ hρ
    refine ⟨deleteRootFactor f' r', g',
      hbranch'.f_largest.deleteRootFactor_ne_zero hf'_ne,
      hg'_ne,
      hbranch'.f_largest.deleteRootFactor_splits hf'_split,
      hg'_split, ?_, ?_, hbranch'.count⟩
    · simpa only [rootSeqDesc_eq_sort_ge] using
        (forall₂_sort_ge_deleteRootFactor_of_roots_rel
          hf_ne hf'_ne hr hbranch'.f_largest hff')
    · simpa only [rootSeqDesc_eq_sort_ge] using
        (forall₂_sort_ge_of_rel_abs_sub_lt hgg')
  exact ⟨hr, hs, hlargest, hcount⟩

/-- A fixed left branch is closed when the first degree is two larger. -/
theorem LeftRootCountBranch.of_forall_pos_exists_close_of_degree_eq_succ_succ
    {f g : ℝ[X]} {r s : ℝ}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ f' g' : ℝ[X], ∃ r' s' : ℝ,
        f' ≠ 0 ∧
        g' ≠ 0 ∧
        f'.Splits ∧
        g'.Splits ∧
        Multiset.Rel
          (fun x x' : ℝ => |x' - x| < ρ)
          f.roots f'.roots ∧
        Multiset.Rel
          (fun y y' : ℝ => |y' - y| < ρ)
          g.roots g'.roots ∧
        LeftRootCountBranch f' g' r' s') :
    LeftRootCountBranch f g r s := by
  have hlargest : s ≤ r := by
    apply le_of_forall_pos_exists_close_le
    intro ρ hρ
    obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranch'⟩ := hclose ρ hρ
    exact ⟨s', r',
      hs.abs_sub_lt_of_roots_rel hg_ne hg'_ne hbranch'.g_largest hgg',
      hr.abs_sub_lt_of_roots_rel hf_ne hf'_ne hbranch'.f_largest hff',
      hbranch'.largest_ge⟩
  have hdelete_degree :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 := by
    rw [natDegree_deleteRootFactor]
    have hf_degree_pos := hr.natDegree_pos hf_ne
    lia
  have hcount : RootCountCompatible (deleteRootFactor f r) g := by
    have hcount_symm : RootCountCompatible g (deleteRootFactor f r) := by
      refine RootCountCompatible.of_forall_pos_exists_close_succDegreeCompatible
        hg_ne (hr.deleteRootFactor_ne_zero hf_ne) hg
        (hr.deleteRootFactor_splits hf) hdelete_degree ?_
      intro ρ hρ
      obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
          hff', hgg', hbranch'⟩ := hclose ρ hρ
      refine ⟨g', deleteRootFactor f' r',
        hg'_ne,
        hbranch'.f_largest.deleteRootFactor_ne_zero hf'_ne,
        hg'_split,
        hbranch'.f_largest.deleteRootFactor_splits hf'_split,
        ?_, ?_, hbranch'.count.symm⟩
      · simpa only [rootSeqDesc_eq_sort_ge] using
          (forall₂_sort_ge_of_rel_abs_sub_lt hgg')
      · simpa only [rootSeqDesc_eq_sort_ge] using
          (forall₂_sort_ge_deleteRootFactor_of_roots_rel
            hf_ne hf'_ne hr hbranch'.f_largest hff')
    exact hcount_symm.symm
  exact ⟨hr, hs, hlargest, hcount⟩

/-- A fixed left branch is closed under close approximations. -/
theorem LeftRootCountBranch.of_forall_pos_exists_close
    {f g : ℝ[X]} {r s : ℝ}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ f' g' : ℝ[X], ∃ r' s' : ℝ,
        f' ≠ 0 ∧
        g' ≠ 0 ∧
        f'.Splits ∧
        g'.Splits ∧
        Multiset.Rel
          (fun x x' : ℝ => |x' - x| < ρ)
          f.roots f'.roots ∧
        Multiset.Rel
          (fun y y' : ℝ => |y' - y| < ρ)
          g.roots g'.roots ∧
        LeftRootCountBranch f' g' r' s') :
    LeftRootCountBranch f g r s := by
  obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
      hff', hgg', hbranch'⟩ := hclose 1 zero_lt_one
  have hf_degree : f'.natDegree = f.natDegree := by
    calc
      f'.natDegree = f'.roots.card := (card_roots_of_splits hf'_split).symm
      _ = f.roots.card := (Multiset.card_eq_card_of_rel hff').symm
      _ = f.natDegree := card_roots_of_splits hf
  have hg_degree : g'.natDegree = g.natDegree := by
    calc
      g'.natDegree = g'.roots.card := (card_roots_of_splits hg'_split).symm
      _ = g.roots.card := (Multiset.card_eq_card_of_rel hgg').symm
      _ = g.natDegree := card_roots_of_splits hg
  have hdegrees :=
    hbranch'.natDegree_eq_or_eq_succ_or_eq_succ_succ
      hf'_ne hf'_split hg'_split
  rw [hf_degree, hg_degree] at hdegrees
  rcases hdegrees with hdeg | hdeg | hdeg
  · exact LeftRootCountBranch.of_forall_pos_exists_close_of_sameDegree
      hf_ne hg_ne hf hg hr hs hdeg hclose
  · exact LeftRootCountBranch.of_forall_pos_exists_close_of_degree_eq_succ
      hf_ne hg_ne hf hg hr hs hdeg hclose
  · exact
      LeftRootCountBranch.of_forall_pos_exists_close_of_degree_eq_succ_succ
        hf_ne hg_ne hf hg hr hs hdeg hclose

/-- A fixed right branch is closed under close approximations. -/
theorem RightRootCountBranch.of_forall_pos_exists_close
    {f g : ℝ[X]} {r s : ℝ}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hrlt : r < s)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ f' g' : ℝ[X], ∃ r' s' : ℝ,
        f' ≠ 0 ∧
        g' ≠ 0 ∧
        f'.Splits ∧
        g'.Splits ∧
        Multiset.Rel
          (fun x x' : ℝ => |x' - x| < ρ)
          f.roots f'.roots ∧
        Multiset.Rel
          (fun y y' : ℝ => |y' - y| < ρ)
          g.roots g'.roots ∧
        RightRootCountBranch f' g' r' s') :
    RightRootCountBranch f g r s := by
  have hleft : LeftRootCountBranch g f s r := by
    apply LeftRootCountBranch.of_forall_pos_exists_close
      hg_ne hf_ne hg hf hs hr
    intro ρ hρ
    obtain ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranch'⟩ := hclose ρ hρ
    exact
      ⟨g', f', s', r',
        hg'_ne, hf'_ne,
        hg'_split, hf'_split,
        hgg', hff',
        hbranch'.toLeftBranch_symm⟩
  exact hleft.toRightBranch_symm_of_lt hrlt

/-- Liu's disjunctive root-count branch is closed under close splitting approximations. -/
theorem theorem21RootCountBranches_of_forall_pos_exists_roots_rel
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hclose : ∀ ρ : ℝ, 0 < ρ →
      ∃ f' g' : ℝ[X],
        f' ≠ 0 ∧
        g' ≠ 0 ∧
        f'.Splits ∧
        g'.Splits ∧
        Multiset.Rel
          (fun x x' : ℝ => |x' - x| < ρ)
          f.roots f'.roots ∧
        Multiset.Rel
          (fun y y' : ℝ => |y' - y| < ρ)
          g.roots g'.roots ∧
        theorem21RootCountBranches f' g') :
    theorem21RootCountBranches f g := by
  obtain ⟨r, hr⟩ :=
    exists_isLargestRoot hf_ne hf (Nat.pos_of_ne_zero hf_deg)
  obtain ⟨s, hs⟩ :=
    exists_isLargestRoot hg_ne hg (Nat.pos_of_ne_zero hg_deg)
  have hrs_ne : r ≠ s := by
    intro hrs
    subst s
    exact (hno r hr.isRoot) hs.isRoot
  rcases lt_or_gt_of_ne hrs_ne with hrs | hsr
  · apply theorem21RootCountBranches_of_right
    apply RightRootCountBranch.of_forall_pos_exists_close
      hf_ne hg_ne hf hg hr hs hrs
    intro ρ hρ
    let δ : ℝ := min ρ ((s - r) / 2)
    have hδ : 0 < δ :=
      lt_min hρ (half_pos (sub_pos.mpr hrs))
    have hδ_le_ρ : δ ≤ ρ := min_le_left _ _
    have hδ_le_gap : δ ≤ (s - r) / 2 := min_le_right _ _
    obtain ⟨f', g', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranches⟩ := hclose δ hδ
    obtain ⟨r', s', hbranch'⟩ := hbranches
    rcases hbranch' with hleft' | hright'
    · exfalso
      have hr_close :=
        hr.abs_sub_lt_of_roots_rel hf_ne hf'_ne hleft'.f_largest hff'
      have hs_close :=
        hs.abs_sub_lt_of_roots_rel hg_ne hg'_ne hleft'.g_largest hgg'
      rw [abs_lt] at hr_close hs_close
      linarith [hleft'.largest_ge, hδ_le_gap]
    · exact
        ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
          hff'.mono (fun _ _ _ _ h => h.trans_le hδ_le_ρ),
          hgg'.mono (fun _ _ _ _ h => h.trans_le hδ_le_ρ),
          hright'⟩
  · apply theorem21RootCountBranches_of_left
    apply LeftRootCountBranch.of_forall_pos_exists_close
      hf_ne hg_ne hf hg hr hs
    intro ρ hρ
    let δ : ℝ := min ρ ((r - s) / 2)
    have hδ : 0 < δ :=
      lt_min hρ (half_pos (sub_pos.mpr hsr))
    have hδ_le_ρ : δ ≤ ρ := min_le_left _ _
    have hδ_le_gap : δ ≤ (r - s) / 2 := min_le_right _ _
    obtain ⟨f', g', hf'_ne, hg'_ne, hf'_split, hg'_split,
        hff', hgg', hbranches⟩ := hclose δ hδ
    obtain ⟨r', s', hbranch'⟩ := hbranches
    rcases hbranch' with hleft' | hright'
    · exact
        ⟨f', g', r', s', hf'_ne, hg'_ne, hf'_split, hg'_split,
          hff'.mono (fun _ _ _ _ h => h.trans_le hδ_le_ρ),
          hgg'.mono (fun _ _ _ _ h => h.trans_le hδ_le_ρ),
          hleft'⟩
    · exfalso
      have hr_close :=
        hr.abs_sub_lt_of_roots_rel hf_ne hf'_ne hright'.f_largest hff'
      have hs_close :=
        hs.abs_sub_lt_of_roots_rel hg_ne hg'_ne hright'.g_largest hgg'
      rw [abs_lt] at hr_close hs_close
      linarith [hright'.largest_lt, hδ_le_gap]

end LiuOppositeSigns
end RealRooted
