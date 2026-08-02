import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.RootMatchingSort

/-!
# Closure of Liu root-count compatibility

This file closes the finite same-degree root inequalities under arbitrarily
small pointwise perturbations.  It is the ordered-root limit step used after
derivative-shift regularization.
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
      have hjrg : j < rg.length := by
        rw [← hgg.length_eq]
        exact hjg
      have hjrf : j - 1 < rf.length := by
        rw [← hff.length_eq]
        exact hjf
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
      have hjrf : j < rf.length := by
        rw [← hff.length_eq]
        exact hjf
      have hjrg : j - 1 < rg.length := by
        rw [← hgg.length_eq]
        exact hjg
      exact ⟨rf.getD j 0, rg.getD (j - 1) 0,
        by simpa using hff.get hjf hjrf,
        by simpa using hgg.get hjg hjrg, hfg.2 j hj1 hj⟩
  have hlower := sameDegreeRootCount_of_rootCrossing hf hg hdeg hcross
  have hupper := sameDegreeRootCountAbove_of_rootCount hf hg hdeg hlower
  exact RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hf_ne hg_ne (fun x _ _ => hupper x)

end LiuOppositeSigns
end RealRooted
