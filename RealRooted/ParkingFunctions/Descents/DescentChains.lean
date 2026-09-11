import RealRooted.ParkingFunctions.Descents.Basic
import RealRooted.ParkingFunctions.Descents.ChainSort
import Mathlib.Data.List.FinRange
import RealRooted.Mathlib.Data.List.SplitBy

/-!
# Chains associated to a descent subset

This module partitions the ordered positions of a word into contiguous runs
whose adjacent edges are prescribed descents.  Reversing those runs produces
the strict increasing chains used in the parking-word transfer.
-/

namespace RealRooted.ParkingFunctions

/-- The ordered adjacent edge from `i` to `j` is selected by `S`. -/
def isDescentStep {n : ℕ} (S : Finset (Fin n))
    (i j : Fin (n + 1)) : Bool :=
  decide (∃ k : Fin n, k ∈ S ∧ i = k.castSucc ∧ j = k.succ)

/-- Contiguous increasing runs connected by the descent edges in `S`. -/
def descentRuns {n : ℕ} (S : Finset (Fin n)) : List (List (Fin (n + 1))) :=
  (List.ofFn id).splitBy (isDescentStep S)

/-- The runs partition the positions in their original order. -/
theorem flatten_descentRuns {n : ℕ} (S : Finset (Fin n)) :
    (descentRuns S).flatten = List.ofFn id :=
  List.flatten_splitBy _ _

/-- No contiguous descent run is empty. -/
theorem nil_not_mem_descentRuns {n : ℕ} (S : Finset (Fin n)) :
    [] ∉ descentRuns S :=
  List.nil_notMem_splitBy _ _

/-- Consecutive positions inside a descent run are selected descent edges. -/
theorem isChain_of_mem_descentRuns {n : ℕ} (S : Finset (Fin n))
    {l : List (Fin (n + 1))} (hl : l ∈ descentRuns S) :
    l.IsChain fun i j => isDescentStep S i j :=
  List.isChain_of_mem_splitBy hl

/-- Reverse each increasing run so strict increase along a chain represents a
strict descent along the original word positions. -/
def descentChains {n : ℕ} (S : Finset (Fin n)) : List (List (Fin (n + 1))) :=
  (descentRuns S).map List.reverse

/-- Consecutive positions in a reversed descent chain read a selected edge in
the descent direction. -/
theorem isChain_of_mem_descentChains {n : ℕ} (S : Finset (Fin n))
    {l : List (Fin (n + 1))} (hl : l ∈ descentChains S) :
    l.IsChain fun i j => isDescentStep S j i := by
  rw [descentChains, List.mem_map] at hl
  obtain ⟨run, hrun, rfl⟩ := hl
  exact List.isChain_reverse.mpr (isChain_of_mem_descentRuns S hrun)

private theorem infix_adjacent_positions {n : ℕ} (k : Fin n) :
    [k.castSucc, k.succ] <:+: List.ofFn (id : Fin (n + 1) → Fin (n + 1)) := by
  apply List.infix_iff_getElem?.mpr
  refine ⟨k.val, by simp; lia, ?_⟩
  intro i hi
  cases i with
  | zero =>
      rw [List.getElem?_ofFn]
      split
      · congr 1
        apply Fin.ext
        simp
      · exact False.elim (by lia)
  | succ i =>
      cases i with
      | zero =>
          rw [List.getElem?_ofFn]
          split
          · congr 1
            apply Fin.ext
            simp [Nat.add_comm]
          · exact False.elim (by lia)
      | succ i => exact False.elim (by simp at hi; lia)

private theorem isDescentStep_castSucc_succ {n : ℕ} (S : Finset (Fin n))
    {k : Fin n} (hk : k ∈ S) :
    isDescentStep S k.castSucc k.succ = true := by
  simp [isDescentStep, hk]

/-- Strict sorting on the reversed selected runs realizes every prescribed
descent. -/
theorem hasDescentsAt_of_isStrictChainSorted_descentChains {n : ℕ}
    (S : Finset (Fin n)) (w : Fin (n + 1) → Fin (n + 2))
    (hsorted : IsStrictChainSorted (descentChains S) w) :
    HasDescentsAt S w := by
  rw [hasDescentsAt_iff]
  intro k hk
  obtain ⟨run, hrun, hinfix⟩ :=
    List.exists_infix_splitBy_of_rel_of_infix (isDescentStep S) (List.ofFn id)
      k.castSucc k.succ (infix_adjacent_positions k) (isDescentStep_castSucc_succ S hk)
  have hsortedRun : ((run.reverse).map w).SortedLT := by
    apply hsorted run.reverse
    simp only [descentChains, List.mem_map]
    exact ⟨run, hrun, rfl⟩
  have hpair : ([w k.succ, w k.castSucc] : List (Fin (n + 2))).Pairwise (· < ·) :=
    hsortedRun.pairwise.sublist (hinfix.reverse.map w).sublist
  exact List.pairwise_pair.mp hpair

/-- Every prescribed descent makes the corresponding reversed runs strictly
increasing. -/
theorem isStrictChainSorted_descentChains_of_hasDescentsAt {n : ℕ}
    (S : Finset (Fin n)) (w : Fin (n + 1) → Fin (n + 2))
    (hdesc : HasDescentsAt S w) :
    IsStrictChainSorted (descentChains S) w := by
  intro l hl
  apply List.IsChain.sortedLT
  rw [List.isChain_map]
  apply (isChain_of_mem_descentChains S hl).imp
  intro i j hij
  simp only [isDescentStep, decide_eq_true_eq] at hij
  obtain ⟨k, hk, hj, hi⟩ := hij
  subst i
  subst j
  exact (hasDescentsAt_iff S w).mp hdesc k hk

/-- The selected descent inequalities are exactly strict sorting along the
reversed contiguous descent chains. -/
theorem hasDescentsAt_iff_isStrictChainSorted_descentChains {n : ℕ}
    (S : Finset (Fin n)) (w : Fin (n + 1) → Fin (n + 2)) :
    HasDescentsAt S w ↔ IsStrictChainSorted (descentChains S) w :=
  ⟨isStrictChainSorted_descentChains_of_hasDescentsAt S w,
    hasDescentsAt_of_isStrictChainSorted_descentChains S w⟩

end RealRooted.ParkingFunctions
