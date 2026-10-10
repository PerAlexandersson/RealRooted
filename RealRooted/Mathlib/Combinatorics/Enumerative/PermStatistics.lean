import RealRooted.Mathlib.Combinatorics.Enumerative.Pattern
import RealRooted.Mathlib.Combinatorics.Enumerative.Peak
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Statistics of finite permutations

For `σ : Equiv.Perm (Fin n)` we use the word `List.ofFn σ`, whose entries are
the `Fin n` values themselves.  The order on `Fin n` is the order used by all
statistics below, and positions remain zero-based.
-/

namespace Equiv.Perm

/-- The descent set of a permutation, read as the word `List.ofFn σ`. -/
def descentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (List.ofFn σ).descentSet

/-- The ascent set of a permutation. -/
def ascentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (List.ofFn σ).ascentSet

/-- The number of descents of a permutation. -/
def descentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.descentSet.card

/-- The number of ascents of a permutation. -/
def ascentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.ascentSet.card

/-- The major index of a permutation. -/
def majorIndex {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (List.ofFn σ).majorIndex

/-- The interior peak set of a permutation. -/
def peakSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (List.ofFn σ).peakSet

/-- The number of interior peaks of a permutation. -/
def peakCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.peakSet.card

/-- The left peak set of a permutation. -/
def leftPeakSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (List.ofFn σ).leftPeakSet

/-- The valley set of a permutation. -/
def valleySet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  (List.ofFn σ).valleySet

/-- The number of valleys of a permutation. -/
def valleyCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.valleySet.card

/-- The left peak count of a permutation. -/
def leftPeakCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.leftPeakSet.card

/-- The descent set of the inverse permutation. -/
def inverseDescentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  σ⁻¹.descentSet

/-- The word interpretation of permutation descents. -/
@[simp] theorem descentSet_eq_list (σ : Equiv.Perm (Fin n)) :
    σ.descentSet = (List.ofFn σ).descentSet := rfl

/-- The word interpretation of permutation ascents. -/
@[simp] theorem ascentSet_eq_list (σ : Equiv.Perm (Fin n)) :
    σ.ascentSet = (List.ofFn σ).ascentSet := rfl

/-- The number of descents is the cardinality of the word descent set. -/
@[simp] theorem descentCount_eq_list (σ : Equiv.Perm (Fin n)) :
    σ.descentCount = (List.ofFn σ).descentCount := rfl

/-- The number of ascents is the cardinality of the word ascent set. -/
@[simp] theorem ascentCount_eq_list (σ : Equiv.Perm (Fin n)) :
    σ.ascentCount = (List.ofFn σ).ascentCount := rfl

/-- Membership in the descent set of a permutation of `n + 1` letters: a position `i < n` with
`σ (i + 1) < σ i`. -/
theorem mem_descentSet {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} {m : ℕ} :
    m ∈ σ.descentSet ↔ ∃ i : Fin n, (i : ℕ) = m ∧ σ i.succ < σ i.castSucc := by
  rw [descentSet_eq_list, List.mem_descentSet]
  constructor
  · rintro ⟨h, hlt⟩
    have hm : m < n := by
      simp only [List.length_ofFn] at h
      lia
    let i : Fin n := ⟨m, hm⟩
    refine ⟨i, rfl, ?_⟩
    rw [List.getElem_ofFn, List.getElem_ofFn] at hlt
    exact hlt
  · rintro ⟨i, rfl, hlt⟩
    have hi : (i : ℕ) + 1 < (List.ofFn σ).length := by
      simp only [List.length_ofFn]
      lia
    refine ⟨hi, ?_⟩
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hlt

/-- Every descent position of a permutation of `n + 1` letters is below `n`. -/
theorem descentSet_subset_range {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    σ.descentSet ⊆ Finset.range n := by
  intro m hm
  obtain ⟨i, rfl, -⟩ := mem_descentSet.mp hm
  simp

/-- Membership in the peak set of a permutation: the position has a smaller neighbour on each
side. -/
theorem mem_peakSet {n : ℕ} {σ : Equiv.Perm (Fin n)} {j : Fin n} :
    (j : ℕ) ∈ σ.peakSet ↔
      ∃ i k : Fin n, i.val + 1 = j.val ∧ j.val + 1 = k.val ∧ σ i < σ j ∧ σ k < σ j := by
  change (j : ℕ) ∈ (List.ofFn σ).peakSet ↔ _
  rw [List.mem_peakSet]
  constructor
  · rintro ⟨hi, h, hleft, hright⟩
    have hjlt : j.val < n := j.isLt
    have hbound : j.val + 1 < n := by
      simpa only [List.length_ofFn] using h
    let i : Fin n := ⟨j.val - 1, by lia⟩
    let k : Fin n := ⟨j.val + 1, by lia⟩
    refine ⟨i, k, ?_, ?_, ?_, ?_⟩
    · dsimp [i]
      lia
    · dsimp [k]
    · rw [List.getElem_ofFn, List.getElem_ofFn] at hleft
      simpa using hleft
    · rw [List.getElem_ofFn, List.getElem_ofFn] at hright
      simpa using hright
  · rintro ⟨i, k, hij, hjk, hleft, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · lia
    · have hklt : k.val < n := k.isLt
      simpa only [List.length_ofFn] using (show j.val + 1 < n by lia)
    · constructor
      · rw [List.getElem_ofFn, List.getElem_ofFn]
        have hi_eq : i = ⟨j.val - 1, by lia⟩ := Fin.ext (by lia)
        rw [hi_eq] at hleft
        simpa using hleft
      · rw [List.getElem_ofFn, List.getElem_ofFn]
        have hk_eq : k = ⟨j.val + 1, by lia⟩ := Fin.ext (by lia)
        rw [hk_eq] at hright
        simpa using hright

private theorem ofFn_reverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    List.ofFn (reverse σ) = (List.ofFn σ).reverse := by
  apply List.ext_getElem
  · simp [reverse]
  · intro i hi₁ hi₂
    simp only [reverse, coe_trans, List.getElem_ofFn, Function.comp_apply, Fin.revPerm_apply,
      List.getElem_reverse, List.length_ofFn, EmbeddingLike.apply_eq_iff_eq]
    apply Fin.ext
    simp [Fin.rev, Nat.sub_sub, Nat.add_comm]

private theorem ofFn_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    List.ofFn (complement σ) = (List.ofFn σ).map Fin.rev := by
  have hrev : (Fin.revPerm : Fin n → Fin n) = Fin.rev := by
    funext i
    exact Fin.revPerm_apply i
  rw [complement]
  change List.ofFn (Fin.revPerm ∘ σ) = _
  rw [hrev]
  exact List.ofFn_comp' σ (Fin.rev : Fin n → Fin n)

/-- Reversal transforms permutation descents using the word reversal formula. -/
theorem descentSet_reverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (reverse σ).descentSet =
      σ.ascentSet.image (fun i => n - 2 - i) := by
  rw [descentSet, ofFn_reverse, List.descentSet_reverse]
  rw [ascentSet_eq_list]
  simp only [List.length_ofFn]

/-- Complement exchanges the descents and ascents of a permutation. -/
theorem descentSet_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (complement σ).descentSet = σ.ascentSet := by
  rw [descentSet, ofFn_complement]
  exact List.descentSet_map_strictAnti _ Fin.rev Fin.rev_strictAnti

/-- Complement exchanges the ascents and descents of a permutation. -/
theorem ascentSet_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (complement σ).ascentSet = σ.descentSet := by
  rw [ascentSet, ofFn_complement]
  exact List.ascentSet_map_strictAnti _ Fin.rev Fin.rev_strictAnti

/-- Reversal transforms permutation peaks using the word reversal formula. -/
theorem peakSet_reverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (reverse σ).peakSet = σ.peakSet.image (fun i => n - 1 - i) := by
  rw [peakSet, ofFn_reverse, List.peakSet_reverse]
  change _ = (List.ofFn σ).peakSet.image (fun i => n - 1 - i)
  simp only [List.length_ofFn]

/-- Complement exchanges the peaks and valleys of a permutation. -/
theorem peakSet_complement {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (complement σ).peakSet = σ.valleySet := by
  rw [peakSet, valleySet, ofFn_complement]
  exact List.peakSet_map_strictAnti _ Fin.rev Fin.rev_strictAnti

/-- The descent and ascent numbers of a positive-size permutation sum to `n - 1`. -/
theorem descentCount_add_ascentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.descentCount + σ.ascentCount = n - 1 := by
  have hnodup : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  rw [descentCount_eq_list, ascentCount_eq_list]
  simpa only [List.length_ofFn] using
    (List.descentCount_add_ascentCount_of_nodup (List.ofFn σ) hnodup)

/-- The Eulerian descent distribution on permutations of `Fin 4`. -/
example :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ.descentCount = 0)).card = 1 := by
  decide

example :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ.descentCount = 1)).card = 11 := by
  decide

example :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ.descentCount = 2)).card = 11 := by
  decide

example :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ.descentCount = 3)).card = 1 := by
  decide

/-- The peak distribution on permutations of `Fin 4`. -/
example :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ.peakCount = 0)).card = 8 := by
  decide

example :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => σ.peakCount = 1)).card = 16 := by
  decide

end Equiv.Perm
