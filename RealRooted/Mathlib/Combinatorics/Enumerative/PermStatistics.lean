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
