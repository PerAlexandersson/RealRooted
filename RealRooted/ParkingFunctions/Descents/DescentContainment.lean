import RealRooted.ParkingFunctions.Descents.CompositionBlocks
import RealRooted.ParkingFunctions.Descents.DescentChains
import Mathlib.Data.List.ChainOfFn

/-!
# Descent-containment content enumerators

This module packages the contiguous runs determined by prescribed descent
positions as a Mathlib `Composition`.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- With no prescribed descents, every position forms a singleton run. -/
@[simp]
theorem descentRuns_empty {n : ℕ} :
    descentRuns (∅ : Finset (Fin n)) =
      (List.ofFn (id : Fin (n + 1) → Fin (n + 1))).map fun i => [i] := by
  unfold descentRuns
  apply List.splitBy_eq_map_singleton_of_forall_eq_false
  intro i j
  simp [isDescentStep]

/-- With every descent prescribed, all positions form one run. -/
@[simp]
theorem descentRuns_univ {n : ℕ} :
    descentRuns (Finset.univ : Finset (Fin n)) =
      [List.ofFn (id : Fin (n + 1) → Fin (n + 1))] := by
  unfold descentRuns
  apply List.splitBy_of_isChain
  · simp
  · rw [List.isChain_ofFn]
    intro i hi
    simp only [id_eq]
    simp only [isDescentStep, decide_eq_true_eq, Finset.mem_univ,
      true_and]
    refine ⟨⟨i, by lia⟩, ?_, ?_⟩
    · apply Fin.ext
      rfl
    · apply Fin.ext
      rfl

/-- The composition of the word length formed by the lengths of its
contiguous prescribed-descent runs. -/
def descentRunComposition {n : ℕ} (S : Finset (Fin n)) :
    Composition (n + 1) where
  blocks := (descentRuns S).map List.length
  blocks_pos := by
    intro k hk
    rw [List.mem_map] at hk
    obtain ⟨run, hrun, rfl⟩ := hk
    apply Nat.pos_of_ne_zero
    intro hzero
    have hnil : run = [] := by simpa using hzero
    subst run
    exact nil_not_mem_descentRuns S hrun
  blocks_sum := by
    calc
      ((descentRuns S).map List.length).sum =
          (descentRuns S).flatten.length := by simp
      _ = (List.ofFn (id : Fin (n + 1) → Fin (n + 1))).length := by
        rw [flatten_descentRuns]
      _ = n + 1 := by simp

@[simp]
theorem descentRunComposition_blocks {n : ℕ} (S : Finset (Fin n)) :
    (descentRunComposition S).blocks =
      (descentRuns S).map List.length := rfl

@[simp]
theorem descentRunComposition_empty {n : ℕ} :
    descentRunComposition (∅ : Finset (Fin n)) =
      Composition.ones (n + 1) := by
  rw [Composition.eq_ones_iff]
  intro i hi
  rw [descentRunComposition_blocks, descentRuns_empty,
    List.map_map] at hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  rfl

@[simp]
theorem descentRunComposition_univ {n : ℕ} :
    descentRunComposition (Finset.univ : Finset (Fin n)) =
      Composition.single (n + 1) (Nat.succ_pos n) := by
  rw [Composition.eq_single_iff_length]
  change ((descentRuns (Finset.univ : Finset (Fin n))).map
    List.length).length = 1
  rw [descentRuns_univ]
  rfl

/-- Splitting the ordered positions along their canonical descent-run
composition recovers the descent runs literally. -/
theorem splitWrtComposition_descentRunComposition {n : ℕ}
    (S : Finset (Fin n)) :
    (List.ofFn (id : Fin (n + 1) → Fin (n + 1))).splitWrtComposition
        (descentRunComposition S) = descentRuns S := by
  rw [List.eq_iff_flatten_eq]
  constructor
  · simp only [List.splitWrtComposition]
    rw [List.flatten_splitWrtCompositionAux]
    · exact (flatten_descentRuns S).symm
    · simpa using (descentRunComposition S).blocks_sum
  · simp only [List.splitWrtComposition]
    rw [List.map_length_splitWrtCompositionAux]
    · rfl
    · simpa using (descentRunComposition S).blocks_sum.le

/-- Prescribing the descents in `S` is exactly strict decrease on every
canonical block of the descent-run composition. -/
theorem hasDescentsAt_iff_blockwiseStrict {n m : ℕ}
    (S : Finset (Fin n)) (w : Fin (n + 1) → Fin m) :
    HasDescentsAt S w ↔
      ∀ i : Fin (descentRunComposition S).length,
        StrictAnti (w ∘ (descentRunComposition S).embedding i) := by
  rw [hasDescentsAt_iff_forall_mem_descentRuns_sortedGT]
  constructor
  · intro h i
    rw [← List.sortedGT_ofFn_iff]
    have hi : i.val <
        ((List.ofFn (id : Fin (n + 1) → Fin (n + 1))).splitWrtComposition
          (descentRunComposition S)).length := by
      rw [List.length_splitWrtComposition]
      exact i.isLt
    have hrun := h _ (by
      rw [← splitWrtComposition_descentRunComposition S]
      exact List.getElem_mem hi)
    rw [getElem_splitWrtComposition_ofFn (descentRunComposition S) i] at hrun
    simpa only [List.map_ofFn] using hrun
  · intro h run hrun
    rw [← splitWrtComposition_descentRunComposition S] at hrun
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrun
    have hi' : i < (descentRunComposition S).length := by
      simpa only [List.length_splitWrtComposition] using hi
    let j : Fin (descentRunComposition S).length := ⟨i, hi'⟩
    have hj := List.sortedGT_ofFn_iff.mpr (h j)
    rw [← List.map_ofFn] at hj
    rw [getElem_splitWrtComposition_ofFn (descentRunComposition S) j]
    simpa only [j] using hj

/-- Words containing every descent in `S` are the blockwise strict words for
the canonical descent-run composition. -/
def descentContainingWordEquivBlockwiseStrict {n m : ℕ}
    (S : Finset (Fin n)) :
    {w : Fin (n + 1) → Fin m // HasDescentsAt S w} ≃
      BlockwiseStrictWord (descentRunComposition S) m :=
  Equiv.subtypeEquivRight fun w =>
    hasDescentsAt_iff_blockwiseStrict S w

/-- The universal multivariate content enumerator of words containing every
descent in `S`. -/
def hasDescentsAtContentEnumerator {n : ℕ}
    (S : Finset (Fin n)) (m : ℕ) : MvPolynomial (Fin m) ℤ :=
  by
    classical
    exact ∑ w : {w : Fin (n + 1) → Fin m // HasDescentsAt S w},
      MvPolynomial.monomial (wordExponent w.1) (1 : ℤ)

/-- The descent-containment content enumerator is the strict-block enumerator
of the canonical descent-run composition. -/
theorem hasDescentsAtContentEnumerator_eq_strictCompositionBlockEnumerator
    {n : ℕ} (S : Finset (Fin n)) (m : ℕ) :
    hasDescentsAtContentEnumerator S m =
      strictCompositionBlockEnumerator (descentRunComposition S) m := by
  classical
  unfold hasDescentsAtContentEnumerator strictCompositionBlockEnumerator
  apply Fintype.sum_equiv (descentContainingWordEquivBlockwiseStrict S)
  intro w
  rfl

/-- The universal content enumerator for prescribed descents is a product of
elementary symmetric polynomials indexed by the descent-run lengths. -/
theorem hasDescentsAtContentEnumerator_eq_prod_esymm {n : ℕ}
    (S : Finset (Fin n)) (m : ℕ) :
    hasDescentsAtContentEnumerator S m =
      ∏ i : Fin (descentRunComposition S).length,
        MvPolynomial.esymm (Fin m) ℤ
          ((descentRunComposition S).blocksFun i) := by
  rw [hasDescentsAtContentEnumerator_eq_strictCompositionBlockEnumerator,
    strictCompositionBlockEnumerator_eq_prod_esymm]

/-- The descent-containment content enumerator is invariant under alphabet
renaming. -/
theorem rename_hasDescentsAtContentEnumerator {n : ℕ}
    (S : Finset (Fin n)) (m : ℕ) (e : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (hasDescentsAtContentEnumerator S m) =
      hasDescentsAtContentEnumerator S m := by
  rw [hasDescentsAtContentEnumerator_eq_strictCompositionBlockEnumerator,
    rename_strictCompositionBlockEnumerator]

@[simp]
theorem hasDescentsAtContentEnumerator_empty (n m : ℕ) :
    hasDescentsAtContentEnumerator (∅ : Finset (Fin n)) m =
      (∑ a : Fin m, MvPolynomial.X a) ^ (n + 1) := by
  rw [hasDescentsAtContentEnumerator_eq_strictCompositionBlockEnumerator,
    descentRunComposition_empty, strictCompositionBlockEnumerator_ones]

@[simp]
theorem hasDescentsAtContentEnumerator_univ (n m : ℕ) :
    hasDescentsAtContentEnumerator (Finset.univ : Finset (Fin n)) m =
      MvPolynomial.esymm (Fin m) ℤ (n + 1) := by
  rw [hasDescentsAtContentEnumerator_eq_strictCompositionBlockEnumerator,
    descentRunComposition_univ, strictCompositionBlockEnumerator_single]

end

end RealRooted.ParkingFunctions
