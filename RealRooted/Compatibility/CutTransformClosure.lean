import RealRooted.ChudnovskySeymour.Core
import RealRooted.Compatibility.CutTransform

/-!
# Sound generic closure for the finite P/Q cut transform

The initial ordered P/Q invariant does not preserve its cross clauses, as
shown in `CutTransformObstruction`.  This module records the coefficient and
same-colour conclusions that do hold for every ordered input family.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A family obtained by appending two finite positive, nonnegative,
pairwise-compatible blocks is fully compatible. -/
theorem familyCompatible_ofFn_append_of_pairwise
    {m n : ℕ} {P : Fin m → ℝ[X]} {Q : Fin n → ℝ[X]}
    (hP_rr : ∀ i, P i ≠ 0 ∧ (P i).Splits)
    (hQ_rr : ∀ i, Q i ≠ 0 ∧ (Q i).Splits)
    (hP_pos : ∀ i, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i, HasPosLeadingCoeff (Q i))
    (hP_nonneg : ∀ i, HasNonnegCoeffs (P i))
    (hQ_nonneg : ∀ i, HasNonnegCoeffs (Q i))
    (hPP : ∀ i j, Compatible (P i) (P j))
    (hPQ : ∀ i j, Compatible (P i) (Q j))
    (hQQ : ∀ i j, Compatible (Q i) (Q j)) :
    FamilyCompatible (List.ofFn P ++ List.ofFn Q) := by
  let fs := List.ofFn P ++ List.ofFn Q
  have hrr : ∀ p ∈ fs, p ≠ 0 ∧ p.Splits := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hP_rr i
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hQ_rr i
  have hpos : ∀ p ∈ fs, HasPosLeadingCoeff p := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hP_pos i
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hQ_pos i
  have hnonneg : ∀ p ∈ fs, HasNonnegCoeffs p := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hP_nonneg i
    · simp only [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hQ_nonneg i
  have hpair : PairwiseCompatible fs := by
    apply pairwiseCompatible_of_forall_mem
    intro p hp q hq
    rcases List.mem_append.mp hp with hp | hp <;>
      rcases List.mem_append.mp hq with hq | hq
    · simp only [List.mem_ofFn] at hp hq
      rcases hp with ⟨i, rfl⟩
      rcases hq with ⟨j, rfl⟩
      exact hPP i j
    · simp only [List.mem_ofFn] at hp hq
      rcases hp with ⟨i, rfl⟩
      rcases hq with ⟨j, rfl⟩
      exact hPQ i j
    · simp only [List.mem_ofFn] at hp hq
      rcases hp with ⟨i, rfl⟩
      rcases hq with ⟨j, rfl⟩
      exact (hPQ j i).comm
    · simp only [List.mem_ofFn] at hp hq
      rcases hp with ⟨i, rfl⟩
      rcases hq with ⟨j, rfl⟩
      exact hQQ i j
  exact
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      hrr hpos hnonneg).1 hpair

namespace OrderedCutCompatible

private theorem compatible_p_all {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (i j : Fin m) :
    Compatible (P i) (P j) := by
  rcases le_total i j with hij | hji
  · exact h.pp_forward hij
  · exact h.pp_reverse hji

private theorem compatible_q_all {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (i j : Fin m) :
    Compatible (Q i) (Q j) := by
  rcases le_total i j with hij | hji
  · exact h.qq_forward hij
  · exact h.qq_reverse hji

/-- The fixed unmarked atom family `P ++ Q` is fully compatible. -/
theorem familyCompatible_pq {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) :
    FamilyCompatible (List.ofFn P ++ List.ofFn Q) :=
  familyCompatible_ofFn_append_of_pairwise h.p_splits h.q_splits
    h.p_pos h.q_pos h.p_nonneg h.q_nonneg
    (compatible_p_all h) h.pq (compatible_q_all h)

/-- The fixed marked-P/unmarked-Q atom family `XP ++ Q` is fully compatible. -/
theorem familyCompatible_xp_q {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) :
    FamilyCompatible
      (List.ofFn (fun i => X * P i) ++ List.ofFn Q) :=
  familyCompatible_ofFn_append_of_pairwise
    (fun i => isRealRooted_X_mul_of_isRealRooted (h.p_splits i)) h.q_splits
    (fun i => (h.p_pos i).X_mul) h.q_pos
    (fun i => (h.p_nonneg i).X_mul) h.q_nonneg
    (fun i j => (compatible_p_all h i j).X_mul) h.xpq
    (compatible_q_all h)

end OrderedCutCompatible

/-- The 0/1 weighted list representing an unmarked cut output. -/
def cutTransformPWeights {m : ℕ} (P Q : Fin m → ℝ[X])
    (j : Fin m) : List (ℝ × ℝ[X]) :=
  List.ofFn (fun i => (if i ≤ j then 1 else 0, P i)) ++
    List.ofFn (fun i => (if j < i then 1 else 0, Q i))

/-- The 0/1 weighted list representing a marked cut output. -/
def cutTransformQWeights {m : ℕ} (P Q : Fin m → ℝ[X])
    (j : Fin m) : List (ℝ × ℝ[X]) :=
  List.ofFn (fun i => (if i ≤ j then 1 else 0, X * P i)) ++
    List.ofFn (fun i => (if j < i then 1 else 0, Q i))

theorem weightedSum_cutTransformPWeights {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    weightedSum (cutTransformPWeights P Q j) = cutTransformP P Q j := by
  rw [cutTransformPWeights, weightedSum_append, weightedSum_ofFn,
    weightedSum_ofFn]
  unfold cutTransformP cutPrefix cutStrictSuffix
  congr 1
  · apply Fintype.sum_congr
    intro i
    by_cases hij : i ≤ j <;> simp [hij]
  · apply Fintype.sum_congr
    intro i
    by_cases hji : j < i <;> simp [hji]

theorem weightedSum_cutTransformQWeights {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    weightedSum (cutTransformQWeights P Q j) = cutTransformQ P Q j := by
  rw [cutTransformQWeights, weightedSum_append, weightedSum_ofFn,
    weightedSum_ofFn]
  unfold cutTransformQ cutPrefix cutStrictSuffix
  rw [Finset.mul_sum]
  congr 1
  · apply Fintype.sum_congr
    intro i
    by_cases hij : i ≤ j <;> simp [hij]
  · apply Fintype.sum_congr
    intro i
    by_cases hji : j < i <;> simp [hji]

private theorem cutTransformPWeights_mem {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    ∀ ap ∈ cutTransformPWeights P Q j,
      ap.2 ∈ List.ofFn P ++ List.ofFn Q := by
  intro ap hap
  rcases List.mem_append.mp hap with hap | hap
  · simp only [List.mem_ofFn] at hap
    rcases hap with ⟨i, rfl⟩
    simp
  · simp only [List.mem_ofFn] at hap
    rcases hap with ⟨i, rfl⟩
    simp

private theorem cutTransformQWeights_mem {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    ∀ ap ∈ cutTransformQWeights P Q j,
      ap.2 ∈ List.ofFn (fun i => X * P i) ++ List.ofFn Q := by
  intro ap hap
  rcases List.mem_append.mp hap with hap | hap
  · simp only [List.mem_ofFn] at hap
    rcases hap with ⟨i, rfl⟩
    simp
  · simp only [List.mem_ofFn] at hap
    rcases hap with ⟨i, rfl⟩
    simp

private theorem cutTransformPWeights_nonneg {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    ∀ ap ∈ cutTransformPWeights P Q j, 0 ≤ ap.1 := by
  intro ap hap
  rcases List.mem_append.mp hap with hap | hap <;>
    simp only [List.mem_ofFn] at hap
  · rcases hap with ⟨i, rfl⟩
    split <;> norm_num
  · rcases hap with ⟨i, rfl⟩
    split <;> norm_num

private theorem cutTransformQWeights_nonneg {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    ∀ ap ∈ cutTransformQWeights P Q j, 0 ≤ ap.1 := by
  intro ap hap
  rcases List.mem_append.mp hap with hap | hap <;>
    simp only [List.mem_ofFn] at hap
  · rcases hap with ⟨i, rfl⟩
    split <;> norm_num
  · rcases hap with ⟨i, rfl⟩
    split <;> norm_num

namespace OrderedCutCompatible

/-- Any two unmarked cut outputs are compatible. -/
theorem compatible_cutTransformP {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (i j : Fin m) :
    Compatible (cutTransformP P Q i) (cutTransformP P Q j) := by
  rw [← weightedSum_cutTransformPWeights P Q i,
    ← weightedSum_cutTransformPWeights P Q j]
  exact h.familyCompatible_pq.compatible_weightedSum
    (cutTransformPWeights_mem P Q i) (cutTransformPWeights_mem P Q j)
    (cutTransformPWeights_nonneg P Q i)
    (cutTransformPWeights_nonneg P Q j)

/-- Any two marked cut outputs are compatible. -/
theorem compatible_cutTransformQ {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (i j : Fin m) :
    Compatible (cutTransformQ P Q i) (cutTransformQ P Q j) := by
  rw [← weightedSum_cutTransformQWeights P Q i,
    ← weightedSum_cutTransformQWeights P Q j]
  exact h.familyCompatible_xp_q.compatible_weightedSum
    (cutTransformQWeights_mem P Q i) (cutTransformQWeights_mem P Q j)
    (cutTransformQWeights_nonneg P Q i)
    (cutTransformQWeights_nonneg P Q j)

private theorem pWeights_polys_nonneg {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    ∀ ap ∈ cutTransformPWeights P Q j, HasNonnegCoeffs ap.2 := by
  intro ap hap
  have hmem := cutTransformPWeights_mem P Q j ap hap
  rcases List.mem_append.mp hmem with hp | hq
  · simp only [List.mem_ofFn] at hp
    rcases hp with ⟨i, hi⟩
    rw [← hi]
    exact h.p_nonneg i
  · simp only [List.mem_ofFn] at hq
    rcases hq with ⟨i, hi⟩
    rw [← hi]
    exact h.q_nonneg i

private theorem qWeights_polys_nonneg {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    ∀ ap ∈ cutTransformQWeights P Q j, HasNonnegCoeffs ap.2 := by
  intro ap hap
  have hmem := cutTransformQWeights_mem P Q j ap hap
  rcases List.mem_append.mp hmem with hp | hq
  · simp only [List.mem_ofFn] at hp
    rcases hp with ⟨i, hi⟩
    rw [← hi]
    exact (h.p_nonneg i).X_mul
  · simp only [List.mem_ofFn] at hq
    rcases hq with ⟨i, hi⟩
    rw [← hi]
    exact h.q_nonneg i

private theorem pWeights_polys_pos {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    ∀ ap ∈ cutTransformPWeights P Q j, HasPosLeadingCoeff ap.2 := by
  intro ap hap
  have hmem := cutTransformPWeights_mem P Q j ap hap
  rcases List.mem_append.mp hmem with hp | hq
  · simp only [List.mem_ofFn] at hp
    rcases hp with ⟨i, hi⟩
    rw [← hi]
    exact h.p_pos i
  · simp only [List.mem_ofFn] at hq
    rcases hq with ⟨i, hi⟩
    rw [← hi]
    exact h.q_pos i

private theorem qWeights_polys_pos {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    ∀ ap ∈ cutTransformQWeights P Q j, HasPosLeadingCoeff ap.2 := by
  intro ap hap
  have hmem := cutTransformQWeights_mem P Q j ap hap
  rcases List.mem_append.mp hmem with hp | hq
  · simp only [List.mem_ofFn] at hp
    rcases hp with ⟨i, hi⟩
    rw [← hi]
    exact (h.p_pos i).X_mul
  · simp only [List.mem_ofFn] at hq
    rcases hq with ⟨i, hi⟩
    rw [← hi]
    exact h.q_pos i

private theorem exists_pos_pWeight {m : ℕ} (P Q : Fin m → ℝ[X])
    (j : Fin m) :
    ∃ ap ∈ cutTransformPWeights P Q j, 0 < ap.1 := by
  refine ⟨(1, P j), ?_, by norm_num⟩
  apply List.mem_append_left
  simp only [List.mem_ofFn]
  exact ⟨j, by simp⟩

private theorem exists_pos_qWeight {m : ℕ} (P Q : Fin m → ℝ[X])
    (j : Fin m) :
    ∃ ap ∈ cutTransformQWeights P Q j, 0 < ap.1 := by
  refine ⟨(1, X * P j), ?_, by norm_num⟩
  apply List.mem_append_left
  simp only [List.mem_ofFn]
  exact ⟨j, by simp⟩

theorem cutTransformP_nonneg {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    HasNonnegCoeffs (cutTransformP P Q j) := by
  rw [← weightedSum_cutTransformPWeights]
  exact hasNonnegCoeffs_weightedSum _
    (cutTransformPWeights_nonneg P Q j) (pWeights_polys_nonneg h j)

theorem cutTransformQ_nonneg {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    HasNonnegCoeffs (cutTransformQ P Q j) := by
  rw [← weightedSum_cutTransformQWeights]
  exact hasNonnegCoeffs_weightedSum _
    (cutTransformQWeights_nonneg P Q j) (qWeights_polys_nonneg h j)

theorem cutTransformP_pos {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    HasPosLeadingCoeff (cutTransformP P Q j) := by
  rw [← weightedSum_cutTransformPWeights]
  exact hasPosLeadingCoeff_weightedSum _
    (cutTransformPWeights_nonneg P Q j) (pWeights_polys_pos h j)
    (exists_pos_pWeight P Q j)

theorem cutTransformQ_pos {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    HasPosLeadingCoeff (cutTransformQ P Q j) := by
  rw [← weightedSum_cutTransformQWeights]
  exact hasPosLeadingCoeff_weightedSum _
    (cutTransformQWeights_nonneg P Q j) (qWeights_polys_pos h j)
    (exists_pos_qWeight P Q j)

end OrderedCutCompatible

end RealRooted
