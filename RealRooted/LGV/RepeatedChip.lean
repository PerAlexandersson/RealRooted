/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.BrandenLeite.KernelRow
import RealRooted.LGV.ChipNetwork.Word
import RealRooted.LGV.PolyaFrequency
import RealRooted.PFPolynomial

/-!
# Pólya-frequency rows from repeated chip words

This is the concrete LeanLGV consumer for the repeated word
`G, K, G, K, ...`.  The path network is finite and minor-local; all path-family
cancellation remains in the standalone LeanLGV package.
-/

open Matrix Polynomial

namespace RealRooted
namespace LGV
namespace RepeatedChip

open ChipNetwork

noncomputable section

/-- Coefficient sequence of the repeated-chip kernel row. -/
def kernelSequence (G K : List (Chip ℝ N)) (q : ℕ) : ℝ :=
  (wordMatrix G * (wordMatrix K * wordMatrix G) ^ q) (Fin.last N) 0

/-- A bound for every row and column selected by a strict Toeplitz minor. -/
def minorBound {n : ℕ} (I : StrictToeplitzMinorIndex n) : ℕ :=
  max (Finset.univ.sup I.sourceRow) (Finset.univ.sup I.sinkColumn)

theorem sourceRow_le_minorBound {n : ℕ} (I : StrictToeplitzMinorIndex n)
    (i : Fin n) : I.sourceRow i ≤ minorBound I := by
  exact (Finset.le_sup (f := I.sourceRow) (Finset.mem_univ i)).trans
    (Nat.le_max_left _ _)

theorem sinkColumn_le_minorBound {n : ℕ} (I : StrictToeplitzMinorIndex n)
    (i : Fin n) : I.sinkColumn i ≤ minorBound I := by
  exact (Finset.le_sup (f := I.sinkColumn) (Finset.mem_univ i)).trans
    (Nat.le_max_right _ _)

/-- Source vertices for a strict Toeplitz minor.  Larger row indices start
earlier in the repeated strip. -/
def minorSource (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i : Fin n) :
    Vertex (repeatedStrip G K (minorBound I)).length N := by
  let R := minorBound I
  let L := G.length + K.length
  let s := (R - I.sourceRow i) * L
  refine (⟨s, Nat.lt_succ_of_le ?_⟩, Fin.last N)
  rw [length_repeatedStrip]
  have hmul := Nat.mul_le_mul_right L (Nat.sub_le R (I.sourceRow i))
  dsimp only [s, L, R]
  lia

/-- Sink vertices for a strict Toeplitz minor. -/
def minorSink (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i : Fin n) :
    Vertex (repeatedStrip G K (minorBound I)).length N := by
  let R := minorBound I
  let L := G.length + K.length
  let s := (R - I.sinkColumn i) * L + G.length
  refine (⟨s, Nat.lt_succ_of_le ?_⟩, 0)
  rw [length_repeatedStrip]
  have hmul := Nat.mul_le_mul_right L (Nat.sub_le R (I.sinkColumn i))
  dsimp only [s, L, R]
  lia

/-- The finite ranked network used for one strict Toeplitz minor. -/
def minorRankedNetwork (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) :=
  let word := repeatedStrip G K (minorBound I)
  rankedNetwork (wordDiagonal word) (wordSubdiagonal word)
    (minorSource G K I) (minorSink G K I)

/-- The finite path network underlying `minorRankedNetwork`. -/
def minorNetwork (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) :
    _root_.LGV.FinitePathNetwork ℝ (Fin n) :=
  (minorRankedNetwork G K I).toFinitePathNetwork

@[simp]
theorem stage_minorSource (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i : Fin n) :
    stage (minorSource G K I i) =
      (minorBound I - I.sourceRow i) * (G.length + K.length) :=
  rfl

@[simp]
theorem level_minorSource (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i : Fin n) :
    level (minorSource G K I i) = N := by
  simp [minorSource, level]

@[simp]
theorem stage_minorSink (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i : Fin n) :
    stage (minorSink G K I i) =
      (minorBound I - I.sinkColumn i) * (G.length + K.length) + G.length :=
  rfl

@[simp]
theorem level_minorSink (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i : Fin n) :
    level (minorSink G K I i) = 0 := by
  simp [minorSink, level]

/-- A strictly lower chip product cannot be represented by the empty word. -/
theorem kernelWord_length_pos (K : List (Chip ℝ N))
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0) :
    0 < K.length := by
  by_contra h
  have hnil : K = [] := List.eq_nil_of_length_eq_zero (by lia)
  have hdiag := hKstrict (0 : Fin (N + 1)) 0 (le_refl 0)
  simp [hnil] at hdiag

theorem minorNetwork_matrix_apply (G K : List (Chip ℝ N)) {n : ℕ}
    (I : StrictToeplitzMinorIndex n) (i j : Fin n) :
    (minorNetwork G K I).matrix i j =
      pathWeightSum
        (wordDiagonal (repeatedStrip G K (minorBound I)))
        (wordSubdiagonal (repeatedStrip G K (minorBound I)))
        (minorSource G K I i).1 (minorSink G K I j).1
        (minorSource G K I i).2 (minorSink G K I j).2 := by
  rfl

theorem minorSink_stage_eq_source_add (G K : List (Chip ℝ N))
    {n : ℕ} (I : StrictToeplitzMinorIndex n) (i j : Fin n)
    (hji : I.sinkColumn j ≤ I.sourceRow i) :
    stage (minorSink G K I j) = stage (minorSource G K I i) +
      ((I.sourceRow i - I.sinkColumn j) * (G.length + K.length) +
        G.length) := by
  rw [stage_minorSink, stage_minorSource]
  have hrow := sourceRow_le_minorBound I i
  have hsplit :
      minorBound I - I.sinkColumn j =
        (minorBound I - I.sourceRow i) +
          (I.sourceRow i - I.sinkColumn j) := by
    lia
  rw [hsplit, Nat.add_mul]
  lia

theorem minorSink_stage_lt_source (G K : List (Chip ℝ N))
    {n : ℕ} (I : StrictToeplitzMinorIndex n) (i j : Fin n)
    (hword : 0 < K.length) (hij : I.sourceRow i < I.sinkColumn j) :
    stage (minorSink G K I j) < stage (minorSource G K I i) := by
  rw [stage_minorSink, stage_minorSource]
  let L := G.length + K.length
  have hcol := sinkColumn_le_minorBound I j
  have hrow := sourceRow_le_minorBound I i
  have hstep : minorBound I - I.sinkColumn j + 1 ≤
      minorBound I - I.sourceRow i := by
    lia
  have hmul := Nat.mul_le_mul_right L hstep
  have hGL : G.length < L := by
    dsimp only [L]
    lia
  dsimp only [L] at hmul hGL ⊢
  rw [Nat.add_mul] at hmul
  lia

theorem minorSource_stage_anti (G K : List (Chip ℝ N))
    {n : ℕ} (I : StrictToeplitzMinorIndex n) (i j : Fin n)
    (hij : I.sourceRow i ≤ I.sourceRow j) :
    stage (minorSource G K I j) ≤ stage (minorSource G K I i) := by
  rw [stage_minorSource, stage_minorSource]
  have hmul := Nat.mul_le_mul_right (G.length + K.length)
    (Nat.sub_le_sub_left hij (minorBound I))
  exact hmul

theorem minorSink_stage_anti (G K : List (Chip ℝ N))
    {n : ℕ} (I : StrictToeplitzMinorIndex n) (i j : Fin n)
    (hij : I.sinkColumn i ≤ I.sinkColumn j) :
    stage (minorSink G K I j) ≤ stage (minorSink G K I i) := by
  rw [stage_minorSink, stage_minorSink]
  have hmul := Nat.mul_le_mul_right (G.length + K.length)
    (Nat.sub_le_sub_left hij (minorBound I))
  lia

/-- The path matrix of the minor-local repeated strip is the requested strict
Toeplitz submatrix. -/
theorem minorNetwork_matrix_eq_toeplitzSubmatrix
    (G K : List (Chip ℝ N))
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0)
    {n : ℕ} (I : StrictToeplitzMinorIndex n) :
    (minorNetwork G K I).matrix = I.toeplitzSubmatrix (kernelSequence G K) := by
  ext i j
  rw [minorNetwork_matrix_apply]
  change pathWeightSum
      (wordDiagonal (repeatedStrip G K (minorBound I)))
      (wordSubdiagonal (repeatedStrip G K (minorBound I)))
      (minorSource G K I i).1 (minorSink G K I j).1
      (minorSource G K I i).2 (minorSink G K I j).2 =
    if I.sinkColumn j ≤ I.sourceRow i then
      kernelSequence G K (I.sourceRow i - I.sinkColumn j) else 0
  by_cases hji : I.sinkColumn j ≤ I.sourceRow i
  · rw [ite_eq_left hji]
    rw [pathWeightSum_word_eq_wordMatrix_take_drop
      (repeatedStrip G K (minorBound I)) _ _ _ _ _
      (minorSink_stage_eq_source_add G K I i j hji)]
    rw [show (minorSource G K I i).1.val =
        (minorBound I - I.sourceRow i) * (G.length + K.length) from
          stage_minorSource G K I i,
      show (minorSource G K I i).2 = Fin.last N by
        apply Fin.ext
        exact level_minorSource G K I i,
      show (minorSink G K I j).2 = 0 by
        apply Fin.ext
        exact level_minorSink G K I j]
    rw [wordMatrix_repeatedStrip_slice G K (sourceRow_le_minorBound I i)]
    rfl
  · rw [ite_eq_right hji]
    rw [pathWeightSum_eq_zero_of_stage_lt]
    exact minorSink_stage_lt_source G K I i j
      (kernelWord_length_pos K hKstrict) (lt_of_not_ge hji)

/-- Oppositely ordered endpoint pairs in a repeated strip must meet. -/
theorem minorNetwork_twoPathObstruction
    (G K : List (Chip ℝ N)) {n : ℕ} (I : StrictToeplitzMinorIndex n) :
    _root_.LGV.FinitePathNetwork.HasTwoPathObstruction
      (minorNetwork G K I)
      (fun p q ↦ _root_.LGV.RankedQuiverNetwork.VertexDisjoint p q) := by
  intro s₁ t₁ s₂ t₂ p q hs ht
  apply not_vertexDisjoint_of_nested_top_bottom p q
  · exact minorSource_stage_anti G K I s₁ s₂
      (I.sourceRow_strictMono hs).le
  · exact minorSink_stage_anti G K I t₂ t₁
      (I.sinkColumn_strictMono ht).le
  · exact level_minorSource G K I s₁
  · exact level_minorSink G K I t₁

/-- The standalone LeanLGV first-collision engine supplies the ordered
cancellation certificate for each repeated-strip minor. -/
def minorNetwork_certificate
    (G K : List (Chip ℝ N)) {n : ℕ} (I : StrictToeplitzMinorIndex n) :
    _root_.LGV.FinitePathNetwork.OrderedCancellationCertificate
      (minorNetwork G K I) :=
  (minorRankedNetwork G K I).orderedCancellationCertificate
    (minorNetwork_twoPathObstruction G K I)

/-- Nonnegative input chips give nonnegative weights to every path in each
minor-local repeated strip. -/
theorem minorNetwork_pathWeight_nonneg
    (G K : List (Chip ℝ N))
    (hG : ∀ c ∈ G, c.IsNonnegative)
    (hK : ∀ c ∈ K, c.IsNonnegative)
    {n : ℕ} (I : StrictToeplitzMinorIndex n) {i j : Fin n}
    (p : (minorNetwork G K I).Path i j) :
    0 ≤ (minorNetwork G K I).weight p := by
  let word := repeatedStrip G K (minorBound I)
  have hword : ∀ c ∈ word, c.IsNonnegative := by
    intro c hc
    exact (mem_repeatedStrip G K (minorBound I) hc).elim (hG c) (hK c)
  exact rankedNetwork_pathWeight_nonneg
    (wordDiagonal word) (wordSubdiagonal word)
    (minorSource G K I) (minorSink G K I)
    (wordDiagonal_nonneg word hword)
    (wordSubdiagonal_nonneg word hword) p

/-- Nonnegative lower-bidiagonal `G` chips and a strictly lower product `K`
produce a Pólya-frequency coefficient sequence. -/
theorem kernelSequence_isPolyaFreqSeq
    (G K : List (Chip ℝ N))
    (hG : ∀ c ∈ G, c.IsNonnegative)
    (hK : ∀ c ∈ K, c.IsNonnegative)
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0) :
    IsPolyaFreqSeq (kernelSequence G K) := by
  apply isPolyaFreqSeq_of_minorOrderedCertificates
    (network := fun I ↦ minorNetwork G K I)
  · exact minorNetwork_matrix_eq_toeplitzSubmatrix G K hKstrict
  · exact minorNetwork_certificate G K
  · exact minorNetwork_pathWeight_nonneg G K hG hK

/-- The repeated-chip sequence vanishes above the ambient top level. -/
theorem kernelSequence_eq_zero_of_top_lt
    (G K : List (Chip ℝ N))
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0)
    {q : ℕ} (hNq : N < q) :
    kernelSequence G K q = 0 := by
  apply Matrix.mul_pow_apply_eq_zero_of_lt_add_of_lower_strictLower
    (wordMatrix G) (wordMatrix K * wordMatrix G)
    (fun _ _ hij ↦ wordMatrix_apply_eq_zero_of_lt G hij)
  · intro i j hij
    exact Matrix.mul_apply_eq_zero_of_le_of_strictLower_lower
      (wordMatrix K) (wordMatrix G) hKstrict
      (fun _ _ hab ↦ wordMatrix_apply_eq_zero_of_lt G hab) hij
  · simpa [kernelSequence] using hNq

/-- If each pass through `K` drops at least `r` levels, the `q`th coefficient
vanishes once `q * r` exceeds the ambient top level. -/
theorem kernelSequence_eq_zero_of_mul_drop
    (G K : List (Chip ℝ N)) {r q : ℕ}
    (hKdrop : ∀ i j, i.val < j.val + r → wordMatrix K i j = 0)
    (hNqr : N < q * r) :
    kernelSequence G K q = 0 := by
  apply Matrix.mul_pow_apply_eq_zero_of_lt_add_mul_of_lower_drop
    (wordMatrix G) (wordMatrix K * wordMatrix G)
    (fun _ _ hij ↦ wordMatrix_apply_eq_zero_of_lt G hij)
  · intro i j hij
    exact Matrix.mul_apply_eq_zero_of_lt_add_of_drop_lower
      (wordMatrix K) (wordMatrix G) hKdrop
      (fun _ _ hab ↦ wordMatrix_apply_eq_zero_of_lt G hab) hij
  · simpa [kernelSequence] using hNqr

/-- The finite kernel-row polynomial has exactly the repeated-chip coefficient
sequence, including beyond its defining finite range. -/
theorem coeff_kernelRow_eq_kernelSequence
    (G K : List (Chip ℝ N))
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0)
    (q : ℕ) :
    (BrandenLeite.kernelRow (wordMatrix G) (wordMatrix K) (Fin.last N)).coeff q =
      kernelSequence G K q := by
  rw [BrandenLeite.coeff_kernelRow]
  by_cases hq : q < N + 1
  · rw [ite_eq_left hq]
    rfl
  · rw [ite_eq_right hq, kernelSequence_eq_zero_of_top_lt G K hKstrict]
    lia

/-- The top kernel-row polynomial of a nonnegative repeated-chip model is PF. -/
theorem kernelRow_isPFPolynomial
    (G K : List (Chip ℝ N))
    (hG : ∀ c ∈ G, c.IsNonnegative)
    (hK : ∀ c ∈ K, c.IsNonnegative)
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0) :
    IsPFPolynomial
      (BrandenLeite.kernelRow (wordMatrix G) (wordMatrix K) (Fin.last N)) := by
  apply IsPFPolynomial.of_polyaFreqSeq
  simpa only [coeff_kernelRow_eq_kernelSequence G K hKstrict] using
    kernelSequence_isPolyaFreqSeq G K hG hK hKstrict

/-- The repeated-chip proof also records the sharp top-row degree bound. -/
theorem natDegree_kernelRow_le_top
    (G K : List (Chip ℝ N))
    (hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0) :
    (BrandenLeite.kernelRow (wordMatrix G) (wordMatrix K) (Fin.last N)).natDegree ≤ N := by
  simpa using BrandenLeite.natDegree_kernelRow_le_row
    (wordMatrix G) (wordMatrix K)
    (fun _ _ hij ↦ wordMatrix_apply_eq_zero_of_lt G hij) hKstrict (Fin.last N)

/-- A mandatory drop of `r > 0` on every `K` pass improves the top-row degree
bound from `N` to `N / r`. -/
theorem natDegree_kernelRow_le_div
    (G K : List (Chip ℝ N)) {r : ℕ} (hr : 0 < r)
    (hKdrop : ∀ i j, i.val < j.val + r → wordMatrix K i j = 0) :
    (BrandenLeite.kernelRow (wordMatrix G) (wordMatrix K) (Fin.last N)).natDegree ≤
      N / r := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro q hq
  have hKstrict : ∀ i j, i.val ≤ j.val → wordMatrix K i j = 0 := by
    intro i j hij
    apply hKdrop
    lia
  rw [coeff_kernelRow_eq_kernelSequence G K hKstrict]
  apply kernelSequence_eq_zero_of_mul_drop G K hKdrop
  exact (Nat.div_lt_iff_lt_mul hr).mp hq

section RodTilingRegression

/-- The two-level background chip for the smallest monomer/rod model. -/
def monomerBackgroundChip (b : ℝ) : Chip ℝ 1 where
  diagonal := fun _ ↦ 1
  subdiagonal := fun _ ↦ b

/-- The mandatory one-level marked chip for the smallest monomer/rod model. -/
def markedMonomerRodChip (c : ℝ) : Chip ℝ 1 where
  diagonal := fun _ ↦ 0
  subdiagonal := fun _ ↦ c

/-- Small rod-tiling regression: a nonnegative monomer background followed by
a mandatory marked one-level drop gives a PF top-row polynomial. -/
theorem monomerRodKernelRow_one_isPFPolynomial
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    IsPFPolynomial
      (BrandenLeite.kernelRow
        (wordMatrix [monomerBackgroundChip b])
        (wordMatrix [markedMonomerRodChip c]) (Fin.last 1)) := by
  apply kernelRow_isPFPolynomial
  · intro chip hchip
    simp only [List.mem_singleton] at hchip
    subst chip
    exact ⟨fun _ ↦ by simp [monomerBackgroundChip],
      fun _ ↦ by simpa [monomerBackgroundChip] using hb⟩
  · intro chip hchip
    simp only [List.mem_singleton] at hchip
    subst chip
    exact ⟨fun _ ↦ by simp [markedMonomerRodChip],
      fun _ ↦ by simpa [markedMonomerRodChip] using hc⟩
  · intro i j hij
    rw [wordMatrix_singleton]
    by_cases hEq : i = j
    · subst j
      simp [Chip.matrix, markedMonomerRodChip]
    · have hsub : i.val ≠ j.val + 1 := by lia
      simp [Chip.matrix, hEq, hsub]

end RodTilingRegression

end

end RepeatedChip
end LGV
end RealRooted
