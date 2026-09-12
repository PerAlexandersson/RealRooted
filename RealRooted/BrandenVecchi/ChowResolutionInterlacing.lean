import RealRooted.BrandenVecchi.ChowResolution
import RealRooted.BrandenVecchi.ChowRowTransform
import RealRooted.InterlacingConeBounds

/-!
# Reflection interlacing for resolved Chow rows

This file proves Bränden--Vecchi, Theorem 4.16.  An explicit nonnegative
resolution supplies a triangular family of Chow-deranged polynomials.  Its
rows are reflection-interlacing by induction from the generic Chow row
transform and the exact transformed resolution recurrence.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The Chow-deranged image of the complete `n`th resolving row. -/
def resolvedChowRow {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) : List ℝ[X] :=
  (List.range (n + 1)).map fun k =>
    resolvedChowDerangement resolution n k

@[simp]
theorem length_resolvedChowRow {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    (resolvedChowRow resolution n).length = n + 1 := by
  simp [resolvedChowRow]

private def weightedResolvedChowRow {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) : List ℝ[X] :=
  (List.range (n + 1)).map fun j =>
    C (resolution.lambda n j) * resolvedChowDerangement resolution n j

private theorem sum_map_range_eq_finset_sum (f : ℕ → ℝ[X]) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, sum_map_range_eq_finset_sum f n]
      simp

private theorem sum_map_range'_eq_finset_sum_Ico
    (f : ℕ → ℝ[X]) (k q : ℕ) :
    ((List.range' k (q - k)).map f).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [Finset.sum_Ico_eq_sum_range, List.range'_eq_map_range, List.map_map,
    sum_map_range_eq_finset_sum]
  simp [Function.comp_apply]

private theorem sum_drop_map_range_eq_finset_sum_Ico
    (f : ℕ → ℝ[X]) (k q : ℕ) :
    (((List.range q).map f).drop k).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [← List.map_drop]
  rw [show List.range q = List.range' 0 q from List.range_eq_range']
  rw [List.drop_range']
  simpa using sum_map_range'_eq_finset_sum_Ico f k q

private theorem weightedResolvedChowRow_sum
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    (weightedResolvedChowRow resolution n).sum =
      resolvedChowWeightSum resolution n := by
  rw [weightedResolvedChowRow, sum_map_range_eq_finset_sum]
  rfl

private theorem weightedResolvedChowRow_drop_sum
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n k : ℕ) :
    ((weightedResolvedChowRow resolution n).drop k).sum =
      ∑ j ∈ Finset.Ico k (n + 1),
        C (resolution.lambda n j) *
          resolvedChowDerangement resolution n j := by
  exact sum_drop_map_range_eq_finset_sum_Ico _ k (n + 1)

private theorem chowRowTransform_weightedResolvedChowRow
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    chowRowTransform n (weightedResolvedChowRow resolution n) =
      resolvedChowRow resolution (n + 1) := by
  apply List.ext_get
  · simp [resolvedChowRow, weightedResolvedChowRow]
  · intro k hkleft hkright
    have hk : k ≤ n + 1 := by
      simpa [resolvedChowRow] using hkright
    have hktransform : k < (weightedResolvedChowRow resolution n).length + 1 := by
      simpa [weightedResolvedChowRow] using Nat.lt_succ_of_le hk
    rw [getElem_chowRowTransform hktransform]
    rw [show (resolvedChowRow resolution (n + 1)).get ⟨k, hkright⟩ =
        resolvedChowDerangement resolution (n + 1) k by
      simp [resolvedChowRow]]
    rw [resolvedChowDerangement_succ resolution hk,
      weightedResolvedChowRow_sum,
      weightedResolvedChowRow_drop_sum resolution n k]

private theorem resolvedChowRow_zero
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) :
    resolvedChowRow resolution 0 = [1] := by
  simp [resolvedChowRow, resolvedChowDerangement_diagonal]

private theorem reflectionInterlacing_one :
    IsReflectionInterlacingSeq 0 [(1 : ℝ[X])] := by
  have hself : Prec0 (1 : ℝ[X]) 1 :=
    (prec_refl one_ne_zero Polynomial.Splits.one).toPrec0
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp_one : p = 1 := by simpa using hp
    subst p
    simp
  · have hclosure : reflectionClosure 0 [(1 : ℝ[X])] = [1, 1] := by
      simp [reflectionClosure]
    rw [hclosure]
    refine ⟨⟨isInterlacingSeq0_iff_pairwise.mpr ?_, ?_⟩, ?_⟩
    · simpa using hself
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hasNonnegCoeffs_one
      · exact hasNonnegCoeffs_one
    · intro p hp hp_ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨one_ne_zero, Polynomial.Splits.one⟩
      · exact ⟨one_ne_zero, Polynomial.Splits.one⟩

/-- Bränden--Vecchi, Theorem 4.16: every transformed resolving row is
reflection-interlacing at its natural degree bound. -/
theorem resolvedChowRow_reflectionInterlacing
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) :
    ∀ n : ℕ, IsReflectionInterlacingSeq n (resolvedChowRow resolution n)
  | 0 => by simpa [resolvedChowRow_zero] using reflectionInterlacing_one
  | n + 1 => by
      have ih := resolvedChowRow_reflectionInterlacing resolution n
      have hscale : List.Forall₂ IsNonnegScalarMultiple
          (resolvedChowRow resolution n)
          (weightedResolvedChowRow resolution n) := by
        rw [resolvedChowRow, weightedResolvedChowRow,
          List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr fun j hj =>
          IsNonnegScalarMultiple.C_mul _
            (resolution.lambda_nonneg n j (by simpa using hj))
      have hweighted := ih.nonnegScalarMultiples hscale
      rw [← chowRowTransform_weightedResolvedChowRow resolution n]
      exact hweighted.chowRowTransform

/-- A nonnegative linear combination of one transformed resolving row. -/
def resolvedChowCombination {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ)
    (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C (a j) * resolvedChowDerangement resolution n j

/-- The corresponding nonnegative combination in the original resolving
row, before applying the Chow-deranged basis transform. -/
def resolvingRowCombination {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ)
    (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C (a j) * resolution.polynomial n j

/-- Applying the Chow-deranged transform to a resolving-row combination is
the same as combining the transformed row. -/
@[simp]
theorem chowDerangedTransform_resolvingRowCombination
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ)
    (a : ℕ → ℝ) :
    chowDerangedTransform A (resolvingRowCombination resolution n a) =
      resolvedChowCombination resolution n a := by
  simp [resolvingRowCombination, resolvedChowCombination,
    resolvedChowDerangement, map_sum]

private def scaledResolvedChowRow {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ)
    (a : ℕ → ℝ) : List ℝ[X] :=
  (List.range (n + 1)).map fun j =>
    C (a j) * resolvedChowDerangement resolution n j

private theorem scaledResolvedChowRow_sum
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ)
    (a : ℕ → ℝ) :
    (scaledResolvedChowRow resolution n a).sum =
      resolvedChowCombination resolution n a := by
  rw [scaledResolvedChowRow, sum_map_range_eq_finset_sum]
  rfl

private theorem resolvedChowRow_forall₂_scaled
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j) :
    List.Forall₂ IsNonnegScalarMultiple
      (resolvedChowRow resolution n)
      (scaledResolvedChowRow resolution n a) := by
  rw [resolvedChowRow, scaledResolvedChowRow,
    List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun j hj =>
    IsNonnegScalarMultiple.C_mul _ (ha j (by simpa using hj))

/-- Every member of a transformed resolving row has nonnegative
coefficients. -/
theorem resolvedChowDerangement_nonnegCoeffs
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n k : ℕ} (hk : k ≤ n) :
    HasNonnegCoeffs (resolvedChowDerangement resolution n k) := by
  have hrow := resolvedChowRow_reflectionInterlacing resolution n
  have hmem : resolvedChowDerangement resolution n k ∈
      resolvedChowRow resolution n :=
    List.mem_map.mpr ⟨k, by simpa using hk, rfl⟩
  exact hrow.closedSequence.nonnegCoeffs _ (by
    simp only [reflectionClosure, List.mem_append]
    exact Or.inl hmem)

/-- Every member of a transformed resolving row is zero or split. -/
theorem resolvedChowDerangement_eq_zero_or_splits
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n k : ℕ} (hk : k ≤ n) :
    resolvedChowDerangement resolution n k = 0 ∨
      (resolvedChowDerangement resolution n k).Splits := by
  by_cases hzero : resolvedChowDerangement resolution n k = 0
  · exact Or.inl hzero
  · have hrow := resolvedChowRow_reflectionInterlacing resolution n
    have hmem : resolvedChowDerangement resolution n k ∈
        resolvedChowRow resolution n :=
      List.mem_map.mpr ⟨k, by simpa using hk, rfl⟩
    exact Or.inr <| hrow.closedSequence.splits (by
      simp only [reflectionClosure, List.mem_append]
      exact Or.inl hmem) hzero

/-- A nonnegative combination of one transformed resolving row is a
Pólya-frequency polynomial, with the zero polynomial allowed. -/
theorem resolvedChowCombination_isPF
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j) :
    IsPFPolynomial (resolvedChowCombination resolution n a) := by
  have hrow := resolvedChowRow_reflectionInterlacing resolution n
  have hscaled := hrow.nonnegScalarMultiples
    (resolvedChowRow_forall₂_scaled resolution ha)
  have hsingle : IsReflectionInterlacingSeq n
      [resolvedChowCombination resolution n a] := by
    have hcollapsed := IsReflectionInterlacingSeq.collapseBlock
      (left := []) (block := scaledResolvedChowRow resolution n a)
      (right := []) (by simpa using hscaled)
    simpa [scaledResolvedChowRow_sum] using hcollapsed
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hsingle.closedSequence.nonnegCoeffs _ (by
      simp [reflectionClosure])
  · by_cases hzero : resolvedChowCombination resolution n a = 0
    · exact Or.inl hzero
    · exact Or.inr <| hsingle.closedSequence.splits (by
        simp [reflectionClosure]) hzero

/-- The first and last transformed resolving polynomials bound every
nonnegative row combination in zero-aware proper position. -/
theorem resolvedChowCombination_endpoint_prec0
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j) :
    Prec0 (resolvedChowDerangement resolution n 0)
        (resolvedChowCombination resolution n a) ∧
      Prec0 (resolvedChowCombination resolution n a)
        (resolvedChowDerangement resolution n n) := by
  have hrow := resolvedChowRow_reflectionInterlacing resolution n
  have hdirect : IsInterlacingSeq0NonnegRealRooted
      (resolvedChowRow resolution n) :=
    hrow.closedSequence.sublist (by simp [reflectionClosure])
  have hmem : ∀ j, j ≤ n →
      resolvedChowDerangement resolution n j ∈
        resolvedChowRow resolution n := by
    intro j hj
    exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
  have hself : ∀ j, j ≤ n →
      Prec0 (resolvedChowDerangement resolution n j)
        (resolvedChowDerangement resolution n j) := by
    intro j hj
    by_cases hzero : resolvedChowDerangement resolution n j = 0
    · exact Or.inl hzero
    · exact (prec_refl hzero (hdirect.splits (hmem j hj) hzero)).toPrec0
  have hleft : ∀ j, j ≤ n →
      Prec0 (resolvedChowDerangement resolution n 0)
        (resolvedChowDerangement resolution n j) := by
    intro j hj
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hjpos
    · exact hself 0 (Nat.zero_le n)
    · let first : Fin (resolvedChowRow resolution n).length :=
        ⟨0, by simp⟩
      let current : Fin (resolvedChowRow resolution n).length :=
        ⟨j, by simpa using hj⟩
      simpa [first, current, resolvedChowRow] using
        hdirect.interlacingSeq0.prec0 (i := first) (j := current) hjpos
  have hright : ∀ j, j ≤ n →
      Prec0 (resolvedChowDerangement resolution n j)
        (resolvedChowDerangement resolution n n) := by
    intro j hj
    by_cases hEq : j = n
    · subst j
      exact hself n le_rfl
    · have hjlt : j < n := Nat.lt_of_le_of_ne hj hEq
      let current : Fin (resolvedChowRow resolution n).length :=
        ⟨j, by simpa using hj⟩
      let last : Fin (resolvedChowRow resolution n).length :=
        ⟨n, by simp⟩
      simpa [current, last, resolvedChowRow] using
        hdirect.interlacingSeq0.prec0 (i := current) (j := last) hjlt
  constructor
  · apply prec0_finsetSum_left_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_right_of_nonneg (hleft j hjn) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn)
        (hdirect.nonnegCoeffs _ (hmem j hjn))
  · apply prec0_finsetSum_right_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_left_of_nonneg (hright j hjn) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn)
        (hdirect.nonnegCoeffs _ (hmem j hjn))

/-- Strict endpoint form of Theorem 4.16.  All three nonvanishing hypotheses
are explicit because resolution weights may vanish. -/
theorem resolvedChowCombination_endpoint_prec_of_ne
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j)
    (hfirst : resolvedChowDerangement resolution n 0 ≠ 0)
    (hcombination : resolvedChowCombination resolution n a ≠ 0)
    (hlast : resolvedChowDerangement resolution n n ≠ 0) :
    Prec (resolvedChowDerangement resolution n 0)
        (resolvedChowCombination resolution n a) ∧
      Prec (resolvedChowCombination resolution n a)
        (resolvedChowDerangement resolution n n) := by
  have hprec := resolvedChowCombination_endpoint_prec0 resolution ha
  exact ⟨hprec.1.toPrec_of_ne hfirst hcombination,
    hprec.2.toPrec_of_ne hcombination hlast⟩

/-- Paper-shaped zero-aware endpoint statement for a nonnegative combination
of the original resolving row. -/
theorem chowPolynomial_resolvingRowCombination_endpoint_prec0
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j) :
    Prec0 (chowPolynomial A n)
        (chowDerangedTransform A
          (resolvingRowCombination resolution n a)) ∧
      Prec0
        (chowDerangedTransform A
          (resolvingRowCombination resolution n a))
        (chowDerangement A n) := by
  simpa using resolvedChowCombination_endpoint_prec0 resolution ha

/-- The Chow-deranged image of a nonnegative resolving-row combination is
zero or split, with nonnegative coefficients. -/
theorem chowDerangedTransform_resolvingRowCombination_isPF
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j) :
    IsPFPolynomial
      (chowDerangedTransform A
        (resolvingRowCombination resolution n a)) := by
  rw [chowDerangedTransform_resolvingRowCombination]
  exact resolvedChowCombination_isPF resolution ha

/-- Strict paper-shaped endpoint statement under explicit nonvanishing
hypotheses. -/
theorem chowPolynomial_resolvingRowCombination_endpoint_prec_of_ne
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) {n : ℕ}
    {a : ℕ → ℝ} (ha : ∀ j, j ≤ n → 0 ≤ a j)
    (hchow : chowPolynomial A n ≠ 0)
    (hcombination :
      chowDerangedTransform A
        (resolvingRowCombination resolution n a) ≠ 0)
    (hderangement : chowDerangement A n ≠ 0) :
    Prec (chowPolynomial A n)
        (chowDerangedTransform A
          (resolvingRowCombination resolution n a)) ∧
      Prec
        (chowDerangedTransform A
          (resolvingRowCombination resolution n a))
        (chowDerangement A n) := by
  have hprec :=
    chowPolynomial_resolvingRowCombination_endpoint_prec0 resolution ha
  exact ⟨hprec.1.toPrec_of_ne hchow hcombination,
    hprec.2.toPrec_of_ne hcombination hderangement⟩

end

end RealRooted.BrandenVecchi
