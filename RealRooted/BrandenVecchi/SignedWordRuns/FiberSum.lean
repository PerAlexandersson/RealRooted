import RealRooted.BrandenVecchi.SignedWordRuns.Statistics
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Finite fibers of signed-word run compression

This file sums the checked runwise signed-word formula over the finite fiber of
a fixed signed Smirnov skeleton.  The length variable is a formal power-series
variable, while the descent/collision statistic remains the polynomial
variable.  Thus every coefficient identity below is finite.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-! ## One-run formal power series -/

/-- A positive skeleton letter has forced run length one. -/
def positiveRunSeries {R : Type*} [CommSemiring R] (weight : R) :
    PowerSeries R[X] :=
  PowerSeries.C (C weight) * PowerSeries.X

/-- A negative skeleton letter may be repeated.  A run of length `n + 1`
contributes `weight ^ (n + 1) * (1 + t) ^ n`. -/
def negativeRunSeries {R : Type*} [CommSemiring R] (weight : R) :
    PowerSeries R[X] :=
  PowerSeries.C (C weight) * PowerSeries.X *
    PowerSeries.rescale (C weight * (1 + X)) (PowerSeries.mk 1)

@[simp]
theorem coeff_positiveRunSeries {R : Type*} [CommSemiring R]
    (weight : R) (n : ℕ) :
  PowerSeries.coeff n (positiveRunSeries weight) =
      if n = 1 then C weight else 0 := by
  simp [positiveRunSeries, PowerSeries.coeff_X]

@[simp]
theorem coeff_negativeRunSeries_zero {R : Type*} [CommSemiring R]
    (weight : R) :
    PowerSeries.coeff 0 (negativeRunSeries weight) = 0 := by
  simp [negativeRunSeries]

@[simp]
theorem coeff_negativeRunSeries_succ {R : Type*} [CommSemiring R]
    (weight : R) (n : ℕ) :
    PowerSeries.coeff (n + 1) (negativeRunSeries weight) =
      C (weight ^ (n + 1)) * (1 + X) ^ n := by
  rw [negativeRunSeries, mul_assoc, PowerSeries.coeff_C_mul]
  rw [show PowerSeries.coeff (n + 1)
      (PowerSeries.X * PowerSeries.rescale (C weight * (1 + X))
        (PowerSeries.mk 1)) =
      PowerSeries.coeff n
        (PowerSeries.rescale (C weight * (1 + X))
          (PowerSeries.mk 1)) by
    simp]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
    Pi.one_apply, mul_one]
  simp [mul_pow, pow_succ']
  ac_rfl

/-- The negative-run series is exactly
`weight z / (1 - weight (1 + t) z)` as a formal identity. -/
theorem negativeRunSeries_mul_one_sub {R : Type*} [CommRing R]
    (weight : R) :
    negativeRunSeries weight *
        (1 - PowerSeries.C (C weight * (1 + X)) * PowerSeries.X) =
      PowerSeries.C (C weight) * PowerSeries.X := by
  have h := congrArg
    (PowerSeries.rescale (C weight * (1 + X)))
    (PowerSeries.mk_one_mul_one_sub_eq_one R[X])
  rw [negativeRunSeries, mul_assoc, mul_assoc]
  rw [show PowerSeries.rescale (C weight * (1 + X))
          (PowerSeries.mk 1) *
          (1 - PowerSeries.C (C weight * (1 + X)) * PowerSeries.X) = 1 by
    simpa [map_sub, PowerSeries.rescale_X] using h]
  simp

/-- The one-run factor selected by the sign of a skeleton letter. -/
def signedRunSeries {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (letter : SignedLetter q p) :
    PowerSeries R[X] := by
  classical
  exact if letter.IsNegative then negativeRunSeries (weight letter)
    else positiveRunSeries (weight letter)

@[simp]
theorem coeff_signedRunSeries_of_isNegative
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) {letter : SignedLetter q p}
    (hnegative : letter.IsNegative) (n : ℕ) :
    PowerSeries.coeff (n + 1) (signedRunSeries weight letter) =
      C (weight letter ^ (n + 1)) * (1 + X) ^ n := by
  classical
  simp [signedRunSeries, hnegative]

@[simp]
theorem coeff_signedRunSeries_of_isPositive
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) {letter : SignedLetter q p}
    (hpositive : letter.IsPositive) (n : ℕ) :
    PowerSeries.coeff n (signedRunSeries weight letter) =
      if n = 1 then C (weight letter) else 0 := by
  classical
  have hnotnegative : ¬letter.IsNegative := by
    intro hnegative
    exact letter.not_isNegative_and_isPositive ⟨hnegative, hpositive⟩
  simp [signedRunSeries, hnotnegative]

@[simp]
theorem coeff_signedRunSeries_zero
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (letter : SignedLetter q p) :
    PowerSeries.coeff 0 (signedRunSeries weight letter) = 0 := by
  classical
  rcases letter.isNegative_or_isPositive with hnegative | hpositive
  · simp [signedRunSeries, hnegative]
  · simp [coeff_signedRunSeries_of_isPositive weight hpositive]

/-! ## Finite length-assignment fibers -/

/-- A length assignment is admissible for a signed skeleton when every run is
nonempty and positive letters have run length one. -/
def IsSignedRunLengthAssignment {q p : ℕ}
    (skeleton : List (SignedLetter q p))
    (lengths : Fin skeleton.length →₀ ℕ) : Prop :=
  ∀ i, 0 < lengths i ∧
    ((skeleton.get i).IsPositive → lengths i = 1)

/-- The finite fiber of admissible run lengths of total length `n` over a
fixed skeleton. -/
def signedRunLengthFiber {q p : ℕ}
    (skeleton : List (SignedLetter q p)) (n : ℕ) :
    Finset (Fin skeleton.length →₀ ℕ) := by
  classical
  exact (Finset.univ.finsuppAntidiag n).filter
    (IsSignedRunLengthAssignment skeleton)

@[simp]
theorem mem_signedRunLengthFiber_iff {q p : ℕ}
    {skeleton : List (SignedLetter q p)} {n : ℕ}
    {lengths : Fin skeleton.length →₀ ℕ} :
    lengths ∈ signedRunLengthFiber skeleton n ↔
      (∑ i : Fin skeleton.length, lengths i) = n ∧
        IsSignedRunLengthAssignment skeleton lengths := by
  classical
  simp [signedRunLengthFiber, Finset.mem_finsuppAntidiag]

/-- The formal product of the independent run factors along a fixed signed
Smirnov skeleton.  The definition itself does not require the Smirnov
condition; that condition enters when this product is identified with a
compression fiber. -/
def signedSkeletonRunSeries {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : List (SignedLetter q p)) : PowerSeries R[X] :=
  ∏ i : Fin skeleton.length, signedRunSeries weight (skeleton.get i)

/-- The explicit runwise contribution of a length assignment. -/
def signedRunLengthSummand {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : List (SignedLetter q p))
    (lengths : Fin skeleton.length →₀ ℕ) : R[X] :=
  ∏ i : Fin skeleton.length,
    C (weight (skeleton.get i) ^ lengths i) *
      (1 + X) ^ (lengths i - 1)

/-- On an admissible assignment, a selected run factor has exactly the
runwise weight and collision contribution. -/
theorem coeff_signedRunSeries_of_assignment
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    {skeleton : List (SignedLetter q p)}
    {lengths : Fin skeleton.length →₀ ℕ}
    (hlengths : IsSignedRunLengthAssignment skeleton lengths)
    (i : Fin skeleton.length) :
    PowerSeries.coeff (lengths i)
        (signedRunSeries weight (skeleton.get i)) =
      C (weight (skeleton.get i) ^ lengths i) *
        (1 + X) ^ (lengths i - 1) := by
  rcases (skeleton.get i).isNegative_or_isPositive with
    hnegative | hpositive
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' (hlengths i).1
    rw [hn]
    exact coeff_signedRunSeries_of_isNegative weight hnegative n
  · have hlength : lengths i = 1 := (hlengths i).2 hpositive
    rw [hlength]
    simpa using
      (coeff_signedRunSeries_of_isPositive weight hpositive 1)

/-- If a length assignment is inadmissible, at least one selected run
coefficient vanishes. -/
theorem exists_coeff_signedRunSeries_eq_zero_of_not_assignment
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    {skeleton : List (SignedLetter q p)}
    {lengths : Fin skeleton.length →₀ ℕ}
    (hlengths : ¬IsSignedRunLengthAssignment skeleton lengths) :
    ∃ i : Fin skeleton.length,
      PowerSeries.coeff (lengths i)
        (signedRunSeries weight (skeleton.get i)) = 0 := by
  classical
  simp only [IsSignedRunLengthAssignment, not_forall,
    not_and_or] at hlengths
  obtain ⟨i, hnonpos | ⟨hpositive, hne⟩⟩ := hlengths
  · refine ⟨i, ?_⟩
    have hzero : lengths i = 0 := Nat.eq_zero_of_not_pos hnonpos
    simp [hzero]
  · refine ⟨i, ?_⟩
    rw [coeff_signedRunSeries_of_isPositive weight hpositive]
    simp [hne]

/-- A fixed skeleton's length-`n` coefficient is the finite sum over its
admissible run-length fiber. -/
theorem coeff_signedSkeletonRunSeries
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : List (SignedLetter q p)) (n : ℕ) :
    PowerSeries.coeff n (signedSkeletonRunSeries weight skeleton) =
      ∑ lengths ∈ signedRunLengthFiber skeleton n,
        signedRunLengthSummand weight skeleton lengths := by
  classical
  rw [signedSkeletonRunSeries, PowerSeries.coeff_prod]
  change (∑ lengths ∈ Finset.univ.finsuppAntidiag n,
      ∏ i : Fin skeleton.length,
        PowerSeries.coeff (lengths i)
          (signedRunSeries weight (skeleton.get i))) = _
  rw [signedRunLengthFiber]
  symm
  calc
    (∑ lengths ∈ (Finset.univ.finsuppAntidiag n).filter
          (IsSignedRunLengthAssignment skeleton),
        signedRunLengthSummand weight skeleton lengths) =
        ∑ lengths ∈ (Finset.univ.finsuppAntidiag n).filter
            (IsSignedRunLengthAssignment skeleton),
          ∏ i : Fin skeleton.length,
            PowerSeries.coeff (lengths i)
              (signedRunSeries weight (skeleton.get i)) := by
      apply Finset.sum_congr rfl
      intro lengths hlengths
      have hvalid := (Finset.mem_filter.mp hlengths).2
      rw [signedRunLengthSummand]
      apply Finset.prod_congr rfl
      intro i _
      exact (coeff_signedRunSeries_of_assignment weight hvalid i).symm
    _ = ∑ lengths ∈ Finset.univ.finsuppAntidiag n,
          ∏ i : Fin skeleton.length,
            PowerSeries.coeff (lengths i)
              (signedRunSeries weight (skeleton.get i)) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro lengths hlengths hnotmem
      have hnotvalid :
          ¬IsSignedRunLengthAssignment skeleton lengths := by
        intro hvalid
        exact hnotmem (Finset.mem_filter.mpr ⟨hlengths, hvalid⟩)
      obtain ⟨i, hi⟩ :=
        exists_coeff_signedRunSeries_eq_zero_of_not_assignment
          weight hnotvalid
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-! ## Realizing a fiber as canonical run data -/

/-- Turn an admissible length assignment on a Smirnov skeleton into canonical
run-length data. -/
def runLengthDataOfAssignment {q p : ℕ}
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    RunLengthData (SignedLetter q p) where
  runs := List.ofFn fun i => (skeleton.get i, lengths i)
  representatives_ne := by
    rw [← List.ofFn_comp']
    simpa using hskeleton
  lengths_pos := by
    intro run hrun
    rw [List.mem_ofFn] at hrun
    obtain ⟨i, hi⟩ := hrun
    rw [← hi]
    exact (hlengths i).1

@[simp]
theorem representatives_runLengthDataOfAssignment {q p : ℕ}
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    RunLengthData.representatives
        (runLengthDataOfAssignment skeleton hskeleton lengths hlengths) =
      skeleton := by
  change (List.ofFn (fun i => (skeleton.get i, lengths i))).map
      Prod.fst = skeleton
  rw [← List.ofFn_comp']
  simp

theorem runLengthDataOfAssignment_isSigned {q p : ℕ}
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    RunLengthData.IsSigned
      (runLengthDataOfAssignment skeleton hskeleton lengths hlengths) := by
  intro run hrun hpositive
  rw [runLengthDataOfAssignment, List.mem_ofFn] at hrun
  obtain ⟨i, hi⟩ := hrun
  rw [← hi] at hpositive ⊢
  exact (hlengths i).2 hpositive

theorem length_expand_runLengthDataOfAssignment {q p : ℕ}
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    (RunLengthData.expand
      (runLengthDataOfAssignment skeleton hskeleton lengths hlengths)).length =
      ∑ i : Fin skeleton.length, lengths i := by
  rw [RunLengthData.length_expand]
  change ((List.ofFn (fun i => (skeleton.get i, lengths i))).map
    Prod.snd).sum = _
  rw [← List.ofFn_comp', List.sum_ofFn]

theorem runWeight_runLengthDataOfAssignment
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    RunLengthData.runWeight weight
        (runLengthDataOfAssignment skeleton hskeleton lengths hlengths) =
      ∏ i : Fin skeleton.length,
        weight (skeleton.get i) ^ lengths i := by
  change ((List.ofFn (fun i => (skeleton.get i, lengths i))).map
    (fun run => weight run.1 ^ run.2)).prod = _
  rw [← List.ofFn_comp', List.prod_ofFn]

theorem excess_runLengthDataOfAssignment {q p : ℕ}
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    (runLengthDataOfAssignment skeleton hskeleton lengths hlengths).excess =
      ∑ i : Fin skeleton.length, (lengths i - 1) := by
  change ((List.ofFn (fun i => (skeleton.get i, lengths i))).map
    (fun run => run.2 - 1)).sum = _
  rw [← List.ofFn_comp', List.sum_ofFn]

/-- The explicit product summand is the run-data summand with the skeleton's
descent factor removed. -/
theorem runSummand_runLengthDataOfAssignment
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : List (SignedLetter q p))
    (hskeleton : skeleton.IsChain (· ≠ ·))
    (lengths : Fin skeleton.length →₀ ℕ)
    (hlengths : IsSignedRunLengthAssignment skeleton lengths) :
    RunLengthData.runSummand weight
        (runLengthDataOfAssignment skeleton hskeleton lengths hlengths) =
      X ^ listDescentNumber skeleton *
        signedRunLengthSummand weight skeleton lengths := by
  rw [RunLengthData.runSummand,
    representatives_runLengthDataOfAssignment,
    runWeight_runLengthDataOfAssignment,
    excess_runLengthDataOfAssignment, signedRunLengthSummand,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← map_prod]
  ring

/-! ## Global finite reindexing by skeleton and run lengths -/

/-- Length-`k` Smirnov words: tuples with distinct adjacent letters. -/
def signedSmirnovWords (q p k : ℕ) :
    Finset (Fin k → SignedLetter q p) := by
  classical
  exact Finset.univ.filter fun skeleton =>
    (List.ofFn skeleton).IsChain (· ≠ ·)

@[simp]
theorem mem_signedSmirnovWords_iff {q p k : ℕ}
    {skeleton : Fin k → SignedLetter q p} :
    skeleton ∈ signedSmirnovWords q p k ↔
      (List.ofFn skeleton).IsChain (· ≠ ·) := by
  classical
  simp [signedSmirnovWords]

/-- Tuple-level form of an admissible signed run-length assignment. -/
def IsSignedTupleRunLengthAssignment {q p k : ℕ}
    (skeleton : Fin k → SignedLetter q p)
    (lengths : Fin k →₀ ℕ) : Prop :=
  ∀ i, 0 < lengths i ∧
    ((skeleton i).IsPositive → lengths i = 1)

/-- Finite tuple-level length fiber with prescribed total length. -/
def signedTupleRunLengthFiber {q p k : ℕ}
    (skeleton : Fin k → SignedLetter q p) (n : ℕ) :
    Finset (Fin k →₀ ℕ) := by
  classical
  exact (Finset.univ.finsuppAntidiag n).filter
    (IsSignedTupleRunLengthAssignment skeleton)

@[simp]
theorem mem_signedTupleRunLengthFiber_iff {q p k : ℕ}
    {skeleton : Fin k → SignedLetter q p} {n : ℕ}
    {lengths : Fin k →₀ ℕ} :
    lengths ∈ signedTupleRunLengthFiber skeleton n ↔
      (∑ i : Fin k, lengths i) = n ∧
        IsSignedTupleRunLengthAssignment skeleton lengths := by
  classical
  simp [signedTupleRunLengthFiber, Finset.mem_finsuppAntidiag]

/-- Formal run-factor product for a tuple skeleton. -/
def signedTupleSkeletonRunSeries
    {R : Type*} [CommSemiring R] {q p k : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : Fin k → SignedLetter q p) : PowerSeries R[X] :=
  ∏ i : Fin k, signedRunSeries weight (skeleton i)

/-- Explicit runwise summand for a tuple length assignment. -/
def signedTupleRunLengthSummand
    {R : Type*} [CommSemiring R] {q p k : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : Fin k → SignedLetter q p)
    (lengths : Fin k →₀ ℕ) : R[X] :=
  ∏ i : Fin k,
    C (weight (skeleton i) ^ lengths i) *
      (1 + X) ^ (lengths i - 1)

theorem coeff_signedRunSeries_of_tupleAssignment
    {R : Type*} [CommSemiring R] {q p k : ℕ}
    (weight : SignedLetter q p → R)
    {skeleton : Fin k → SignedLetter q p}
    {lengths : Fin k →₀ ℕ}
    (hlengths : IsSignedTupleRunLengthAssignment skeleton lengths)
    (i : Fin k) :
    PowerSeries.coeff (lengths i) (signedRunSeries weight (skeleton i)) =
      C (weight (skeleton i) ^ lengths i) *
        (1 + X) ^ (lengths i - 1) := by
  rcases (skeleton i).isNegative_or_isPositive with
    hnegative | hpositive
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (hlengths i).1
    rw [hm]
    exact coeff_signedRunSeries_of_isNegative weight hnegative m
  · have hlength : lengths i = 1 := (hlengths i).2 hpositive
    rw [hlength]
    simpa using
      (coeff_signedRunSeries_of_isPositive weight hpositive 1)

theorem exists_coeff_signedRunSeries_eq_zero_of_not_tupleAssignment
    {R : Type*} [CommSemiring R] {q p k : ℕ}
    (weight : SignedLetter q p → R)
    {skeleton : Fin k → SignedLetter q p}
    {lengths : Fin k →₀ ℕ}
    (hlengths : ¬IsSignedTupleRunLengthAssignment skeleton lengths) :
    ∃ i : Fin k,
      PowerSeries.coeff (lengths i)
        (signedRunSeries weight (skeleton i)) = 0 := by
  classical
  simp only [IsSignedTupleRunLengthAssignment, not_forall,
    not_and_or] at hlengths
  obtain ⟨i, hnonpos | ⟨hpositive, hne⟩⟩ := hlengths
  · refine ⟨i, ?_⟩
    have hzero : lengths i = 0 := Nat.eq_zero_of_not_pos hnonpos
    simp [hzero]
  · refine ⟨i, ?_⟩
    rw [coeff_signedRunSeries_of_isPositive weight hpositive]
    simp [hne]

/-- Tuple form of the finite fixed-skeleton fiber factorization. -/
theorem coeff_signedTupleSkeletonRunSeries
    {R : Type*} [CommSemiring R] {q p k : ℕ}
    (weight : SignedLetter q p → R)
    (skeleton : Fin k → SignedLetter q p) (n : ℕ) :
    PowerSeries.coeff n (signedTupleSkeletonRunSeries weight skeleton) =
      ∑ lengths ∈ signedTupleRunLengthFiber skeleton n,
        signedTupleRunLengthSummand weight skeleton lengths := by
  classical
  rw [signedTupleSkeletonRunSeries, PowerSeries.coeff_prod]
  change (∑ lengths ∈ Finset.univ.finsuppAntidiag n,
      ∏ i : Fin k,
        PowerSeries.coeff (lengths i)
          (signedRunSeries weight (skeleton i))) = _
  rw [signedTupleRunLengthFiber]
  symm
  calc
    (∑ lengths ∈ (Finset.univ.finsuppAntidiag n).filter
          (IsSignedTupleRunLengthAssignment skeleton),
        signedTupleRunLengthSummand weight skeleton lengths) =
        ∑ lengths ∈ (Finset.univ.finsuppAntidiag n).filter
            (IsSignedTupleRunLengthAssignment skeleton),
          ∏ i : Fin k,
            PowerSeries.coeff (lengths i)
              (signedRunSeries weight (skeleton i)) := by
      apply Finset.sum_congr rfl
      intro lengths hlengths
      have hvalid := (Finset.mem_filter.mp hlengths).2
      rw [signedTupleRunLengthSummand]
      apply Finset.prod_congr rfl
      intro i _
      exact (coeff_signedRunSeries_of_tupleAssignment
        weight hvalid i).symm
    _ = ∑ lengths ∈ Finset.univ.finsuppAntidiag n,
          ∏ i : Fin k,
            PowerSeries.coeff (lengths i)
              (signedRunSeries weight (skeleton i)) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro lengths hlengths hnotmem
      have hnotvalid :
          ¬IsSignedTupleRunLengthAssignment skeleton lengths := by
        intro hvalid
        exact hnotmem (Finset.mem_filter.mpr ⟨hlengths, hvalid⟩)
      obtain ⟨i, hi⟩ :=
        exists_coeff_signedRunSeries_eq_zero_of_not_tupleAssignment
          weight hnotvalid
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- The finite disjoint union of all Smirnov skeleton/run-length pairs that
expand to total length `n`. -/
def signedSmirnovExpansionFiber (q p n : ℕ) : Finset
    (Σ k : ℕ,
      Σ _skeleton : Fin k → SignedLetter q p, Fin k →₀ ℕ) := by
  classical
  exact (Finset.range (n + 1)).sigma fun k =>
    (signedSmirnovWords q p k).sigma fun skeleton =>
      signedTupleRunLengthFiber skeleton n

/-- Tuple of representatives of canonical run data. -/
def RunLengthData.representativeTuple {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    Fin data.runs.length → SignedLetter q p :=
  fun i => (data.runs.get i).1

/-- Tuple of lengths of canonical run data, viewed as a finitely supported
function on its finite run positions. -/
def RunLengthData.lengthTuple {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    Fin data.runs.length →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (data.runs.get i).2

@[simp]
theorem RunLengthData.lengthTuple_apply {q p : ℕ}
    (data : RunLengthData (SignedLetter q p))
    (i : Fin data.runs.length) :
    data.lengthTuple i = (data.runs.get i).2 :=
  rfl

@[simp]
theorem RunLengthData.ofFn_representativeTuple {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    List.ofFn data.representativeTuple = data.representatives := by
  change List.ofFn (fun i => (data.runs.get i).1) =
    data.runs.map Prod.fst
  calc
    _ = (List.ofFn data.runs.get).map Prod.fst :=
      List.ofFn_comp' data.runs.get Prod.fst
    _ = _ := by rw [List.ofFn_get]

/-- The skeleton/length index obtained by compressing a finite word. -/
def compressedRunIndex {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    Σ k : ℕ,
      Σ _skeleton : Fin k → SignedLetter q p, Fin k →₀ ℕ :=
  let data := compressRunLengthData (List.ofFn word)
  ⟨data.runs.length, data.representativeTuple, data.lengthTuple⟩

/-- Recover the literal run list encoded by a global skeleton/length index. -/
def runIndexRuns {q p : ℕ}
    (index : Σ k : ℕ,
      Σ _skeleton : Fin k → SignedLetter q p, Fin k →₀ ℕ) :
    List (SignedLetter q p × ℕ) :=
  List.ofFn fun i => (index.2.1 i, index.2.2 i)

@[simp]
theorem runIndexRuns_compressedRunIndex {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    runIndexRuns (compressedRunIndex word) =
      (compressRunLengthData (List.ofFn word)).runs := by
  rw [runIndexRuns, compressedRunIndex]
  change List.ofFn (fun i =>
    (((compressRunLengthData (List.ofFn word)).runs.get i).1,
      ((compressRunLengthData (List.ofFn word)).runs.get i).2)) = _
  simp

theorem runIndexRuns_injective {q p : ℕ} :
    Function.Injective
      (runIndexRuns (q := q) (p := p)) := by
  rintro ⟨k, skeleton, lengths⟩ ⟨k', skeleton', lengths'⟩ hindex
  have hk : k = k' := by
    simpa [runIndexRuns] using congrArg List.length hindex
  subst k'
  have hpairs :
      (fun i => (skeleton i, lengths i)) =
        fun i => (skeleton' i, lengths' i) := by
    exact List.ofFn_injective hindex
  have hskeleton : skeleton = skeleton' := by
    funext i
    exact congrArg Prod.fst (congrFun hpairs i)
  have hlengths : lengths = lengths' := by
    apply Finsupp.ext
    intro i
    exact congrArg Prod.snd (congrFun hpairs i)
  subst skeleton'
  subst lengths'
  rfl

theorem compressedRunIndex_injective {q p n : ℕ} :
    Function.Injective
      (compressedRunIndex :
        (Fin n → SignedLetter q p) →
          Σ k : ℕ,
            Σ _skeleton : Fin k → SignedLetter q p,
              Fin k →₀ ℕ) := by
  intro left right hindex
  have hruns := congrArg runIndexRuns hindex
  rw [runIndexRuns_compressedRunIndex,
    runIndexRuns_compressedRunIndex] at hruns
  have hdata :
      compressRunLengthData (List.ofFn left) =
        compressRunLengthData (List.ofFn right) :=
    RunLengthData.ext hruns
  apply List.ofFn_injective
  calc
    List.ofFn left =
        (compressRunLengthData (List.ofFn left)).expand := by simp
    _ = (compressRunLengthData (List.ofFn right)).expand := by rw [hdata]
    _ = List.ofFn right := by simp

theorem RunLengthData.sum_lengthTuple {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    (∑ i : Fin data.runs.length, data.lengthTuple i) =
      (data.runs.map Prod.snd).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn fun i => (data.runs.get i).2).sum = _
  calc
    _ = ((List.ofFn data.runs.get).map Prod.snd).sum := by
      rw [← List.ofFn_comp']
    _ = _ := by rw [List.ofFn_get]

theorem RunLengthData.lengthTuple_isSignedAssignment {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) (hsigned : data.IsSigned) :
    IsSignedTupleRunLengthAssignment data.representativeTuple
      data.lengthTuple := by
  intro i
  have hmem : data.runs.get i ∈ data.runs := List.get_mem data.runs i
  exact ⟨data.lengths_pos _ hmem, fun hpositive =>
    hsigned _ hmem hpositive⟩

theorem RunLengthData.runCount_le_sum_lengthTuple {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    data.runs.length ≤
      ∑ i : Fin data.runs.length, data.lengthTuple i := by
  calc
    data.runs.length = ∑ _i : Fin data.runs.length, 1 := by simp
    _ ≤ ∑ i : Fin data.runs.length, data.lengthTuple i := by
      apply Finset.sum_le_sum
      intro i _
      exact data.lengths_pos _ (List.get_mem data.runs i)

/-- Compression sends every admissible length-`n` word into the finite global
Smirnov expansion fiber. -/
theorem compressedRunIndex_mem_signedSmirnovExpansionFiber
    {q p n : ℕ} (word : Fin n → SignedLetter q p)
    (hword : IsSignedWord n word) :
    compressedRunIndex word ∈ signedSmirnovExpansionFiber q p n := by
  classical
  let data := compressRunLengthData (List.ofFn word)
  have hsum : (∑ i : Fin data.runs.length, data.lengthTuple i) = n := by
    rw [data.sum_lengthTuple]
    exact sum_runLengths_compress_ofFn word
  have hsigned : data.IsSigned := by
    rw [← data.isSignedList_expand_iff]
    simpa [data] using (isSignedList_ofFn_iff word).mpr hword
  have hcount : data.runs.length ≤ n := by
    rw [← hsum]
    exact data.runCount_le_sum_lengthTuple
  change ⟨data.runs.length, data.representativeTuple,
    data.lengthTuple⟩ ∈ signedSmirnovExpansionFiber q p n
  rw [signedSmirnovExpansionFiber]
  simp only [Finset.mem_sigma, Finset.mem_range]
  refine ⟨Nat.lt_succ_iff.mpr hcount, ?_, ?_⟩
  · rw [mem_signedSmirnovWords_iff,
      data.ofFn_representativeTuple]
    exact data.representatives_ne
  · rw [mem_signedTupleRunLengthFiber_iff]
    exact ⟨hsum, data.lengthTuple_isSignedAssignment hsigned⟩

/-- The polynomial contribution attached to a global skeleton/length index. -/
def signedExpansionIndexSummand
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (index : Σ k : ℕ,
      Σ _skeleton : Fin k → SignedLetter q p, Fin k →₀ ℕ) :
    R[X] :=
  X ^ listDescentNumber (List.ofFn index.2.1) *
    ∏ i,
      C (weight (index.2.1 i) ^ index.2.2 i) *
        (1 + X) ^ (index.2.2 i - 1)

theorem RunLengthData.runWeight_eq_tupleProduct
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (data : RunLengthData (SignedLetter q p)) :
    data.runWeight weight =
      ∏ i : Fin data.runs.length,
        weight (data.representativeTuple i) ^ data.lengthTuple i := by
  change (data.runs.map fun run => weight run.1 ^ run.2).prod = _
  conv_lhs => rw [← List.ofFn_get data.runs]
  rw [← List.ofFn_comp', List.prod_ofFn]
  rfl

theorem RunLengthData.excess_eq_tupleSum {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    data.excess =
      ∑ i : Fin data.runs.length, (data.lengthTuple i - 1) := by
  change (data.runs.map fun run => run.2 - 1).sum = _
  conv_lhs => rw [← List.ofFn_get data.runs]
  rw [← List.ofFn_comp', List.sum_ofFn]
  rfl

theorem RunLengthData.runSummand_eq_expansionIndexSummand
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (data : RunLengthData (SignedLetter q p)) :
    data.runSummand weight =
      signedExpansionIndexSummand weight
        ⟨data.runs.length, data.representativeTuple,
          data.lengthTuple⟩ := by
  rw [RunLengthData.runSummand, data.runWeight_eq_tupleProduct,
    data.excess_eq_tupleSum]
  unfold signedExpansionIndexSummand
  rw [data.ofFn_representativeTuple, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← map_prod]
  ring

/-- The global index summand of a compressed word is its literal signed-word
summand. -/
theorem signedExpansionIndexSummand_compressedRunIndex
    {R : Type*} [CommSemiring R] {q p n : ℕ}
    (weight : SignedLetter q p → R)
    (word : Fin n → SignedLetter q p) :
    signedExpansionIndexSummand weight (compressedRunIndex word) =
      C (signedWordWeight weight word) *
        X ^ signedDescentNumber word *
          (1 + X) ^ signedCollisionNumber word := by
  rw [signedWordSummand_eq_runSummand]
  exact (RunLengthData.runSummand_eq_expansionIndexSummand weight
    (compressRunLengthData (List.ofFn word))).symm

/-- Canonical run data built directly from a tuple skeleton and its admissible
length assignment. -/
def runLengthDataOfTupleAssignment {q p k : ℕ}
    (skeleton : Fin k → SignedLetter q p)
    (hskeleton : (List.ofFn skeleton).IsChain (· ≠ ·))
    (lengths : Fin k →₀ ℕ)
    (hlengths : IsSignedTupleRunLengthAssignment skeleton lengths) :
    RunLengthData (SignedLetter q p) where
  runs := List.ofFn fun i => (skeleton i, lengths i)
  representatives_ne := by
    rw [← List.ofFn_comp']
    simpa using hskeleton
  lengths_pos := by
    intro run hrun
    rw [List.mem_ofFn] at hrun
    obtain ⟨i, hi⟩ := hrun
    rw [← hi]
    exact (hlengths i).1

theorem runLengthDataOfTupleAssignment_isSigned {q p k : ℕ}
    (skeleton : Fin k → SignedLetter q p)
    (hskeleton : (List.ofFn skeleton).IsChain (· ≠ ·))
    (lengths : Fin k →₀ ℕ)
    (hlengths : IsSignedTupleRunLengthAssignment skeleton lengths) :
    RunLengthData.IsSigned
      (runLengthDataOfTupleAssignment skeleton hskeleton lengths hlengths) := by
  intro run hrun hpositive
  rw [runLengthDataOfTupleAssignment, List.mem_ofFn] at hrun
  obtain ⟨i, hi⟩ := hrun
  rw [← hi] at hpositive ⊢
  exact (hlengths i).2 hpositive

theorem length_expand_runLengthDataOfTupleAssignment {q p k : ℕ}
    (skeleton : Fin k → SignedLetter q p)
    (hskeleton : (List.ofFn skeleton).IsChain (· ≠ ·))
    (lengths : Fin k →₀ ℕ)
    (hlengths : IsSignedTupleRunLengthAssignment skeleton lengths) :
    (RunLengthData.expand
      (runLengthDataOfTupleAssignment skeleton hskeleton lengths hlengths)).length =
      ∑ i : Fin k, lengths i := by
  rw [RunLengthData.length_expand]
  change ((List.ofFn fun i => (skeleton i, lengths i)).map
    Prod.snd).sum = _
  rw [← List.ofFn_comp', List.sum_ofFn]

/-- Convert a list of known length to its corresponding finite tuple. -/
def listAsTuple {A : Type*} {n : ℕ} (word : List A)
    (hlength : word.length = n) : Fin n → A :=
  fun i => word.get (Fin.cast hlength.symm i)

@[simp]
theorem ofFn_listAsTuple {A : Type*} {n : ℕ} (word : List A)
    (hlength : word.length = n) :
    List.ofFn (listAsTuple word hlength) = word := by
  apply List.ext_get (by simp [hlength])
  intro i hi hword
  simp [listAsTuple]

theorem compressedRunIndex_surjOn_signedSmirnovExpansionFiber
    {q p n : ℕ}
    (index : Σ k : ℕ,
      Σ _skeleton : Fin k → SignedLetter q p, Fin k →₀ ℕ)
    (hindex : index ∈ signedSmirnovExpansionFiber q p n) :
    ∃ word ∈ signedWords q p n, compressedRunIndex word = index := by
  classical
  obtain ⟨k, skeleton, lengths⟩ := index
  rw [signedSmirnovExpansionFiber] at hindex
  simp only [Finset.mem_sigma, Finset.mem_range] at hindex
  obtain ⟨_, hskeleton, hlengths⟩ := hindex
  rw [mem_signedSmirnovWords_iff] at hskeleton
  rw [mem_signedTupleRunLengthFiber_iff] at hlengths
  let data := runLengthDataOfTupleAssignment skeleton hskeleton lengths
    hlengths.2
  have hexpandLength : data.expand.length = n := by
    calc
      data.expand.length = ∑ i : Fin k, lengths i := by
        simpa [data] using
          (length_expand_runLengthDataOfTupleAssignment skeleton hskeleton
            lengths hlengths.2)
      _ = n := hlengths.1
  let word := listAsTuple data.expand hexpandLength
  have hwordList : List.ofFn word = data.expand := by
    exact ofFn_listAsTuple data.expand hexpandLength
  have hsigned : data.IsSigned := by
    exact runLengthDataOfTupleAssignment_isSigned skeleton hskeleton
      lengths hlengths.2
  have hword : IsSignedWord n word := by
    rw [← isSignedList_ofFn_iff, hwordList,
      data.isSignedList_expand_iff]
    exact hsigned
  refine ⟨word, (mem_signedWords_iff.mpr hword), ?_⟩
  apply runIndexRuns_injective
  rw [runIndexRuns_compressedRunIndex, hwordList,
    data.compress_expand]
  rfl

/-! ## Coefficientwise substitution identity -/

/-- The coefficientwise finite form of the signed-Smirnov substitution.
For a fixed length `n`, only skeleton lengths `k ≤ n` occur.  A positive
letter contributes `weight z`, while a negative letter contributes the formal
factor `weight z / (1 - weight (1 + t) z)`. -/
def signedSmirnovSubstitutionCoeff
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    ∑ skeleton ∈ signedSmirnovWords q p k,
      X ^ listDescentNumber (List.ofFn skeleton) *
        PowerSeries.coeff n
          (signedTupleSkeletonRunSeries weight skeleton)

/-- Expanding the substituted run factors gives exactly the finite global
skeleton/run-length fiber sum. -/
theorem signedSmirnovSubstitutionCoeff_eq_sum_expansionFiber
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (n : ℕ) :
    signedSmirnovSubstitutionCoeff weight n =
      ∑ index ∈ signedSmirnovExpansionFiber q p n,
        signedExpansionIndexSummand weight index := by
  classical
  unfold signedSmirnovSubstitutionCoeff
  simp_rw [coeff_signedTupleSkeletonRunSeries, Finset.mul_sum]
  rw [signedSmirnovExpansionFiber, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_sigma]
  rfl

/-- The literal signed-word enumerator is the finite global
skeleton/run-length fiber sum. -/
theorem signedWordEnumerator_eq_sum_expansionFiber
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (n : ℕ) :
    signedWordEnumerator weight n =
      ∑ index ∈ signedSmirnovExpansionFiber q p n,
        signedExpansionIndexSummand weight index := by
  classical
  rw [signedWordEnumerator]
  apply Finset.sum_bij
    (fun word _ => compressedRunIndex word)
  · intro word hword
    exact compressedRunIndex_mem_signedSmirnovExpansionFiber word
      (mem_signedWords_iff.mp hword)
  · intro left _ right _ hindex
    exact compressedRunIndex_injective hindex
  · intro index hindex
    obtain ⟨word, hword, hcompressed⟩ :=
      compressedRunIndex_surjOn_signedSmirnovExpansionFiber index hindex
    exact ⟨word, hword, hcompressed⟩
  · intro word _
    exact (signedExpansionIndexSummand_compressedRunIndex
      weight word).symm

/-- Checked coefficientwise Brändén--Vecchi negative-run substitution:
the signed-word enumerator equals the substituted signed-Smirnov skeleton sum
in every length. -/
theorem signedWordEnumerator_eq_signedSmirnovSubstitutionCoeff
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (n : ℕ) :
    signedWordEnumerator weight n =
      signedSmirnovSubstitutionCoeff weight n := by
  rw [signedWordEnumerator_eq_sum_expansionFiber,
    signedSmirnovSubstitutionCoeff_eq_sum_expansionFiber]

/-- Coefficientwise signed-Smirnov substitution is compatible with the
zero-weight sign-preserving alphabet extensions from the literal enumerator. -/
theorem signedSmirnovSubstitutionCoeff_extend
    {R : Type*} [CommSemiring R] {q p q' p' : ℕ}
    (e : SignedLetter q p ↪o SignedLetter q' p')
    (hnegative : ∀ a, (e a).IsNegative ↔ a.IsNegative)
    (weight : SignedLetter q p → R) (n : ℕ) :
    signedSmirnovSubstitutionCoeff weight n =
      signedSmirnovSubstitutionCoeff
        (extendSignedLetterWeight e.toEmbedding weight) n := by
  calc
    signedSmirnovSubstitutionCoeff weight n =
        signedWordEnumerator weight n :=
      (signedWordEnumerator_eq_signedSmirnovSubstitutionCoeff
        weight n).symm
    _ = signedWordEnumerator
        (extendSignedLetterWeight e.toEmbedding weight) n :=
      signedWordEnumerator_extend e hnegative weight n
    _ = signedSmirnovSubstitutionCoeff
        (extendSignedLetterWeight e.toEmbedding weight) n :=
      signedWordEnumerator_eq_signedSmirnovSubstitutionCoeff _ n

/-- Adjoining outer zero-weight negative and positive letters leaves the
substituted signed-Smirnov coefficient unchanged. -/
theorem signedSmirnovSubstitutionCoeff_add_zero_letters
    {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R) (r s n : ℕ) :
    signedSmirnovSubstitutionCoeff weight n =
      signedSmirnovSubstitutionCoeff
        (extendSignedLetterWeight
          (signedLetterExtend q p r s).toEmbedding weight) n := by
  exact signedSmirnovSubstitutionCoeff_extend
    (signedLetterExtend q p r s)
    (signedLetterExtend_isNegative_iff q p r s) weight n

end

end RealRooted.BrandenVecchi
