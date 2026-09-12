import RealRooted.BrandenLeite.WhitneyReduction
import RealRooted.BrandenVecchi.ChowResolutionInterlacing

/-!
# Chow polynomials of totally nonnegative matrices

This file derives the matrix endpoint of Bränden--Vecchi, Theorem 4.18 from
the canonical resolution of a lower-unitriangular totally nonnegative matrix.
All statements retain the zero-polynomial cases explicitly.
-/

open Matrix Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

variable {A : LowerTriangularMatrix ℝ}

private theorem reflect_reverses_prec0_of_pf
    {n : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n)
    (hpq : Prec0 p q) :
    Prec0 (q.reflect n) (p.reflect n) := by
  rcases hpq with hpzero | hqzero | hpq
  · subst p
    simpa using prec0_zero_right (q.reflect n)
  · subst q
    simpa using prec0_zero_left (p.reflect n)
  · exact (reciprocalShift_reverses_prec hp hq hpdeg hqdeg hpq).toPrec0

private theorem reflectionInterlacing_pair_of_relations
    {n : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n)
    (hpq : Prec0 p q)
    (hpqref : Prec0 p (q.reflect n))
    (hpref : Prec0 p (p.reflect n))
    (hqref : Prec0 q (q.reflect n))
    (hqpref : Prec0 q (p.reflect n))
    (hqrefpref : Prec0 (q.reflect n) (p.reflect n)) :
    IsReflectionInterlacingSeq n [p, q] := by
  have hpref_pf := reciprocalShift_preserves_pf hp hpdeg
  have hqref_pf := reciprocalShift_preserves_pf hq hqdeg
  refine ⟨by simp [hpdeg, hqdeg], ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    simpa [reflectionClosure] using
      And.intro (And.intro hpq <| And.intro hpqref hpref) <|
        And.intro (And.intro hqref hqpref) hqrefpref
  · intro r hr
    simp only [reflectionClosure, List.mem_append, List.mem_cons,
      List.mem_reverse, List.mem_map, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | ⟨s, rfl | rfl, rfl⟩
    · exact hp.hasNonnegCoeffs
    · exact hq.hasNonnegCoeffs
    · exact hpref_pf.hasNonnegCoeffs
    · exact hqref_pf.hasNonnegCoeffs
  · intro r hr hrzero
    simp only [reflectionClosure, List.mem_append, List.mem_cons,
      List.mem_reverse, List.mem_map, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | ⟨s, rfl | rfl, rfl⟩
    · exact hp.ne_zero_and_splits hrzero
    · exact hq.ne_zero_and_splits hrzero
    · exact hpref_pf.ne_zero_and_splits hrzero
    · exact hqref_pf.ne_zero_and_splits hrzero

private theorem reflect_finset_sum_C_mul
    {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (f : ι → ℝ[X]) (n : ℕ) :
    (∑ i ∈ s, C (a i) * f i).reflect n =
      ∑ i ∈ s, C (a i) * (f i).reflect n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih, Polynomial.reflect_add, Polynomial.reflect_C_mul]

private theorem resolvedChowWeightSum_endpoint_pairs
    {A : LowerTriangularMatrix ℝ}
    (resolution : BrandenLeite.Resolution A) (n : ℕ) :
    IsReflectionInterlacingSeq n
        [resolvedChowDerangement resolution n 0,
          resolvedChowWeightSum resolution n] ∧
      IsReflectionInterlacingSeq n
        [resolvedChowWeightSum resolution n,
          resolvedChowDerangement resolution n n] := by
  classical
  let d : ℕ → ℝ[X] := fun j => resolvedChowDerangement resolution n j
  let a : ℕ → ℝ := fun j => resolution.lambda n j
  let F : ℝ[X] := resolvedChowWeightSum resolution n
  have ha : ∀ j, j ≤ n → 0 ≤ a j := by
    intro j hj
    exact resolution.lambda_nonneg n j hj
  have hrow := resolvedChowRow_reflectionInterlacing resolution n
  have hclosed := hrow.closedSequence
  have hpairwise :
      (resolvedChowRow resolution n ++
        ((resolvedChowRow resolution n).map fun p => p.reflect n).reverse).Pairwise
          Prec0 := by
    simpa [reflectionClosure] using
      isInterlacingSeq0_iff_pairwise.mp hclosed.interlacingSeq0
  have hdirect := (List.pairwise_append.mp hpairwise).1
  have hcross := (List.pairwise_append.mp hpairwise).2.2
  have hmem : ∀ j, j ≤ n → d j ∈ resolvedChowRow resolution n := by
    intro j hj
    exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
  have hrefmem : ∀ j, j ≤ n →
      (d j).reflect n ∈
        ((resolvedChowRow resolution n).map fun p => p.reflect n).reverse := by
    intro j hj
    rw [List.mem_reverse]
    exact List.mem_map.mpr ⟨d j, hmem j hj, rfl⟩
  have hdnn : ∀ j, j ≤ n → HasNonnegCoeffs (d j) := by
    intro j hj
    exact resolvedChowDerangement_nonnegCoeffs resolution hj
  have hdpf : ∀ j, j ≤ n → IsPFPolynomial (d j) := by
    intro j hj
    exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits (hdnn j hj)
      (resolvedChowDerangement_eq_zero_or_splits resolution hj)
  have hddeg : ∀ j, j ≤ n → (d j).natDegree ≤ n := by
    intro j hj
    exact hrow.natDegree_le (hmem j hj)
  have hdself : ∀ j, j ≤ n → Prec0 (d j) (d j) := by
    intro j hj
    exact (hdpf j hj).prec0_self
  have hleft : ∀ j, j ≤ n → Prec0 (d 0) (d j) := by
    intro j hj
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hjpos
    · exact hdself 0 (Nat.zero_le n)
    · let first : Fin (resolvedChowRow resolution n).length :=
        ⟨0, by simp; lia⟩
      let current : Fin (resolvedChowRow resolution n).length :=
        ⟨j, by simpa using hj⟩
      simpa [first, current, d, resolvedChowRow] using
        hdirect.rel_get_of_lt (a := first) (b := current) hjpos
  have hright : ∀ j, j ≤ n → Prec0 (d j) (d n) := by
    intro j hj
    by_cases heq : j = n
    · subst j
      exact hdself n le_rfl
    · have hjlt : j < n := Nat.lt_of_le_of_ne hj heq
      let current : Fin (resolvedChowRow resolution n).length :=
        ⟨j, by simpa using hj⟩
      let last : Fin (resolvedChowRow resolution n).length :=
        ⟨n, by simp⟩
      simpa [current, last, d, resolvedChowRow] using
        hdirect.rel_get_of_lt (a := current) (b := last) hjlt
  have hdirectReflect : ∀ i, i ≤ n → ∀ j, j ≤ n →
      Prec0 (d i) ((d j).reflect n) := by
    intro i hi j hj
    exact hcross (d i) (hmem i hi) ((d j).reflect n) (hrefmem j hj)
  have hreflectLeft : ∀ j, j ≤ n →
      Prec0 ((d j).reflect n) ((d 0).reflect n) := by
    intro j hj
    exact reflect_reverses_prec0_of_pf (hdpf 0 (Nat.zero_le n))
      (hdpf j hj) (hddeg 0 (Nat.zero_le n)) (hddeg j hj) (hleft j hj)
  have hreflectRight : ∀ j, j ≤ n →
      Prec0 ((d n).reflect n) ((d j).reflect n) := by
    intro j hj
    exact reflect_reverses_prec0_of_pf (hdpf j hj) (hdpf n le_rfl)
      (hddeg j hj) (hddeg n le_rfl) (hright j hj)
  have hFpf : IsPFPolynomial F := by
    simpa [F, a, resolvedChowWeightSum, resolvedChowCombination] using
      resolvedChowCombination_isPF resolution ha
  have hFdeg : F.natDegree ≤ n := by
    dsimp only [F, resolvedChowWeightSum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro j hj
    exact (natDegree_C_mul_le (a j) (d j)).trans (hddeg j (by simpa using hj))
  have hreflectF : F.reflect n =
      ∑ j ∈ Finset.range (n + 1), C (a j) * (d j).reflect n := by
    simpa [F, a, d, resolvedChowWeightSum] using
      reflect_finset_sum_C_mul (Finset.range (n + 1)) a d n
  have hFbounds : Prec0 (d 0) F ∧ Prec0 F (d n) := by
    simpa [F, a, d, resolvedChowWeightSum, resolvedChowCombination] using
      resolvedChowCombination_endpoint_prec0 resolution ha
  have h0refF : Prec0 (d 0) (F.reflect n) := by
    rw [hreflectF]
    apply prec0_finsetSum_left_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_right_of_nonneg
        (hdirectReflect 0 (Nat.zero_le n) j hjn) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) ((hdnn j hjn).reflect n)
  have hFref0 : Prec0 F ((d 0).reflect n) := by
    dsimp only [F, resolvedChowWeightSum]
    apply prec0_finsetSum_right_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_left_of_nonneg
        (hdirectReflect j hjn 0 (Nat.zero_le n)) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) (hdnn j hjn)
  have hrefFref0 : Prec0 (F.reflect n) ((d 0).reflect n) := by
    rw [hreflectF]
    apply prec0_finsetSum_right_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_left_of_nonneg (hreflectLeft j hjn) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) ((hdnn j hjn).reflect n)
  have hFrefn : Prec0 F ((d n).reflect n) := by
    dsimp only [F, resolvedChowWeightSum]
    apply prec0_finsetSum_right_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_left_of_nonneg
        (hdirectReflect j hjn n le_rfl) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) (hdnn j hjn)
  have hnrefF : Prec0 (d n) (F.reflect n) := by
    rw [hreflectF]
    apply prec0_finsetSum_left_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_right_of_nonneg
        (hdirectReflect n le_rfl j hjn) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) ((hdnn j hjn).reflect n)
  have hrefnrefF : Prec0 ((d n).reflect n) (F.reflect n) := by
    rw [hreflectF]
    apply prec0_finsetSum_left_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_right_of_nonneg (hreflectRight j hjn) (ha j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) ((hdnn j hjn).reflect n)
  have hFrefF : Prec0 F (F.reflect n) := by
    rw [hreflectF]
    dsimp only [F, resolvedChowWeightSum]
    apply prec0_finsetSum_pairwise_of_nonneg
    · intro i hi j hj
      have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_right_of_nonneg
        (prec0_C_mul_left_of_nonneg (hdirectReflect i hin j hjn) (ha i hin))
        (ha j hjn)
    · intro i hi
      have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
      exact nonnegCoeffs_C_mul (ha i hin) (hdnn i hin)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (ha j hjn) ((hdnn j hjn).reflect n)
  constructor
  · exact reflectionInterlacing_pair_of_relations
      (hdpf 0 (Nat.zero_le n)) hFpf (hddeg 0 (Nat.zero_le n)) hFdeg
      hFbounds.1 h0refF
      (hdirectReflect 0 (Nat.zero_le n) 0 (Nat.zero_le n))
      hFrefF hFref0 hrefFref0
  · exact reflectionInterlacing_pair_of_relations
      hFpf (hdpf n le_rfl) hFdeg (hddeg n le_rfl)
      hFbounds.2 hFrefn hFrefF
      (hdirectReflect n le_rfl n le_rfl) hnrefF hrefnrefF

/-- The canonical resolution row of a lower-unitriangular totally
nonnegative matrix is reflection-interlacing. -/
theorem resolvedChowRow_reflectionInterlacing_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    IsReflectionInterlacingSeq n
      (resolvedChowRow
        (BrandenLeite.resolutionOfTotallyNonneg A hunit hA) n) :=
  resolvedChowRow_reflectionInterlacing
    (BrandenLeite.resolutionOfTotallyNonneg A hunit hA) n

/-- Chow polynomials of lower-unitriangular totally nonnegative matrices have
nonnegative coefficients. -/
theorem chowPolynomial_nonnegCoeffs_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    HasNonnegCoeffs (chowPolynomial A n) := by
  simpa using resolvedChowDerangement_nonnegCoeffs
    (BrandenLeite.resolutionOfTotallyNonneg A hunit hA)
    (Nat.zero_le n)

/-- Chow polynomials of lower-unitriangular totally nonnegative matrices are
zero or split. -/
theorem chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    chowPolynomial A n = 0 ∨ (chowPolynomial A n).Splits := by
  simpa using resolvedChowDerangement_eq_zero_or_splits
    (BrandenLeite.resolutionOfTotallyNonneg A hunit hA)
    (Nat.zero_le n)

/-- Chow-derangement polynomials of lower-unitriangular totally nonnegative
matrices have nonnegative coefficients. -/
theorem chowDerangement_nonnegCoeffs_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    HasNonnegCoeffs (chowDerangement A n) := by
  simpa using resolvedChowDerangement_nonnegCoeffs
    (BrandenLeite.resolutionOfTotallyNonneg A hunit hA)
    (le_rfl : n ≤ n)

/-- Chow-derangement polynomials of lower-unitriangular totally nonnegative
matrices are zero or split. -/
theorem chowDerangement_eq_zero_or_splits_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    chowDerangement A n = 0 ∨ (chowDerangement A n).Splits := by
  simpa using resolvedChowDerangement_eq_zero_or_splits
    (BrandenLeite.resolutionOfTotallyNonneg A hunit hA)
    (le_rfl : n ≤ n)

/-- In each row, the Chow polynomial precedes the Chow-derangement
polynomial, with vanishing endpoints allowed. -/
theorem chowPolynomial_prec0_chowDerangement_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    Prec0 (chowPolynomial A n) (chowDerangement A n) := by
  let resolution := BrandenLeite.resolutionOfTotallyNonneg A hunit hA
  cases n with
  | zero =>
      rw [chowPolynomial_zero A (hunit.diagonal 0), chowDerangement_zero]
      exact (prec_refl one_ne_zero Polynomial.Splits.one).toPrec0
  | succ n =>
      have hrow := resolvedChowRow_reflectionInterlacing resolution (n + 1)
      have hdirect : IsInterlacingSeq0NonnegRealRooted
          (resolvedChowRow resolution (n + 1)) :=
        hrow.closedSequence.sublist (by simp [reflectionClosure])
      let first : Fin (resolvedChowRow resolution (n + 1)).length :=
        ⟨0, by rw [length_resolvedChowRow]; lia⟩
      let last : Fin (resolvedChowRow resolution (n + 1)).length :=
        ⟨n + 1, by rw [length_resolvedChowRow]; lia⟩
      have hprec := hdirect.interlacingSeq0.prec0
        (i := first) (j := last) (by change 0 < n + 1; lia)
      simpa [first, last, resolvedChowRow] using hprec

/-- Strict within-row endpoint relation under explicit nonvanishing
hypotheses. -/
theorem chowPolynomial_prec_chowDerangement_of_isTotallyNonneg_of_ne
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ)
    (hchow : chowPolynomial A n ≠ 0)
    (hderangement : chowDerangement A n ≠ 0) :
    Prec (chowPolynomial A n) (chowDerangement A n) :=
  (chowPolynomial_prec0_chowDerangement_of_isTotallyNonneg hunit hA n).toPrec_of_ne
    hchow hderangement

/-- Consecutive Chow polynomials are in zero-aware proper position. -/
theorem chowPolynomial_prec0_succ_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    Prec0 (chowPolynomial A n) (chowPolynomial A (n + 1)) := by
  let resolution := BrandenLeite.resolutionOfTotallyNonneg A hunit hA
  have hpairs := resolvedChowWeightSum_endpoint_pairs resolution n
  have hext := hpairs.1.chowSExtension
  have hsucc : chowPolynomial A (n + 1) =
      X * chowS n (resolvedChowWeightSum resolution n) +
        resolvedChowWeightSum resolution n := by
    rw [← resolvedChowDerangement_zero resolution (n + 1),
      resolvedChowDerangement_succ resolution (k := 0) (by lia)]
    simp [resolvedChowWeightSum]
  have hprec := hext.closedSequence.interlacingSeq0.prec0
    (i := (⟨1, by simp [reflectionClosure]⟩ :
      Fin (reflectionClosure n
        [chowS n (resolvedChowDerangement resolution n 0),
          resolvedChowDerangement resolution n 0,
          resolvedChowWeightSum resolution n,
          X * chowS n (resolvedChowWeightSum resolution n) +
            resolvedChowWeightSum resolution n]).length))
    (j := (⟨3, by simp [reflectionClosure]⟩ :
      Fin (reflectionClosure n
        [chowS n (resolvedChowDerangement resolution n 0),
          resolvedChowDerangement resolution n 0,
          resolvedChowWeightSum resolution n,
          X * chowS n (resolvedChowWeightSum resolution n) +
            resolvedChowWeightSum resolution n]).length)) (by simp)
  simpa [reflectionClosure, hsucc] using hprec

/-- Strict consecutive Chow relation under explicit nonvanishing
hypotheses. -/
theorem chowPolynomial_prec_succ_of_isTotallyNonneg_of_ne
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ)
    (hn : chowPolynomial A n ≠ 0)
    (hsucc : chowPolynomial A (n + 1) ≠ 0) :
    Prec (chowPolynomial A n) (chowPolynomial A (n + 1)) :=
  (chowPolynomial_prec0_succ_of_isTotallyNonneg hunit hA n).toPrec_of_ne
    hn hsucc

/-- Consecutive Chow-derangement polynomials are in zero-aware proper
position. -/
theorem chowDerangement_prec0_succ_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    Prec0 (chowDerangement A n) (chowDerangement A (n + 1)) := by
  let resolution := BrandenLeite.resolutionOfTotallyNonneg A hunit hA
  have hpairs := resolvedChowWeightSum_endpoint_pairs resolution n
  have hext := hpairs.2.chowSExtension
  have hFdeg : (resolvedChowWeightSum resolution n).natDegree ≤ n :=
    hpairs.2.natDegree_le (by simp)
  have hrefS :
      (chowS n (resolvedChowWeightSum resolution n)).reflect n =
        X * chowS n (resolvedChowWeightSum resolution n) :=
    reflect_chowS n (resolvedChowWeightSum resolution n) hFdeg
  have hprec := hext.closedSequence.interlacingSeq0.prec0
    (i := (⟨2, by simp [reflectionClosure]⟩ :
      Fin (reflectionClosure n
        [chowS n (resolvedChowWeightSum resolution n),
          resolvedChowWeightSum resolution n,
          resolvedChowDerangement resolution n n,
          X * chowS n (resolvedChowDerangement resolution n n) +
            resolvedChowDerangement resolution n n]).length))
    (j := (⟨7, by simp [reflectionClosure]⟩ :
      Fin (reflectionClosure n
        [chowS n (resolvedChowWeightSum resolution n),
          resolvedChowWeightSum resolution n,
          resolvedChowDerangement resolution n n,
          X * chowS n (resolvedChowDerangement resolution n n) +
            resolvedChowDerangement resolution n n]).length)) (by simp)
  rw [chowDerangement_succ_eq_resolvedChowWeightSum resolution n]
  simpa [reflectionClosure, hrefS] using hprec

/-- Strict consecutive Chow-derangement relation under explicit
nonvanishing hypotheses. -/
theorem chowDerangement_prec_succ_of_isTotallyNonneg_of_ne
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular A)
    (hA : Matrix.IsTotallyNonneg A) (n : ℕ)
    (hn : chowDerangement A n ≠ 0)
    (hsucc : chowDerangement A (n + 1) ≠ 0) :
    Prec (chowDerangement A n) (chowDerangement A (n + 1)) :=
  (chowDerangement_prec0_succ_of_isTotallyNonneg hunit hA n).toPrec_of_ne
    hn hsucc

end

end RealRooted.BrandenVecchi
