import RealRooted.AffineFamily

open Polynomial

noncomputable section

namespace RealRooted

/-- Sparse handbook test family for the converse direction: `1` at `i`,
`α X + β` at `j`, and `0` elsewhere. -/
def sparseLinearPairSeq (n : ℕ) (i j : Fin n) (a b : ℝ) : List ℝ[X] :=
  List.ofFn (fun k : Fin n =>
    if k = i then (1 : ℝ[X]) else if k = j then C a * X + C b else 0)

@[simp] lemma length_sparseLinearPairSeq (n : ℕ) (i j : Fin n) (a b : ℝ) :
    (sparseLinearPairSeq n i j a b).length = n := by
  simp [sparseLinearPairSeq]

lemma get_sparseLinearPairSeq {n : ℕ} (i j : Fin n) (a b : ℝ) (k : Fin n) :
    (sparseLinearPairSeq n i j a b).get
        ⟨k, by simp [length_sparseLinearPairSeq]⟩ =
      (if k = i then (1 : ℝ[X]) else if k = j then C a * X + C b else 0) := by
  simp [sparseLinearPairSeq]

lemma isInterlacingSeq0Nonneg_sparseLinearPairSeq
    {n : ℕ} {i j : Fin n} (hij : i < j) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsInterlacingSeq0Nonneg (sparseLinearPairSeq n i j a b) := by
  constructor
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro p q hpq
    let p' : Fin n := ⟨p, by simpa [length_sparseLinearPairSeq] using p.2⟩
    let q' : Fin n := ⟨q, by simpa [length_sparseLinearPairSeq] using q.2⟩
    have : p' < q' := by grind
    rw [show (sparseLinearPairSeq n i j a b).get p =
          (if p' = i then (1 : ℝ[X]) else if p' = j then C a * X + C b else 0) by
          simpa [p'] using get_sparseLinearPairSeq i j a b p']
    rw [show (sparseLinearPairSeq n i j a b).get q =
          (if q' = i then (1 : ℝ[X]) else if q' = j then C a * X + C b else 0) by
          simpa [q'] using get_sparseLinearPairSeq i j a b q']
    by_cases hpi : p' = i
    · have hq_ne_i : q' ≠ i := by lia
      by_cases hqj : q' = j
      · have hji : j ≠ i := ne_of_gt hij
        simpa [hpi, hqj, hji] using prec0_one_affine_linear ha
      · simp [hpi, hqj, hq_ne_i, prec0_zero_right]
    · by_cases hpj : p' = j
      · have hq_ne_i : q' ≠ i := by lia
        have hq_ne_j : q' ≠ j := by lia
        simp [hpj, hq_ne_i, hq_ne_j, prec0_zero_right]
      · simp [hpi, hpj, prec0_zero_left]
  · rw [List.forall_mem_iff_get]
    intro k
    let k' : Fin n := ⟨k, by simpa [length_sparseLinearPairSeq] using k.2⟩
    rw [show (sparseLinearPairSeq n i j a b).get k =
          (if k' = i then (1 : ℝ[X]) else if k' = j then C a * X + C b else 0) by
          simpa [k'] using get_sparseLinearPairSeq i j a b k']
    by_cases hki : k' = i
    · simp [hki, hasNonnegCoeffs_one]
    · by_cases hkj : k' = j
      · have hji : j ≠ i := by lia
        simp [hkj, hji, hasNonnegCoeffs_affine_linear ha.le hb.le]
      · simp [hki, hkj, hasNonnegCoeffs_zero]

/-- Single-support weak test family for the converse: `1` at `i` and `0`
elsewhere. -/
def oneSupportSeq (n : ℕ) (i : Fin n) : List ℝ[X] :=
  List.ofFn (fun k : Fin n => if k = i then (1 : ℝ[X]) else 0)

@[simp] lemma length_oneSupportSeq (n : ℕ) (i : Fin n) :
    (oneSupportSeq n i).length = n := by
  simp [oneSupportSeq]

lemma get_oneSupportSeq {n : ℕ} (i k : Fin n) :
    (oneSupportSeq n i).get
        ⟨k, by simp [length_oneSupportSeq]⟩ =
      (if k = i then (1 : ℝ[X]) else 0) := by
  simp [oneSupportSeq]

lemma isInterlacingSeq0Nonneg_oneSupportSeq {n : ℕ} (i : Fin n) :
    IsInterlacingSeq0Nonneg (oneSupportSeq n i) := by
  constructor
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro p q hpq
    let p' : Fin n := ⟨p, by simpa [length_oneSupportSeq] using p.2⟩
    let q' : Fin n := ⟨q, by simpa [length_oneSupportSeq] using q.2⟩
    have : p' < q' := by grind
    rw [show (oneSupportSeq n i).get p =
          (if p' = i then (1 : ℝ[X]) else 0) by
          simpa [p'] using get_oneSupportSeq i p']
    rw [show (oneSupportSeq n i).get q =
          (if q' = i then (1 : ℝ[X]) else 0) by
          simpa [q'] using get_oneSupportSeq i q']
    by_cases hpi : p' = i
    · have hqi : q' ≠ i := by lia
      simp [hpi, hqi, prec0_zero_right]
    · by_cases hqi : q' = i <;> simp [hpi, hqi, prec0_zero_left]
  · rw [List.forall_mem_iff_get]
    intro k
    let k' : Fin n := ⟨k, by simpa [length_oneSupportSeq] using k.2⟩
    rw [show (oneSupportSeq n i).get k =
          (if k' = i then (1 : ℝ[X]) else 0) by
          simpa [k'] using get_oneSupportSeq i k']
    by_cases hki : k' = i <;> simp [hki, hasNonnegCoeffs_one, hasNonnegCoeffs_zero]

lemma zipWith_mul_replicate_zero_sum_eq_zero (row : List ℝ[X]) :
    ((row.zipWith (· * ·) (List.replicate row.length (0 : ℝ[X]))).sum) = 0 := by
  induction row <;> simp [List.replicate, *]

lemma zipWith_mul_oneSupportSeq_sum_eq_get
    (row : List ℝ[X]) (i : Fin row.length) :
    ((row.zipWith (· * ·) (oneSupportSeq row.length i)).sum) = row.get i := by
  induction row with
  | nil =>
      grind
  | cons a row ih =>
      cases i using Fin.cases with
      | zero =>
          simp [oneSupportSeq, List.ofFn_succ, zipWith_mul_replicate_zero_sum_eq_zero]
      | succ i =>
          have hne : ¬ ((0 : Fin (row.length + 1)) = i.succ) :=
            fun h => Fin.succ_ne_zero i h.symm
          simpa [oneSupportSeq, List.ofFn_succ, hne] using ih i

lemma zipWith_mul_sum_zipWith_add_right
    (row fs gs : List ℝ[X]) :
    fs.length = row.length →
    gs.length = row.length →
    ((row.zipWith (· * ·) (fs.zipWith (· + ·) gs)).sum)
      = ((row.zipWith (· * ·) fs).sum) + ((row.zipWith (· * ·) gs).sum) :=
  fun hfs_len hgs_len => by
  induction row generalizing fs gs with
  | nil =>
      simp
  | cons a row ih =>
      cases fs with
      | nil =>
          simp at hfs_len
      | cons f fs =>
          cases gs with
          | nil =>
              simp at hgs_len
          | cons g gs =>
              simp only [List.length_cons, Nat.succ.injEq] at hfs_len hgs_len
              simp [mul_add, ih _ _ hfs_len hgs_len, add_assoc, add_left_comm]

lemma zipWith_mul_sum_map_mul_right
    (c : ℝ[X]) (row fs : List ℝ[X]) :
    ((row.zipWith (· * ·) (fs.map (fun q => c * q))).sum)
      = c * ((row.zipWith (· * ·) fs).sum) := by
  induction row generalizing fs with
  | nil => simp
  | cons a row ih =>
    cases fs with
    | nil => simp
    | cons f fs => simp [ih, mul_add, mul_left_comm]

lemma sparseLinearPairSeq_eq_zipWith_oneSupport
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    sparseLinearPairSeq n i j a b
      = (oneSupportSeq n i).zipWith (· + ·)
          ((oneSupportSeq n j).map (fun q => (C a * X + C b) * q)) := by
  apply List.ext_get
  · simp
  · intro k hk1 hk2
    let k' : Fin n := ⟨k, by simp_all⟩
    rw [show (sparseLinearPairSeq n i j a b).get ⟨k, hk1⟩
          = (if k' = i then (1 : ℝ[X]) else if k' = j then C a * X + C b else 0) by
          simpa [k'] using get_sparseLinearPairSeq i j a b k']
    rw [show ((oneSupportSeq n i).zipWith (· + ·)
          ((oneSupportSeq n j).map (fun q => (C a * X + C b) * q))).get ⟨k, hk2⟩
          = (oneSupportSeq n i).get ⟨k, by simp_all⟩
              + (((oneSupportSeq n j).map (fun q => (C a * X + C b) * q)).get
                  ⟨k, by simp_all⟩) by
          simp]
    rw [show (oneSupportSeq n i).get ⟨k, by simp_all⟩
          = (if k' = i then (1 : ℝ[X]) else 0) by
          simpa [k'] using get_oneSupportSeq i k']
    rw [show ((oneSupportSeq n j).map (fun q => (C a * X + C b) * q)).get
          ⟨k, by simp_all⟩
          = (C a * X + C b)
              * (if k' = j then (1 : ℝ[X]) else 0) by
          simp [oneSupportSeq, k']]
    grind

lemma zipWith_mul_sparseLinearPairSeq_sum_eq
    (row : List ℝ[X]) (i j : Fin row.length) (hij : i ≠ j) (a b : ℝ) :
    ((row.zipWith (· * ·) (sparseLinearPairSeq row.length i j a b)).sum)
      = row.get i + (C a * X + C b) * row.get j := by
  rw [sparseLinearPairSeq_eq_zipWith_oneSupport i j hij a b,
    zipWith_mul_sum_zipWith_add_right]
  · rw [zipWith_mul_sum_map_mul_right]
    simp [zipWith_mul_oneSupportSeq_sum_eq_get, add_comm]
  · simp
  · simp

lemma zipWith_mul_sparseLinearPairSeq_sum_eq_of_length
    (row : List ℝ[X]) (hrow_len : row.length = n)
    (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    ((row.zipWith (· * ·) (sparseLinearPairSeq n i j a b)).sum)
      = row.get ⟨i, by lia⟩
          + (C a * X + C b) * row.get ⟨j, by lia⟩ := by
  subst n
  simpa using zipWith_mul_sparseLinearPairSeq_sum_eq row i j hij a b


end RealRooted
