import RealRooted.AffineFamily

/-!
# Matrix preservation of interlacing sequences

Sparse pair machinery, `matPolyAction` definition, forward and backward
matrix-preservation theorems (Brändén, Theorem 7.8.5).
-/

open Polynomial

noncomputable section

namespace RealRooted

section

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
    have hpq' : p' < q' := by simpa [p', q'] using hpq
    rw [show (sparseLinearPairSeq n i j a b).get p =
          (if p' = i then (1 : ℝ[X]) else if p' = j then C a * X + C b else 0) by
          simpa [p'] using get_sparseLinearPairSeq i j a b p']
    rw [show (sparseLinearPairSeq n i j a b).get q =
          (if q' = i then (1 : ℝ[X]) else if q' = j then C a * X + C b else 0) by
          simpa [q'] using get_sparseLinearPairSeq i j a b q']
    by_cases hpi : p' = i
    · have hq_ne_i : q' ≠ i := by
        intro hq
        have : i < i := by simp [hpi, hq] at hpq'
        exact (lt_irrefl i) this
      by_cases hqj : q' = j
      · have hji : j ≠ i := ne_of_gt hij
        simpa [hpi, hqj, hji] using prec0_one_affine_linear ha hb
      · simp [hpi, hqj, hq_ne_i, prec0_zero_right]
    · by_cases hpj : p' = j
      · have hq_ne_i : q' ≠ i := by
          intro hq
          have : j < i := by simpa [hpj, hq] using hpq'
          exact (not_lt_of_gt hij) this
        have hq_ne_j : q' ≠ j := by
          intro hq
          have : j < j := by simp [hpj, hq] at hpq'
          exact (lt_irrefl _ this).elim
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
      · have hji : j ≠ i := by
          intro hji
          apply hki
          simpa [hkj] using hji
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
    have hpq' : p' < q' := by simpa [p', q'] using hpq
    rw [show (oneSupportSeq n i).get p =
          (if p' = i then (1 : ℝ[X]) else 0) by
          simpa [p'] using get_oneSupportSeq i p']
    rw [show (oneSupportSeq n i).get q =
          (if q' = i then (1 : ℝ[X]) else 0) by
          simpa [q'] using get_oneSupportSeq i q']
    by_cases hpi : p' = i
    · have hqi : q' ≠ i := by
        intro hq
        have : i < i := by simp [hpi, hq] at hpq'
        exact (lt_irrefl i) this
      simp [hpi, hqi, prec0_zero_right]
    · by_cases hqi : q' = i
      · simp [hpi, hqi, prec0_zero_left]
      · simp [hpi, hqi, prec0_zero_left]
  · rw [List.forall_mem_iff_get]
    intro k
    let k' : Fin n := ⟨k, by simpa [length_oneSupportSeq] using k.2⟩
    rw [show (oneSupportSeq n i).get k =
          (if k' = i then (1 : ℝ[X]) else 0) by
          simpa [k'] using get_oneSupportSeq i k']
    by_cases hki : k' = i
    · simp [hki, hasNonnegCoeffs_one]
    · simp [hki, hasNonnegCoeffs_zero]

lemma zipWith_mul_replicate_zero_sum_eq_zero (row : List ℝ[X]) :
    ((row.zipWith (· * ·) (List.replicate row.length (0 : ℝ[X]))).sum) = 0 := by
  induction row with
  | nil =>
      simp
  | cons a row ih =>
      simp [List.replicate, ih]

lemma zipWith_mul_oneSupportSeq_sum_eq_get
    (row : List ℝ[X]) (i : Fin row.length) :
    ((row.zipWith (· * ·) (oneSupportSeq row.length i)).sum) = row.get i := by
  induction row with
  | nil =>
      exact (Nat.not_lt_zero _ i.2).elim
  | cons a row ih =>
      cases i using Fin.cases with
      | zero =>
          simp [oneSupportSeq, List.ofFn_succ, zipWith_mul_replicate_zero_sum_eq_zero]
      | succ i =>
          have hne : ¬ ((0 : Fin (row.length + 1)) = i.succ) := by
            intro h
            cases h
          simpa [oneSupportSeq, List.ofFn_succ, hne] using ih i

lemma zipWith_mul_sum_ne_zero_of_get_ne_zero
    {row fs : List ℝ[X]}
    (hlen : row.length = fs.length)
    (hrow_nonneg : ∀ p ∈ row, HasNonnegCoeffs p)
    (hfs_nonneg : ∀ p ∈ fs, HasNonnegCoeffs p)
    (i : Fin row.length)
    (hrowi_ne : row.get i ≠ 0)
    (hfsi_ne : fs.get ⟨i.1, by simpa [hlen] using i.2⟩ ≠ 0) :
    ((row.zipWith (· * ·) fs).sum) ≠ 0 := by
  have hmem :
      row.get i * fs.get ⟨i.1, by simpa [hlen] using i.2⟩ ∈ row.zipWith (· * ·) fs :=
    mem_zipWith_mul_get hlen i
  have hprod_ne :
      row.get i * fs.get ⟨i.1, by simpa [hlen] using i.2⟩ ≠ 0 :=
    mul_ne_zero hrowi_ne hfsi_ne
  exact
    zipWith_mul_sum_ne_zero_of_mem_ne_zero
      hrow_nonneg hfs_nonneg hmem hprod_ne

lemma zipWith_mul_sum_zipWith_add_right
    (row fs gs : List ℝ[X]) :
    fs.length = row.length →
    gs.length = row.length →
    ((row.zipWith (· * ·) (fs.zipWith (· + ·) gs)).sum)
      = ((row.zipWith (· * ·) fs).sum) + ((row.zipWith (· * ·) gs).sum) := by
  intro hfs_len hgs_len
  induction row generalizing fs gs with
  | nil =>
      cases fs <;> cases gs <;> simp at hfs_len hgs_len ⊢
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
  | nil =>
      cases fs <;> simp
  | cons a row ih =>
      cases fs with
      | nil =>
          simp
      | cons f fs =>
          simp [ih, mul_add, mul_left_comm]

lemma sparseLinearPairSeq_eq_zipWith_oneSupport
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    sparseLinearPairSeq n i j a b
      = (oneSupportSeq n i).zipWith (· + ·)
          ((oneSupportSeq n j).map (fun q => (C a * X + C b) * q)) := by
  apply List.ext_get
  · simp [sparseLinearPairSeq, oneSupportSeq]
  · intro k hk1 hk2
    let k' : Fin n := ⟨k, by simpa [sparseLinearPairSeq] using hk1⟩
    rw [show (sparseLinearPairSeq n i j a b).get ⟨k, hk1⟩
          = (if k' = i then (1 : ℝ[X]) else if k' = j then C a * X + C b else 0) by
          simpa [k'] using get_sparseLinearPairSeq i j a b k']
    rw [show ((oneSupportSeq n i).zipWith (· + ·)
          ((oneSupportSeq n j).map (fun q => (C a * X + C b) * q))).get ⟨k, hk2⟩
          = (oneSupportSeq n i).get ⟨k, by simpa [oneSupportSeq] using hk2⟩
              + (((oneSupportSeq n j).map (fun q => (C a * X + C b) * q)).get
                  ⟨k, by simpa [oneSupportSeq] using hk2⟩) by
          simp]
    rw [show (oneSupportSeq n i).get ⟨k, by simpa [oneSupportSeq] using hk2⟩
          = (if k' = i then (1 : ℝ[X]) else 0) by
          simpa [k'] using get_oneSupportSeq i k']
    rw [show ((oneSupportSeq n j).map (fun q => (C a * X + C b) * q)).get
          ⟨k, by simpa [oneSupportSeq] using hk2⟩
          = (C a * X + C b)
              * (if k' = j then (1 : ℝ[X]) else 0) by
          simp [oneSupportSeq, k']]
    by_cases hki : k' = i
    · have hkj : k' ≠ j := by
        intro hkj
        exact hij (hki.symm.trans hkj)
      have hij' : i ≠ j := by
        intro hij'
        exact hkj (hki.trans hij')
      simp [hki, hij']
    · by_cases hkj : k' = j
      · have hji : j ≠ i := by
          intro hji
          exact hki (hkj.trans hji)
        simp [hkj, hji]
      · simp [hki, hkj]

lemma zipWith_mul_sparseLinearPairSeq_sum_eq
    (row : List ℝ[X]) (i j : Fin row.length) (hij : i ≠ j) (a b : ℝ) :
    ((row.zipWith (· * ·) (sparseLinearPairSeq row.length i j a b)).sum)
      = row.get i + (C a * X + C b) * row.get j := by
  rw [sparseLinearPairSeq_eq_zipWith_oneSupport i j hij a b]
  rw [zipWith_mul_sum_zipWith_add_right]
  · rw [zipWith_mul_sum_map_mul_right]
    simp [zipWith_mul_oneSupportSeq_sum_eq_get, add_comm]
  · simp
  · simp

lemma zipWith_mul_sparseLinearPairSeq_sum_eq_of_length
    (row : List ℝ[X]) (hrow_len : row.length = n)
    (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    ((row.zipWith (· * ·) (sparseLinearPairSeq n i j a b)).sum)
      = row.get ⟨i, by simp [hrow_len]⟩
          + (C a * X + C b) * row.get ⟨j, by simp [hrow_len]⟩ := by
  subst n
  simpa using zipWith_mul_sparseLinearPairSeq_sum_eq row i j hij a b


/-- A matrix of polynomials acts on a sequence by matrix-vector multiplication. -/
def matPolyAction (G : List (List ℝ[X])) (fs : List ℝ[X]) : List ℝ[X] :=
  G.map (fun row => (row.zipWith (· * ·) fs).sum)

/-- Weak zero-aware converse, entrywise nonnegativity half.

This is the clean handbook-style target for recovering condition (1) from a
matrix action hypothesis in the presence of zero polynomials. The intended proof
uses single-support test vectors (`1` in one position, `0` elsewhere), which do
not belong to the current strict `IsInterlacingSeqNonneg` family but do belong
to the weak `IsInterlacingSeq0Nonneg` family introduced above. -/
theorem matrix_preserves_interlacing_seq0_nonneg_entries
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs)) :
    ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hp
  let fs := oneSupportSeq row.length i
  have hfs_len : fs.length = n := by
    simp [fs, hG_rect _ hrow]
  have hfs : IsInterlacingSeq0Nonneg fs := by
    simpa [fs] using isInterlacingSeq0Nonneg_oneSupportSeq i
  have himage : IsInterlacingSeq0Nonneg (matPolyAction G fs) := hpres0 fs hfs_len hfs
  have himage_nonneg : ∀ q ∈ matPolyAction G fs, HasNonnegCoeffs q := himage.2
  have hrow_eval :
      (row.zipWith (· * ·) fs).sum = row.get i := by
    simpa [fs] using zipWith_mul_oneSupportSeq_sum_eq_get row i
  have hmem_eval : (row.zipWith (· * ·) fs).sum ∈ matPolyAction G fs := by
    exact List.mem_map.2 ⟨row, hrow, rfl⟩
  simpa [hrow_eval] using himage_nonneg _ hmem_eval

theorem matrix_preserves_interlacing_seq0_sparse_pair_prec0
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs))
    (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n)
    (hi : i₁ < i₂) (hj : j₁ < j₂)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Prec0
      (((G.get i₁).get ⟨j₁, by have := hG_rect _ (G.get_mem i₁); lia⟩
          + (C a * X + C b)
            * ((G.get i₁).get ⟨j₂, by have := hG_rect _ (G.get_mem i₁); lia⟩)))
      (((G.get i₂).get ⟨j₁, by have := hG_rect _ (G.get_mem i₂); lia⟩
          + (C a * X + C b)
            * ((G.get i₂).get ⟨j₂, by have := hG_rect _ (G.get_mem i₂); lia⟩))) := by
  let fs := sparseLinearPairSeq n j₁ j₂ a b
  have hfs_len : fs.length = n := by
    simp [fs]
  have hfs : IsInterlacingSeq0Nonneg fs := by
    simpa [fs] using isInterlacingSeq0Nonneg_sparseLinearPairSeq hj ha hb
  have himage : IsInterlacingSeq0Nonneg (matPolyAction G fs) := hpres0 fs hfs_len hfs
  let iG : Fin (matPolyAction G fs).length := ⟨i₁, by simp [matPolyAction]⟩
  let iRowJ₁ : Fin (G.get i₁).length := ⟨j₁, by have := hG_rect _ (G.get_mem i₁); lia⟩
  let iRowJ₂ : Fin (G.get i₁).length := ⟨j₂, by have := hG_rect _ (G.get_mem i₁); lia⟩
  let jG : Fin (matPolyAction G fs).length := ⟨i₂, by simp [matPolyAction]⟩
  let jRowJ₁ : Fin (G.get i₂).length := ⟨j₁, by have := hG_rect _ (G.get_mem i₂); lia⟩
  let jRowJ₂ : Fin (G.get i₂).length := ⟨j₂, by have := hG_rect _ (G.get_mem i₂); lia⟩
  have hpair : Prec0 ((matPolyAction G fs).get iG) ((matPolyAction G fs).get jG) := by
    exact himage.1.prec0 (i := iG) (j := jG) (by simpa [iG, jG] using hi)
  have hleft :
      (matPolyAction G fs).get iG
        = (G.get i₁).get iRowJ₁ + (C a * X + C b) * (G.get i₁).get iRowJ₂ := by
    simpa [matPolyAction, fs, iG, iRowJ₁, iRowJ₂] using
      zipWith_mul_sparseLinearPairSeq_sum_eq_of_length
        (row := G.get i₁) (n := n) (hrow_len := hG_rect _ (G.get_mem i₁))
        j₁ j₂ (ne_of_lt hj) a b
  have hright :
      (matPolyAction G fs).get jG
        = (G.get i₂).get jRowJ₁ + (C a * X + C b) * (G.get i₂).get jRowJ₂ := by
    simpa [matPolyAction, fs, jG, jRowJ₁, jRowJ₂] using
      zipWith_mul_sparseLinearPairSeq_sum_eq_of_length
        (row := G.get i₂) (n := n) (hrow_len := hG_rect _ (G.get_mem i₂))
        j₁ j₂ (ne_of_lt hj) a b
  rwa [hleft, hright] at hpair

/-- Weak handbook-style converse package: a matrix preserving the zero-aware
family `𝓕ₙ⁰⁺` must have entrywise nonnegative coefficients, and its 2×2 affine
sparse test images satisfy the corresponding weak `Prec0` relation. -/
theorem matrix_preserves_interlacing_seq0_necessary_conditions
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs)) :
    (∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p) ∧
    (∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ < i₂ → j₁ < j₂ →
      ∀ {a b : ℝ}, 0 < a → 0 < b →
      Prec0
        (((G.get i₁).get ⟨j₁, by
            have := hG_rect _ (G.get_mem i₁)
            lia⟩)
          + (C a * X + C b) * ((G.get i₁).get ⟨j₂, by
            have := hG_rect _ (G.get_mem i₁)
            lia⟩))
        (((G.get i₂).get ⟨j₁, by
            have := hG_rect _ (G.get_mem i₂)
            lia⟩)
          + (C a * X + C b) * ((G.get i₂).get ⟨j₂, by
            have := hG_rect _ (G.get_mem i₂)
            lia⟩))) := by
  refine ⟨?_, ?_⟩
  · exact matrix_preserves_interlacing_seq0_nonneg_entries (n := n) G hG_rect hpres0
  · intro i₁ i₂ j₁ j₂ hi hj a b ha hb
    exact matrix_preserves_interlacing_seq0_sparse_pair_prec0
      (n := n) G hG_rect hpres0 i₁ i₂ j₁ j₂ hi hj ha hb

/-- Auxiliary column family in Brändén's forward matrix proof:
for fixed `s, t`, the `j`th entry is `((C s * X + C t) * row₁[j]) + row₂[j]`. -/
def rowPairAffineSeq (row₁ row₂ : List ℝ[X]) (s t : ℝ) : List ℝ[X] :=
  row₁.zipWith (fun p q => ((C s * X + C t) * p) + q) row₂

lemma length_rowPairAffineSeq {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n) (hrow₂_len : row₂.length = n) :
    (rowPairAffineSeq row₁ row₂ s t).length = n := by
  simp [rowPairAffineSeq, List.length_zipWith, hrow₁_len, hrow₂_len]

lemma get_rowPairAffineSeq {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n) (hrow₂_len : row₂.length = n)
    (i : Fin n) :
    (rowPairAffineSeq row₁ row₂ s t).get
        ⟨i, by
          simp [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len
            hrow₂_len]⟩
      =
        ((C s * X + C t) * row₁.get ⟨i, by simp [hrow₁_len]⟩) +
          row₂.get ⟨i, by simp [hrow₂_len]⟩ := by
  simp [rowPairAffineSeq, List.get_eq_getElem]

lemma isInterlacingSeq0_reverse_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ < j₂ →
      Has2x2InterlacingProperty0
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsInterlacingSeq0 (rowPairAffineSeq row₁ row₂ s t).reverse := by
  rw [isInterlacingSeq0_iff_pairwise]
  refine (List.Pairwise.reverse ?_)
  refine List.pairwise_iff_get.2 ?_
  intro i j hij
  let i' : Fin n :=
    ⟨i, by
      simpa [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len
        hrow₂_len] using i.2⟩
  let j' : Fin n :=
    ⟨j, by
      simpa [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len
        hrow₂_len] using j.2⟩
  have hij' : i' < j' := by
    simpa [i', j'] using hij
  rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len i']
  rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len j']
  exact h2x2 i' j' hij' s t hs ht

lemma isInterlacingSeq_reverse_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ < j₂ →
      Has2x2InterlacingProperty
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsInterlacingSeq (rowPairAffineSeq row₁ row₂ s t).reverse := by
  rw [isInterlacingSeq_iff_pairwise]
  refine (List.Pairwise.reverse ?_ )
  refine List.pairwise_iff_get.2 ?_
  intro i j hij
  let i' : Fin n :=
    ⟨i, by
      simpa [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len
        hrow₂_len] using i.2⟩
  let j' : Fin n :=
    ⟨j, by
      simpa [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len
        hrow₂_len] using j.2⟩
  have hij' : i' < j' := by
    simpa [i', j'] using hij
  rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len i']
  rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len j']
  exact h2x2 i' j' hij' s t hs ht

lemma isRealRooted_mem_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (h2x2_diag : ∀ (j : Fin n),
      Has2x2InterlacingProperty
        (row₁.get ⟨j, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (p : ℝ[X]) (hp : p ∈ (rowPairAffineSeq row₁ row₂ s t).reverse) :
    (p ≠ 0 ∧ p.roots.card = p.natDegree) := by
  have hp' : p ∈ rowPairAffineSeq row₁ row₂ s t := by
    simpa using List.mem_reverse.1 hp
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hp'
  let j' : Fin n := ⟨j, by
    simpa [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len] using j.2⟩
  let j₁' : Fin row₁.length := ⟨j', by simp [hrow₁_len]⟩
  let j₂' : Fin row₂.length := ⟨j', by simp [hrow₂_len]⟩
  have hself :
      Prec
        (((C s * X + C t) * row₁.get j₁') + row₂.get j₂')
        (((C s * X + C t) * row₁.get j₁') + row₂.get j₂') := by
    simpa using h2x2_diag j' s t hs ht
  rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len j']
  simpa [j₁', j₂'] using hself.1

lemma isRealRooted_mem_rowPairAffineSeq_of_ne
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (h2x2_diag : ∀ (j : Fin n),
      Has2x2InterlacingProperty0
        (row₁.get ⟨j, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (p : ℝ[X]) (hp : p ∈ (rowPairAffineSeq row₁ row₂ s t).reverse)
    (hp_ne : p ≠ 0) :
    (p ≠ 0 ∧ p.roots.card = p.natDegree) := by
  have hp' : p ∈ rowPairAffineSeq row₁ row₂ s t := by
    simpa using List.mem_reverse.1 hp
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hp'
  let j' : Fin n := ⟨j, by
    simpa [length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len] using j.2⟩
  let j₁' : Fin row₁.length := ⟨j', by simp [hrow₁_len]⟩
  let j₂' : Fin row₂.length := ⟨j', by simp [hrow₂_len]⟩
  have hentry_ne :
      (((C s * X + C t) * row₁.get j₁') + row₂.get j₂') ≠ 0 := by
    intro hzero
    apply hp_ne
    rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len j']
    simpa [j₁', j₂'] using hzero
  have hself0 :
      Prec0
        (((C s * X + C t) * row₁.get j₁') + row₂.get j₂')
        (((C s * X + C t) * row₁.get j₁') + row₂.get j₂') := by
    simpa using h2x2_diag j' s t hs ht
  have hself : Prec
      (((C s * X + C t) * row₁.get j₁') + row₂.get j₂')
      (((C s * X + C t) * row₁.get j₁') + row₂.get j₂') :=
    hself0.toPrec_of_ne hentry_ne hentry_ne
  rw [get_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len j']
  simpa [j₁', j₂'] using hself.1

lemma hasNonnegCoeffs_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ p ∈ rowPairAffineSeq row₁ row₂ s t, HasNonnegCoeffs p := by
  induction row₁ generalizing row₂ with
  | nil =>
      intro p hp
      cases row₂ <;> simp [rowPairAffineSeq] at hp
  | cons a row₁ ih =>
      cases row₂ with
      | nil =>
          intro p hp
          simp [rowPairAffineSeq] at hp
      | cons b row₂ =>
          intro p hp
          simp only [rowPairAffineSeq, List.zipWith_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · have ha : HasNonnegCoeffs a := hrow₁_nonneg a (by simp)
            have hb : HasNonnegCoeffs b := hrow₂_nonneg b (by simp)
            have hsa : HasNonnegCoeffs (C s * (X * a)) :=
              nonnegCoeffs_C_mul hs (hasNonnegCoeffs_X.mul ha)
            have hta : HasNonnegCoeffs (C t * a) :=
              nonnegCoeffs_C_mul ht ha
            have hsum : HasNonnegCoeffs (C s * (X * a) + (C t * a + b)) :=
              hsa.add (hta.add hb)
            simpa [left_distrib, right_distrib, mul_add, mul_assoc, add_assoc, add_left_comm,
              add_comm] using hsum
          · exact
              ih
                (fun q hq => hrow₁_nonneg q (by simp [hq]))
                (fun q hq => hrow₂_nonneg q (by simp [hq]))
                p hp

/-- For fixed positive `s, t`, the auxiliary affine row family coming from two
matrix rows is an interlacing sequence whose members have nonnegative
coefficients after reversing to the handbook orientation. This is the exact
auxiliary-family package used in the forward matrix proof; it is intentionally
weaker than membership in `𝓕ₙ⁺`, since these affine row entries need not be
individually real-rooted. -/
lemma isInterlacingSeqAndNonneg_reverse_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ < j₂ →
      Has2x2InterlacingProperty
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsInterlacingSeq ((rowPairAffineSeq row₁ row₂ s t).reverse) ∧
      ∀ p ∈ (rowPairAffineSeq row₁ row₂ s t).reverse, HasNonnegCoeffs p := by
  refine ⟨?_, ?_⟩
  · exact
      isInterlacingSeq_reverse_rowPairAffineSeq
        (n := n) (row₁ := row₁) (row₂ := row₂)
        hrow₁_len hrow₂_len h2x2 hs ht
  · intro p hp
    have hp' : p ∈ rowPairAffineSeq row₁ row₂ s t := by
      simpa using List.mem_reverse.1 hp
    exact
      hasNonnegCoeffs_rowPairAffineSeq
        (row₁ := row₁) (row₂ := row₂)
        hrow₁_nonneg hrow₂_nonneg hs.le ht.le p hp'

lemma isInterlacingSeq0Nonneg_reverse_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ < j₂ →
      Has2x2InterlacingProperty0
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsInterlacingSeq0Nonneg ((rowPairAffineSeq row₁ row₂ s t).reverse) := by
  refine ⟨?_, ?_⟩
  · exact
      isInterlacingSeq0_reverse_rowPairAffineSeq
        (n := n) (row₁ := row₁) (row₂ := row₂)
        hrow₁_len hrow₂_len h2x2 hs ht
  · intro p hp
    have hp' : p ∈ rowPairAffineSeq row₁ row₂ s t := by
      simpa using List.mem_reverse.1 hp
    exact
      hasNonnegCoeffs_rowPairAffineSeq
        (row₁ := row₁) (row₂ := row₂)
        hrow₁_nonneg hrow₂_nonneg hs.le ht.le p hp'

lemma isInterlacingSeqNonneg_reverse_rowPairAffineSeq
    {row₁ row₂ : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsInterlacingSeqNonneg ((rowPairAffineSeq row₁ row₂ s t).reverse) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_⟩
    · exact
        isRealRooted_mem_rowPairAffineSeq
          (n := n) hrow₁_len hrow₂_len
          (fun j => h2x2 j j le_rfl) hs ht p hp
    · exact
        (isInterlacingSeqAndNonneg_reverse_rowPairAffineSeq
          (n := n) (row₁ := row₁) (row₂ := row₂)
          hrow₁_len hrow₂_len hrow₁_nonneg hrow₂_nonneg
          (fun j₁ j₂ hj => h2x2 j₁ j₂ (le_of_lt hj)) hs ht).2 p hp
  · exact
      (isInterlacingSeqAndNonneg_reverse_rowPairAffineSeq
        (n := n) (row₁ := row₁) (row₂ := row₂)
        hrow₁_len hrow₂_len hrow₁_nonneg hrow₂_nonneg
        (fun j₁ j₂ hj => h2x2 j₁ j₂ (le_of_lt hj)) hs ht).1

/-- Mechanical expansion of the affine row combination used in the forward
matrix theorem. -/
lemma rowPairAffine_combo_eq_zipWith_sum
    {row₁ row₂ fs : List ℝ[X]} {s t : ℝ}
    (hrows : row₁.length = row₂.length) :
    ((C s * X + C t) * ((row₁.zipWith (· * ·) fs).sum)) + ((row₂.zipWith (· * ·) fs).sum)
      = ((rowPairAffineSeq row₁ row₂ s t).zipWith (· * ·) fs).sum := by
  induction row₁ generalizing row₂ fs with
  | nil =>
      cases row₂ with
      | nil =>
          cases fs <;> simp [rowPairAffineSeq]
      | cons b row₂ =>
          simp at hrows
  | cons a row₁ ih =>
      cases row₂ with
      | nil =>
          simp at hrows
      | cons b row₂ =>
          have hrows' : row₁.length = row₂.length := by
            simpa using Nat.succ.inj hrows
          cases fs with
          | nil =>
              simp [rowPairAffineSeq]
          | cons f fs =>
              calc
                ((C s * X + C t) * ((a * f) + ((row₁.zipWith (· * ·) fs).sum))) +
                    ((b * f) + ((row₂.zipWith (· * ·) fs).sum))
                    =
                    ((((C s * X + C t) * a) + b) * f) +
                      (((C s * X + C t) * ((row₁.zipWith (· * ·) fs).sum)) +
                        ((row₂.zipWith (· * ·) fs).sum)) := by
                          simp [mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm]
                _ =
                    ((((C s * X + C t) * a) + b) * f) +
                      (((rowPairAffineSeq row₁ row₂ s t).zipWith (· * ·) fs).sum) := by
                          rw [ih hrows']
                _ =
                    ((rowPairAffineSeq (a :: row₁) (b :: row₂) s t).zipWith
                      (· * ·) (f :: fs)).sum := by
                      simp [rowPairAffineSeq]

lemma zipWith_mul_sum_reverse_reverse
    {row fs : List ℝ[X]} (hlen : row.length = fs.length) :
    ((row.reverse.zipWith (· * ·) fs.reverse).sum) = ((row.zipWith (· * ·) fs).sum) := by
  rw [← List.reverse_zipWith (f := (· * ·)) hlen]
  simp

/-- Fixed-row form of the forward matrix theorem.

This is the point where Brändén's proof uses Lemma 7.8.3: from the 2×2
hypothesis one gets an interlacing auxiliary column family, and the
corresponding reversed product-sum against `fs` is real-rooted. The affine
family criterion above should then convert that real-rootedness statement to
`Prec` for the two row sums.

Note: in full generality this statement needs row-wise nondegeneracy input
(at least enough to exclude zero-row counterexamples). The current proof body
is the forward derivation up to the final affine-family-to-`Prec` conversion. -/
theorem prec_zipWith_sum_pair_of_2x2
    {row₁ row₂ fs : List ℝ[X]}
    (hn : 0 < n)
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (hrow₁_head_ne : row₁.get ⟨0, by simpa [hrow₁_len] using hn⟩ ≠ 0)
    (hrow₂_head_ne : row₂.get ⟨0, by simpa [hrow₂_len] using hn⟩ ≠ 0)
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    Prec ((row₁.zipWith (· * ·) fs).sum) ((row₂.zipWith (· * ·) fs).sum) := by
  let auxRow := rowPairAffineSeq row₁ row₂
  have hrows : row₁.length = row₂.length := by rw [hrow₁_len, hrow₂_len]
  /-
  The new local affine-row helpers reduce the theorem to one concrete missing
  statement: for every `s,t > 0`, the reversed product-sum

    `((auxRow s t).zipWith (· * ·) fs).sum`

  is real-rooted. Everything else is now explicit bookkeeping.

  For fixed `s,t > 0`, set

    h_j := ((C s * X + C t) * row₁[j]) + row₂[j].

  By `h2x2`, the list `(h_j)` should be an interlacing sequence; by
  `hasNonnegCoeffs_rowPairAffineSeq` it has nonnegative coefficients. The
  affine combination of row sums is then exactly

    `((auxRow s t).zipWith (· * ·) fs).sum`

  by `rowPairAffine_combo_eq_zipWith_sum`. So the remaining gap is the local
  Brändén 7.8.3 product-sum theorem for two interlacing sequences.
  -/
  have haux_len : ∀ {s t : ℝ}, (auxRow s t).length = n := by
    intro s t
    simpa [auxRow] using length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len
  have haux_nonneg :
      ∀ {s t : ℝ}, 0 ≤ s → 0 ≤ t → ∀ p ∈ auxRow s t, HasNonnegCoeffs p := by
    intro s t hs ht p hp
    simpa [auxRow] using
      hasNonnegCoeffs_rowPairAffineSeq
        (row₁ := row₁) (row₂ := row₂) hrow₁_nonneg hrow₂_nonneg hs ht p hp
  have hrewrite :
      ∀ {s t : ℝ},
        (C s * X + C t) * ((row₁.zipWith (· * ·) fs).sum)
          + ((row₂.zipWith (· * ·) fs).sum)
          = ((auxRow s t).zipWith (· * ·) fs).sum := by
    intro s t
    simpa [auxRow] using
      rowPairAffine_combo_eq_zipWith_sum
        (row₁ := row₁) (row₂ := row₂) (fs := fs) (s := s) (t := t) hrows
  have hfs_all : IsInterlacingSeqNonneg fs := hfs
  rcases hfs with ⟨hfs_mem, hfs_int⟩
  have hfs_nonneg : ∀ f ∈ fs, HasNonnegCoeffs f := by
    exact fun f hf => (hfs_mem f hf).2
  have hfs_ne : fs ≠ [] := by
    intro hnil
    rw [hnil] at hfs_len
    simp at hfs_len
    lia
  have haux_rr :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((auxRow s t).zipWith (· * ·) fs).sum) ≠ 0 ∧ (((auxRow s t).zipWith (· * ·) fs).sum).roots.card = (((auxRow s t).zipWith (· * ·) fs).sum).natDegree) := by
    intro s t hs ht
    have haux :
        IsInterlacingSeqNonneg ((auxRow s t).reverse) := by
      exact
        isInterlacingSeqNonneg_reverse_rowPairAffineSeq
          (n := n) hrow₁_len hrow₂_len hrow₁_nonneg hrow₂_nonneg h2x2 hs ht
    have hrr_rev :
        (((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum) ≠ 0 ∧ ((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum).roots.card = ((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum).natDegree) := by
      exact
        isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeqNonneg
          (fs := (auxRow s t).reverse) (gs := fs)
          (by
            intro hnil
            have hnil' : auxRow s t = [] := by simpa using hnil
            have : n = 0 := by
              rw [← haux_len (s := s) (t := t), hnil']
              simp
            lia)
          (by simp [haux_len, hfs_len])
          haux hfs_all
    simpa [zipWith_mul_sum_reverse_reverse (row := auxRow s t) (fs := fs)
      (haux_len.trans hfs_len.symm)] using hrr_rev
  let F : ℝ[X] := ((row₁.zipWith (· * ·) fs).sum)
  let G : ℝ[X] := ((row₂.zipWith (· * ·) fs).sum)
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * F) + G) ≠ 0 ∧ (((C s * X + C t) * F) + G).roots.card = (((C s * X + C t) * F) + G).natDegree) := by
    intro s t hs ht
    simpa [F, G, hrewrite (s := s) (t := t)] using haux_rr (s := s) (t := t) hs ht
  have hposCombo :
      ∀ {t : ℝ}, 0 < t → PosComboRealRooted (C t * F + G) (X * F) := by
    intro t ht
    exact posComboRealRooted_of_affine_family (f := F) (g := G) haff (t := t) ht
  have hF_nonneg : HasNonnegCoeffs F := by
    simpa [F] using
      hasNonnegCoeffs_zipWith_mul_sum
        (hrow := hrow₁_nonneg) (hfs := hfs_nonneg)
  have hG_nonneg : HasNonnegCoeffs G := by
    simpa [G] using
      hasNonnegCoeffs_zipWith_mul_sum
        (hrow := hrow₂_nonneg) (hfs := hfs_nonneg)
  let j0 : Fin row₁.length := ⟨0, by simpa [hrow₁_len] using hn⟩
  let k0 : Fin row₂.length := ⟨0, by simpa [hrow₂_len] using hn⟩
  have hfs0_ne : fs.get ⟨0, by simpa [hfs_len] using hn⟩ ≠ 0 := by
    exact (hfs_mem _ (List.get_mem _ _)).1.1
  have hF_ne : F ≠ 0 := by
    unfold F
    exact
      zipWith_mul_sum_ne_zero_of_get_ne_zero
        (hlen := hrow₁_len.trans hfs_len.symm)
        hrow₁_nonneg hfs_nonneg j0 hrow₁_head_ne hfs0_ne
  have hG_ne : G ≠ 0 := by
    unfold G
    exact
      zipWith_mul_sum_ne_zero_of_get_ne_zero
        (hlen := hrow₂_len.trans hfs_len.symm)
        hrow₂_nonneg hfs_nonneg k0 hrow₂_head_ne hfs0_ne
  have hFG : Prec F G :=
    prec_of_affine_family_nonneg
      (f := F) (g := G) hF_ne hG_ne hF_nonneg hG_nonneg haff
  simpa [F, G] using hFG

/-- Zero-aware fixed-row form of the forward matrix theorem. This weak variant
uses `Has2x2InterlacingProperty0` and returns `Prec0`, so either output row sum
may vanish. When both sums are nonzero, the proof filters zero auxiliary
affine-row entries and reuses the strict product-family theorem. -/
theorem prec0_zipWith_sum_pair_of_2x2
    {row₁ row₂ fs : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    Prec0 ((row₁.zipWith (· * ·) fs).sum) ((row₂.zipWith (· * ·) fs).sum) := by
  let F : ℝ[X] := ((row₁.zipWith (· * ·) fs).sum)
  let G : ℝ[X] := ((row₂.zipWith (· * ·) fs).sum)
  by_cases hF_zero : F = 0
  · exact Or.inl (by simpa [F] using hF_zero)
  by_cases hG_zero : G = 0
  · exact Or.inr (Or.inl (by simpa [G] using hG_zero))
  let auxRow := rowPairAffineSeq row₁ row₂
  have hrows : row₁.length = row₂.length := by rw [hrow₁_len, hrow₂_len]
  have haux_len : ∀ {s t : ℝ}, (auxRow s t).length = n := by
    intro s t
    simpa [auxRow] using length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len
  have hrewrite :
      ∀ {s t : ℝ},
        ((C s * X + C t) * F) + G = ((auxRow s t).zipWith (· * ·) fs).sum := by
    intro s t
    simpa [F, G, auxRow] using
      rowPairAffine_combo_eq_zipWith_sum
        (row₁ := row₁) (row₂ := row₂) (fs := fs) (s := s) (t := t) hrows
  rcases hfs with ⟨hfs_mem, hfs_int⟩
  have hfs_nonneg : ∀ f ∈ fs, HasNonnegCoeffs f := by
    exact fun f hf => (hfs_mem f hf).2
  have hfs_all : IsInterlacingSeqNonneg fs := ⟨hfs_mem, hfs_int⟩
  have hF_nonneg : HasNonnegCoeffs F := by
    simpa [F] using
      hasNonnegCoeffs_zipWith_mul_sum
        (hrow := hrow₁_nonneg) (hfs := hfs_nonneg)
  have hG_nonneg : HasNonnegCoeffs G := by
    simpa [G] using
      hasNonnegCoeffs_zipWith_mul_sum
        (hrow := hrow₂_nonneg) (hfs := hfs_nonneg)
  have haux_rr :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((auxRow s t).zipWith (· * ·) fs).sum) ≠ 0 ∧ (((auxRow s t).zipWith (· * ·) fs).sum).roots.card = (((auxRow s t).zipWith (· * ·) fs).sum).natDegree) := by
    intro s t hs ht
    have haux0 :
        IsInterlacingSeq0Nonneg ((auxRow s t).reverse) := by
      exact
        isInterlacingSeq0Nonneg_reverse_rowPairAffineSeq
          (n := n) (row₁ := row₁) (row₂ := row₂)
          hrow₁_len hrow₂_len hrow₁_nonneg hrow₂_nonneg
          (fun j₁ j₂ hj => h2x2 j₁ j₂ (le_of_lt hj)) hs ht
    have haux_real :
        ∀ p ∈ (auxRow s t).reverse, p ≠ 0 → (p ≠ 0 ∧ p.roots.card = p.natDegree) := by
      intro p hp hp_ne
      exact
        isRealRooted_mem_rowPairAffineSeq_of_ne
          (n := n) (row₁ := row₁) (row₂ := row₂)
          hrow₁_len hrow₂_len (fun j => h2x2 j j le_rfl) hs ht p hp hp_ne
    have hleft_nonneg : HasNonnegCoeffs ((C s * X + C t) * F) :=
      hasNonnegCoeffs_affine_mul hs.le ht.le hF_nonneg
    have hcombo_ne : (((C s * X + C t) * F) + G) ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hleft_nonneg hG_nonneg hG_zero
    have haux_sum_ne : ((auxRow s t).zipWith (· * ·) fs).sum ≠ 0 := by
      intro hsum0
      exact hcombo_ne (by rw [hrewrite (s := s) (t := t), hsum0])
    have hsum_ne_rev :
        (((auxRow s t).reverse.zipWith (· * ·) fs.reverse).sum) ≠ 0 := by
      intro hsum0
      apply haux_sum_ne
      rw [← zipWith_mul_sum_reverse_reverse (row := auxRow s t) (fs := fs)
        (haux_len.trans hfs_len.symm)]
      exact hsum0
    have hrr_rev :
        (((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum) ≠ 0 ∧ ((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum).roots.card = ((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum).natDegree) := by
      exact
        isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeq0Nonneg
          (fs := (auxRow s t).reverse) (gs := fs)
          (by simp [haux_len, hfs_len])
          haux0 haux_real hfs_all hsum_ne_rev
    simpa [zipWith_mul_sum_reverse_reverse (row := auxRow s t) (fs := fs)
      (haux_len.trans hfs_len.symm)] using hrr_rev
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * F) + G) ≠ 0 ∧ (((C s * X + C t) * F) + G).roots.card = (((C s * X + C t) * F) + G).natDegree) := by
    intro s t hs ht
    simpa [hrewrite (s := s) (t := t)] using haux_rr (s := s) (t := t) hs ht
  have hFG : Prec F G :=
    prec_of_affine_family_nonneg
      (f := F) (g := G) hF_zero hG_zero hF_nonneg hG_nonneg haff
  simpa [F, G] using hFG.toPrec0

/-- Zero-aware fixed-row form with zero-aware input.  Besides weak
interlacing and nonnegative coefficients, the input sequence is assumed to have
real-rooted nonzero entries. -/
theorem prec0_zipWith_sum_pair_of_2x2_weak
    {row₁ row₂ fs : List ℝ[X]}
    (hrow₁_len : row₁.length = n)
    (hrow₂_len : row₂.length = n)
    (hrow₁_nonneg : ∀ p ∈ row₁, HasNonnegCoeffs p)
    (hrow₂_nonneg : ∀ p ∈ row₂, HasNonnegCoeffs p)
    (h2x2 : ∀ (j₁ j₂ : Fin n), j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (row₁.get ⟨j₁, by simp [hrow₁_len]⟩)
        (row₁.get ⟨j₂, by simp [hrow₁_len]⟩)
        (row₂.get ⟨j₁, by simp [hrow₂_len]⟩)
        (row₂.get ⟨j₂, by simp [hrow₂_len]⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.roots.card = f.natDegree)) :
    Prec0 ((row₁.zipWith (· * ·) fs).sum) ((row₂.zipWith (· * ·) fs).sum) := by
  let F : ℝ[X] := ((row₁.zipWith (· * ·) fs).sum)
  let G : ℝ[X] := ((row₂.zipWith (· * ·) fs).sum)
  by_cases hF_zero : F = 0
  · exact Or.inl (by simpa [F] using hF_zero)
  by_cases hG_zero : G = 0
  · exact Or.inr (Or.inl (by simpa [G] using hG_zero))
  let auxRow := rowPairAffineSeq row₁ row₂
  have hrows : row₁.length = row₂.length := by rw [hrow₁_len, hrow₂_len]
  have haux_len : ∀ {s t : ℝ}, (auxRow s t).length = n := by
    intro s t
    simpa [auxRow] using
      length_rowPairAffineSeq (n := n) (s := s) (t := t) hrow₁_len hrow₂_len
  have hrewrite :
      ∀ {s t : ℝ},
        ((C s * X + C t) * F) + G = ((auxRow s t).zipWith (· * ·) fs).sum := by
    intro s t
    simpa [F, G, auxRow] using
      rowPairAffine_combo_eq_zipWith_sum
        (row₁ := row₁) (row₂ := row₂) (fs := fs) (s := s) (t := t) hrows
  have hfs_nonneg : ∀ f ∈ fs, HasNonnegCoeffs f := hfs.2
  have hF_nonneg : HasNonnegCoeffs F := by
    simpa [F] using
      hasNonnegCoeffs_zipWith_mul_sum
        (hrow := hrow₁_nonneg) (hfs := hfs_nonneg)
  have hG_nonneg : HasNonnegCoeffs G := by
    simpa [G] using
      hasNonnegCoeffs_zipWith_mul_sum
        (hrow := hrow₂_nonneg) (hfs := hfs_nonneg)
  have haux_rr :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((auxRow s t).zipWith (· * ·) fs).sum) ≠ 0 ∧ (((auxRow s t).zipWith (· * ·) fs).sum).roots.card = (((auxRow s t).zipWith (· * ·) fs).sum).natDegree) := by
    intro s t hs ht
    have haux0 :
        IsInterlacingSeq0Nonneg ((auxRow s t).reverse) := by
      exact
        isInterlacingSeq0Nonneg_reverse_rowPairAffineSeq
          (n := n) (row₁ := row₁) (row₂ := row₂)
          hrow₁_len hrow₂_len hrow₁_nonneg hrow₂_nonneg
          (fun j₁ j₂ hj => h2x2 j₁ j₂ (le_of_lt hj)) hs ht
    have haux_real :
        ∀ p ∈ (auxRow s t).reverse, p ≠ 0 → (p ≠ 0 ∧ p.roots.card = p.natDegree) := by
      intro p hp hp_ne
      exact
        isRealRooted_mem_rowPairAffineSeq_of_ne
          (n := n) (row₁ := row₁) (row₂ := row₂)
          hrow₁_len hrow₂_len (fun j => h2x2 j j le_rfl) hs ht p hp hp_ne
    have hleft_nonneg : HasNonnegCoeffs ((C s * X + C t) * F) :=
      hasNonnegCoeffs_affine_mul hs.le ht.le hF_nonneg
    have hcombo_ne : (((C s * X + C t) * F) + G) ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hleft_nonneg hG_nonneg hG_zero
    have haux_sum_ne : ((auxRow s t).zipWith (· * ·) fs).sum ≠ 0 := by
      intro hsum0
      exact hcombo_ne (by rw [hrewrite (s := s) (t := t), hsum0])
    have hsum_ne_rev :
        (((auxRow s t).reverse.zipWith (· * ·) fs.reverse).sum) ≠ 0 := by
      intro hsum0
      apply haux_sum_ne
      rw [← zipWith_mul_sum_reverse_reverse (row := auxRow s t) (fs := fs)
        (haux_len.trans hfs_len.symm)]
      exact hsum0
    have hrr_rev :
        (((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum) ≠ 0 ∧ ((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum).roots.card = ((((auxRow s t).reverse).zipWith (· * ·) fs.reverse).sum).natDegree) := by
      exact
        isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeq0Nonneg_both
          (fs := (auxRow s t).reverse) (gs := fs)
          (by simp [haux_len, hfs_len])
          haux0 haux_real hfs hfs_real hsum_ne_rev
    simpa [zipWith_mul_sum_reverse_reverse (row := auxRow s t) (fs := fs)
      (haux_len.trans hfs_len.symm)] using hrr_rev
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * F) + G) ≠ 0 ∧ (((C s * X + C t) * F) + G).roots.card = (((C s * X + C t) * F) + G).natDegree) := by
    intro s t hs ht
    simpa [hrewrite (s := s) (t := t)] using haux_rr (s := s) (t := t) hs ht
  have hFG : Prec F G :=
    prec_of_affine_family_nonneg
      (f := F) (g := G) hF_zero hG_zero hF_nonneg hG_nonneg haff
  simpa [F, G] using hFG.toPrec0

/-! ## Main characterization theorem -/

/-- **Forward direction**: If `n > 0`, `G` has non-negative coefficients, and
    Brändén's affine condition holds for all row/column choices (including the
    boundary cases with repeated indices), then `G` maps `𝓕ₙ⁺ → 𝓕ₘ⁺`. -/
theorem matrix_preserves_interlacing_seq
    (hn : 0 < n)
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by have := hG_rect _ (G.get_mem i₁); lia⟩)
        ((G.get i₁).get ⟨j₂, by have := hG_rect _ (G.get_mem i₁); lia⟩)
        ((G.get i₂).get ⟨j₁, by have := hG_rect _ (G.get_mem i₂); lia⟩)
        ((G.get i₂).get ⟨j₂, by have := hG_rect _ (G.get_mem i₂); lia⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) := by
  /-
  Handbook proof structure (Brändén, §7.8, Theorem 7.8.5):

  For fixed output rows `i < j`, one considers, for each `s, t > 0`, the
  auxiliary column sequence

    h_k := ((C s * X + C t) * G[i,k]) + G[j,k].

  The affine matrix hypothesis is exactly what makes `(h_k)` an interlacing
  sequence. The non-strict index form is also what supplies the boundary cases
  needed to recover elementwise real-rootedness of the image when `m = 1` or
  `n = 1`.
  Then

    ((C s * X + C t) * (matPolyAction G fs).get i) + (matPolyAction G fs).get j
      = ∑ h_k * fs_k

  is real-rooted by Brändén's Lemma 7.8.3: the reversed product-sum of an
  interlacing sequence with an interlacing sequence of non-negative-coefficient
  polynomials is real-rooted. The remaining local gap is to package that
  Lemma 7.8.3 in this codebase and then route the affine family back to `Prec`
  through the already-developed affine-family machinery above.
  -/
  rcases hfs with ⟨hfs_mem, hfs_int⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hentry_head_ne (iG : Fin G.length) :
      (G.get iG).get ⟨0, by
        have hleni : (G.get iG).length = n := hG_rect _ (G.get_mem iG)
        lia⟩ ≠ 0 := by
    have hdiag :
        Has2x2InterlacingProperty
          ((G.get iG).get ⟨j0, by have := hG_rect _ (G.get_mem iG); lia⟩)
          ((G.get iG).get ⟨j0, by have := hG_rect _ (G.get_mem iG); lia⟩)
          ((G.get iG).get ⟨j0, by have := hG_rect _ (G.get_mem iG); lia⟩)
          ((G.get iG).get ⟨j0, by have := hG_rect _ (G.get_mem iG); lia⟩) := by
      simpa [j0] using hG_affine iG iG j0 j0 le_rfl le_rfl
    exact
      ne_zero_of_self_2x2
        ((G.get iG).get ⟨j0, by have := hG_rect _ (G.get_mem iG); lia⟩)
        hdiag
  constructor
  · intro p hp
    rcases List.mem_map.mp hp with ⟨row, hrow_mem, rfl⟩
    have hrow_nonneg_sum :
        HasNonnegCoeffs ((row.zipWith (· * ·) fs).sum) := by
      exact hasNonnegCoeffs_zipWith_mul_sum (fun q hq => hG_nonneg row hrow_mem q hq)
        (fun q hq => (hfs_mem q hq).2)
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hrow_mem
    let iG : Fin G.length := ⟨i, by simp⟩
    have hself :
        Prec (((G.get iG).zipWith (· * ·) fs).sum) (((G.get iG).zipWith (· * ·) fs).sum) := by
      exact
        prec_zipWith_sum_pair_of_2x2
          (n := n)
          (hn := hn)
          (row₁ := G.get iG)
          (row₂ := G.get iG)
          (fs := fs)
          (hrow₁_len := hG_rect _ (G.get_mem iG))
          (hrow₂_len := hG_rect _ (G.get_mem iG))
          (hrow₁_head_ne := hentry_head_ne iG)
          (hrow₂_head_ne := hentry_head_ne iG)
          (hrow₁_nonneg := fun q hq => hG_nonneg _ (G.get_mem iG) _ hq)
          (hrow₂_nonneg := fun q hq => hG_nonneg _ (G.get_mem iG) _ hq)
          (h2x2 := fun j₁ j₂ hj =>
            hG_affine iG iG j₁ j₂ le_rfl hj)
          (hfs_len := hfs_len)
          (hfs := ⟨hfs_mem, hfs_int⟩)
    exact ⟨hself.1, hrow_nonneg_sum⟩
  · rw [isInterlacingSeq_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let iG : Fin G.length := ⟨i, by simpa [matPolyAction] using i.2⟩
    let jG : Fin G.length := ⟨j, by simpa [matPolyAction] using j.2⟩
    have hpair :
        Prec (((G.get iG).zipWith (· * ·) fs).sum) (((G.get jG).zipWith (· * ·) fs).sum) := by
      exact
        prec_zipWith_sum_pair_of_2x2
          (n := n)
          (hn := hn)
          (row₁ := G.get iG)
          (row₂ := G.get jG)
          (fs := fs)
          (hrow₁_len := hG_rect _ (G.get_mem iG))
          (hrow₂_len := hG_rect _ (G.get_mem jG))
          (hrow₁_head_ne := hentry_head_ne iG)
          (hrow₂_head_ne := hentry_head_ne jG)
          (hrow₁_nonneg := fun p hp => hG_nonneg _ (G.get_mem iG) _ hp)
          (hrow₂_nonneg := fun p hp => hG_nonneg _ (G.get_mem jG) _ hp)
          (h2x2 := fun j₁ j₂ hj =>
            by
              simpa [iG, jG] using
                hG_affine iG jG j₁ j₂ (le_of_lt (by simpa [iG, jG] using hij)) hj)
          (hfs_len := hfs_len)
          (hfs := ⟨hfs_mem, hfs_int⟩)
    simpa [matPolyAction, iG, jG] using hpair

/-- **Weak zero-aware forward direction**: if `G` has non-negative coefficients
and satisfies the weak affine 2×2 condition `Has2x2InterlacingProperty0`, then
it maps strict nonnegative interlacing input sequences to weak zero-aware
nonnegative interlacing output sequences. The weak codomain is what makes zero
output rows harmless. -/
theorem matrix_preserves_interlacing_seq0_of_2x2
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by have := hG_rect _ (G.get_mem i₁); lia⟩)
        ((G.get i₁).get ⟨j₂, by have := hG_rect _ (G.get_mem i₁); lia⟩)
        ((G.get i₂).get ⟨j₁, by have := hG_rect _ (G.get_mem i₂); lia⟩)
        ((G.get i₂).get ⟨j₂, by have := hG_rect _ (G.get_mem i₂); lia⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) := by
  rcases hfs with ⟨hfs_mem, hfs_int⟩
  refine ⟨?_, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let iG : Fin G.length := ⟨i, by simpa [matPolyAction] using i.2⟩
    let jG : Fin G.length := ⟨j, by simpa [matPolyAction] using j.2⟩
    have hpair :
        Prec0 (((G.get iG).zipWith (· * ·) fs).sum)
          (((G.get jG).zipWith (· * ·) fs).sum) := by
      exact
        prec0_zipWith_sum_pair_of_2x2
          (n := n)
          (row₁ := G.get iG)
          (row₂ := G.get jG)
          (fs := fs)
          (hrow₁_len := hG_rect _ (G.get_mem iG))
          (hrow₂_len := hG_rect _ (G.get_mem jG))
          (hrow₁_nonneg := fun p hp => hG_nonneg _ (G.get_mem iG) _ hp)
          (hrow₂_nonneg := fun p hp => hG_nonneg _ (G.get_mem jG) _ hp)
          (h2x2 := fun j₁ j₂ hj =>
            by
              simpa [iG, jG] using
                hG_affine iG jG j₁ j₂ (le_of_lt (by simpa [iG, jG] using hij)) hj)
          (hfs_len := hfs_len)
          (hfs := ⟨hfs_mem, hfs_int⟩)
    simpa [matPolyAction, iG, jG] using hpair
  · intro p hp
    rcases List.mem_map.mp hp with ⟨row, hrow_mem, rfl⟩
    exact
      hasNonnegCoeffs_zipWith_mul_sum
        (fun q hq => hG_nonneg row hrow_mem q hq)
        (fun q hq => (hfs_mem q hq).2)

/-- Weak zero-aware forward direction with zero-aware input.  The extra
conclusion records that each nonzero output entry is real-rooted, so this
statement can be iterated. -/
theorem matrix_preserves_interlacing_seq0_of_2x2_weak
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by have := hG_rect _ (G.get_mem i₁); lia⟩)
        ((G.get i₁).get ⟨j₂, by have := hG_rect _ (G.get_mem i₁); lia⟩)
        ((G.get i₂).get ⟨j₁, by have := hG_rect _ (G.get_mem i₂); lia⟩)
        ((G.get i₂).get ⟨j₂, by have := hG_rect _ (G.get_mem i₂); lia⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.roots.card = f.natDegree)) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.roots.card = f.natDegree) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [isInterlacingSeq0_iff_pairwise]
      refine List.pairwise_iff_get.2 ?_
      intro i j hij
      let iG : Fin G.length := ⟨i, by simpa [matPolyAction] using i.2⟩
      let jG : Fin G.length := ⟨j, by simpa [matPolyAction] using j.2⟩
      have hpair :
          Prec0 (((G.get iG).zipWith (· * ·) fs).sum)
            (((G.get jG).zipWith (· * ·) fs).sum) := by
        exact
          prec0_zipWith_sum_pair_of_2x2_weak
            (n := n)
            (row₁ := G.get iG)
            (row₂ := G.get jG)
            (fs := fs)
            (hrow₁_len := hG_rect _ (G.get_mem iG))
            (hrow₂_len := hG_rect _ (G.get_mem jG))
            (hrow₁_nonneg := fun p hp => hG_nonneg _ (G.get_mem iG) _ hp)
            (hrow₂_nonneg := fun p hp => hG_nonneg _ (G.get_mem jG) _ hp)
            (h2x2 := fun j₁ j₂ hj =>
              by
                simpa [iG, jG] using
                  hG_affine iG jG j₁ j₂ (le_of_lt (by simpa [iG, jG] using hij)) hj)
            (hfs_len := hfs_len)
            (hfs := hfs)
            (hfs_real := hfs_real)
      simpa [matPolyAction, iG, jG] using hpair
    · intro p hp
      rcases List.mem_map.mp hp with ⟨row, hrow_mem, rfl⟩
      exact
        hasNonnegCoeffs_zipWith_mul_sum
          (fun q hq => hG_nonneg row hrow_mem q hq)
          (fun q hq => hfs.2 q hq)
  · intro p hp hp0
    rcases List.mem_map.mp hp with ⟨row, hrow_mem, hp_eq⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hrow_mem
    let iG : Fin G.length := i
    have hsum_eq_p : ((G.get iG).zipWith (· * ·) fs).sum = p := by
      have h := hp_eq
      rw [← hi] at h
      simpa [iG, List.get_eq_getElem] using h
    have hself0 :
        Prec0 (((G.get iG).zipWith (· * ·) fs).sum)
          (((G.get iG).zipWith (· * ·) fs).sum) := by
      exact
        prec0_zipWith_sum_pair_of_2x2_weak
          (n := n)
          (row₁ := G.get iG)
          (row₂ := G.get iG)
          (fs := fs)
          (hrow₁_len := hG_rect _ (G.get_mem iG))
          (hrow₂_len := hG_rect _ (G.get_mem iG))
          (hrow₁_nonneg := fun q hq => hG_nonneg _ (G.get_mem iG) _ hq)
          (hrow₂_nonneg := fun q hq => hG_nonneg _ (G.get_mem iG) _ hq)
          (h2x2 := fun j₁ j₂ hj => hG_affine iG iG j₁ j₂ le_rfl hj)
          (hfs_len := hfs_len)
          (hfs := hfs)
          (hfs_real := hfs_real)
    have hp0' : ((G.get iG).zipWith (· * ·) fs).sum ≠ 0 := by
      intro hzero
      exact hp0 (by rw [← hsum_eq_p, hzero])
    rw [← hsum_eq_p]
    exact (hself0.toPrec_of_ne hp0' hp0').1

end
end RealRooted
