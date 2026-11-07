module

public import RealRooted.AissenSchoenbergWhitney
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
public import RealRooted.ToeplitzFin

/-! # Positive supported minors of elementary Toeplitz matrices -/

public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- Every supported ordered minor of a positive lower bidiagonal matrix is positive. -/
theorem det_bidiagonal_submatrix_pos {a : ℝ} (ha : 0 < a) {n : ℕ}
    {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hlo : ∀ i, cols i ≤ rows i) (hhi : ∀ i, rows i ≤ cols i + 1) :
    0 < ((bidiagonal a).submatrix rows cols).det := by
  induction n with
  | zero => simp
  | succ n ih =>
    let S := (bidiagonal a).submatrix rows cols
    have ht : 0 < (S.submatrix Fin.succ Fin.succ).det :=
      ih (hrows.comp Fin.strictMono_succ) (hcols.comp Fin.strictMono_succ)
        (fun i => hlo i.succ) (fun i => hhi i.succ)
    by_cases heq : rows 0 = cols 0
    · have h00 : S 0 0 = a := by simp [S, heq]
      have h0j (j : Fin n) : S 0 j.succ = 0 := by
        have hc := hcols (Fin.succ_pos j)
        have hne : rows 0 ≠ cols j.succ := by lia
        have hne' : rows 0 ≠ cols j.succ + 1 := by lia
        simp [S, hne, hne']
      change 0 < S.det
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simpa [h00, h0j] using mul_pos ha ht
    · have heq' : rows 0 = cols 0 + 1 := by have := hlo 0; have := hhi 0; lia
      have h00 : S 0 0 = 1 := by simp [S, heq']
      have hi0 (i : Fin n) : S i.succ 0 = 0 := by
        have hr := hrows (Fin.succ_pos i)
        have hne : rows i.succ ≠ cols 0 := by lia
        have hne' : rows i.succ ≠ cols 0 + 1 := by lia
        simp [S, hne, hne']
      change 0 < S.det
      rw [det_succ_column_zero, Fin.sum_univ_succ]
      simpa [h00, hi0] using ht

/-- Polynomial multiplication agrees with finite Toeplitz multiplication. -/
theorem toeplitzFin_coeff_mul (p q : ℝ[X]) (N : ℕ) :
    toeplitzFin (p * q).coeff N = toeplitzFin p.coeff N * toeplitzFin q.coeff N := by
  rw [toeplitzFin_mul_coeff]
  congr 1
  funext k
  simp [Polynomial.coeff_mul, PowerSeries.coeff_mul]

/-- Multiplication by a positive linear factor extends the positive-minor band by one. -/
theorem det_toeplitzFin_linear_mul_pos {q : ℝ[X]} (hq : IsPolyaFreqSeq q.coeff)
    {d N n : ℕ}
    (hpos : ∀ (rows cols : Fin n → Fin (N + 1)), StrictMono rows → StrictMono cols →
      (∀ i, (cols i).val ≤ (rows i).val) →
      (∀ i, (rows i).val ≤ (cols i).val + d) →
      0 < ((toeplitzFin q.coeff N).submatrix rows cols).det)
    {a : ℝ} (ha : 0 < a) {rows cols : Fin n → Fin (N + 1)}
    (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hlo : ∀ i, (cols i).val ≤ (rows i).val)
    (hhi : ∀ i, (rows i).val ≤ (cols i).val + (d + 1)) :
    0 < ((toeplitzFin ((X - C (-a)) * q).coeff N).submatrix rows cols).det := by
  let mid : Fin n → Fin (N + 1) := fun i =>
    ⟨min (rows i).val ((cols i).val + d), lt_of_le_of_lt (min_le_left _ _) (rows i).isLt⟩
  have hm : StrictMono mid := by
    intro i j hij
    have hr := hrows hij
    have hc := hcols hij
    change min (rows i).val ((cols i).val + d) <
      min (rows j).val ((cols j).val + d)
    exact lt_min (lt_of_le_of_lt (min_le_left _ _) hr)
      (lt_of_le_of_lt (min_le_right _ _) (Nat.add_lt_add_right hc d))
  rw [toeplitzFin_coeff_mul]
  apply (IsPolyaFreqSeq.linear (neg_nonpos.mpr ha.le)).submatrix
    Fin.val_strictMono Fin.val_strictMono |>.toRect.det_submatrix_mul_pos
      (hq.submatrix Fin.val_strictMono Fin.val_strictMono).toRect hrows hcols
      (OrderEmbedding.ofStrictMono mid hm)
  · change 0 < ((toeplitz (X - C (-a)).coeff).submatrix
      (fun i => (rows i).val) (fun i => (mid i).val)).det
    rw [toeplitz_linear_coeff, neg_neg]
    apply det_bidiagonal_submatrix_pos ha
      (Fin.val_strictMono.comp hrows) (Fin.val_strictMono.comp hm)
    · intro i
      exact min_le_left _ _
    · intro i
      have hi := hhi i
      change (rows i).val ≤ min (rows i).val ((cols i).val + d) + 1
      lia
  · apply hpos mid cols hm hcols
    · intro i
      change (cols i).val ≤ min (rows i).val ((cols i).val + d)
      exact le_min (hlo i) (Nat.le_add_right _ _)
    · intro i
      exact min_le_right _ _

/-- Products of positive linear factors have PF coefficient sequences. -/
private theorem isPolyaFreqSeq_prod_linear {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    IsPolyaFreqSeq (∏ i ∈ s, (X - C (-a i))).coeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPolyaFreqSeq.one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))).linear_mul
      (neg_nonpos.mpr (ha i (Finset.mem_insert_self _ _)).le)

/-- Every minor within the degree band of a positive linear-factor product is positive. -/
theorem det_toeplitzFin_prod_linear_pos {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {N n : ℕ}
    (rows cols : Fin n → Fin (N + 1)) (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hlo : ∀ i, (cols i).val ≤ (rows i).val)
    (hhi : ∀ i, (rows i).val ≤ (cols i).val + s.card) :
    0 < ((toeplitzFin (∏ i ∈ s, (X - C (-a i))).coeff N).submatrix rows cols).det := by
  classical
  induction s using Finset.induction_on generalizing rows cols with
  | empty =>
    have heq : rows = cols := by
      funext i
      apply Fin.ext
      have hl := hlo i
      have hh := hhi i
      simp only [Finset.card_empty, Nat.add_zero] at hh
      lia
    subst rows
    simp [toeplitzFin, toeplitz_one_coeff, Matrix.submatrix_submatrix,
      Matrix.submatrix_one _ (Fin.val_injective.comp hcols.injective)]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have has : ∀ j ∈ s, 0 < a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    apply det_toeplitzFin_linear_mul_pos (isPolyaFreqSeq_prod_linear s a has)
      (fun r c hr hc hl hh => ih has r c hr hc hl hh)
      (ha i (Finset.mem_insert_self _ _)) hrows hcols hlo
    simpa only [Finset.card_insert_of_notMem hi] using hhi

/-- Supported ordered minors of an infinite Toeplitz matrix of positive linear factors
are positive; no ambient truncation size occurs in the statement. -/
theorem det_toeplitz_prod_linear_pos {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {n : ℕ}
    (rows cols : Fin n → ℕ) (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hlo : ∀ i, cols i ≤ rows i) (hhi : ∀ i, rows i ≤ cols i + s.card) :
    0 < ((toeplitz (∏ i ∈ s, (X - C (-a i))).coeff).submatrix rows cols).det := by
  cases n with
  | zero => simp
  | succ n =>
    let N := max (rows (Fin.last n)) (cols (Fin.last n))
    let r : Fin (n + 1) → Fin (N + 1) := fun i =>
      ⟨rows i, Nat.lt_succ_of_le
        ((hrows.monotone (Fin.le_last i)).trans (le_max_left _ _))⟩
    let c : Fin (n + 1) → Fin (N + 1) := fun i =>
      ⟨cols i, Nat.lt_succ_of_le
        ((hcols.monotone (Fin.le_last i)).trans (le_max_right _ _))⟩
    exact det_toeplitzFin_prod_linear_pos s a ha r c
      (fun _ _ hij => hrows hij) (fun _ _ hij => hcols hij) hlo hhi

end RealRooted.Schur
