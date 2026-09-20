import RealRooted.BrandenLeite.MarkedShift
import RealRooted.FiniteFreeRootCount

/-!
# Nonstationary weighted-shift tiling rows

This file turns the marked-shift kernel package into polynomial rows.  The
shared finite transition kernel remains explicit throughout; the PF and proper-
position conclusions are inherited from the checked kernel-limit theorem.
-/

open Matrix Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- The Green kernel acts on every matrix by the same weighted row recurrence. -/
theorem weightedGreenKernel_mul_apply_succ
    (b : ℕ → ℝ) {N : ℕ} (s : Fin N)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    (weightedGreenKernel b N * A) s.succ j =
      A s.succ j + b (s.val + 1) *
        (weightedGreenKernel b N * A) s.castSucc j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp_rw [weightedGreenKernel_apply_succ]
  simp_rw [add_mul]
  simp_rw [mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single s.succ]
  · simp
  · intro k _ hks
    simp [Ne.symm hks]
  · simp

/-- Powers of the unweighted lower shift have one possible displaced entry. -/
theorem lowerShift_pow_apply (N r : ℕ) (i j : Fin (N + 1)) :
    (lowerShift N ^ r : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j =
      if i.val = j.val + r then 1 else 0 := by
  simpa [lowerShift, descendingWeightProduct] using
    (weightedLowerShift_pow_apply (fun _ => (1 : ℝ)) N r i j)

/-- A marked shift reads the optional-rise product at the uniquely displaced
column, when that column is still in the finite index type. -/
theorem markedShiftKernel_apply
    (as : List (ℕ → ℝ)) (N r : ℕ) (i j : Fin (N + 1)) :
    markedShiftKernel as N r i j =
      if h : j.val + r < N + 1 then
        optionalRiseMatrix as N i ⟨j.val + r, h⟩
      else 0 := by
  rw [markedShiftKernel, Matrix.mul_apply]
  by_cases h : j.val + r < N + 1
  · let k : Fin (N + 1) := ⟨j.val + r, h⟩
    rw [dite_eq_left h, Finset.sum_eq_single k]
    · rw [lowerShift_pow_apply, ite_eq_left (by rfl), mul_one]
    · intro k' _ hk'
      rw [lowerShift_pow_apply, ite_eq_right, mul_zero]
      intro heq
      exact hk' (Fin.ext heq)
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro k _
    rw [lowerShift_pow_apply, ite_eq_right, mul_zero]
    intro heq
    exact h (heq ▸ k.isLt)

/-- Recurrence-friendly entry formula for the marked kernel, with all natural
subtractions guarded by the displayed displacement inequality. -/
theorem markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient
    (as : List (ℕ → ℝ)) (N r : ℕ) (i j : Fin (N + 1)) :
    markedShiftKernel as N r i j =
      if j.val + r ≤ i.val then
        orderedOptionalRiseCoefficient as i.val (i.val - (j.val + r))
      else 0 := by
  rw [markedShiftKernel_apply]
  by_cases hji : j.val + r ≤ i.val
  · have hbound : j.val + r < N + 1 := hji.trans_lt i.isLt
    rw [dite_eq_left hbound, ite_eq_left hji, optionalRiseMatrix_apply]
    simp [hji]
  · rw [ite_eq_right hji]
    by_cases hbound : j.val + r < N + 1
    · rw [dite_eq_left hbound, optionalRiseMatrix_apply]
      simp [hji]
    · rw [dite_eq_right hbound]

/-- The finite nonstationary tiling row with background weights `b`, ordered
optional-rise weights `as`, and marked shift order `r`. -/
def weightedShiftTilingRow
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) (N r : ℕ)
    (i : Fin (N + 1)) : ℝ[X] :=
  kernelRow (weightedGreenKernel b N) (markedShiftKernel as N r) i

/-- Nonnegative data give PF tiling rows. -/
theorem weightedShiftTilingRow_isPFPolynomial
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {as : List (ℕ → ℝ)} (has : ∀ a ∈ as, ∀ n, 0 ≤ a n)
    (N : ℕ) {r : ℕ} (hr : 0 < r) (i : Fin (N + 1)) :
    IsPFPolynomial (weightedShiftTilingRow b as N r i) := by
  exact (weightedGreenKernel_markedShiftKernel_pf_and_prec0
    hb has N hr).1 i

/-- Consecutive nonstationary tiling rows are in zero-aware proper position. -/
theorem prec0_weightedShiftTilingRow_succ
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {as : List (ℕ → ℝ)} (has : ∀ a ∈ as, ∀ n, 0 ≤ a n)
    (N : ℕ) {r : ℕ} (hr : 0 < r) (i : Fin N) :
    Interl (weightedShiftTilingRow b as N r i.castSucc)
      (weightedShiftTilingRow b as N r i.succ) := by
  exact (weightedGreenKernel_markedShiftKernel_pf_and_prec0
    hb has N hr).2 i

/-- The constant coefficient of a tiling row is the unique descending Green-
kernel path product. -/
theorem coeff_zero_weightedShiftTilingRow
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) (N r : ℕ)
    (i : Fin (N + 1)) :
    (weightedShiftTilingRow b as N r i).coeff 0 =
      descendingWeightProduct b i.val i.val := by
  rw [weightedShiftTilingRow, coeff_kernelRow]
  simp [weightedGreenKernel_apply, descendingWeightProduct]

/-- Positive background weights make every tiling-row constant coefficient
positive. -/
theorem coeff_zero_weightedShiftTilingRow_pos
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    (as : List (ℕ → ℝ)) (N r : ℕ) (i : Fin (N + 1)) :
    0 < (weightedShiftTilingRow b as N r i).coeff 0 := by
  rw [coeff_zero_weightedShiftTilingRow]
  exact Finset.prod_pos fun t _ => hb (i.val - t)

/-- The shared-kernel finite vector equation before resolving the Green-kernel
row recurrence. -/
theorem weightedShiftTilingRow_eq_global
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) (N : ℕ)
    {r : ℕ} (hr : 0 < r) (i : Fin (N + 1)) :
    weightedShiftTilingRow b as N r i =
      C (weightedGreenKernel b N i 0) +
        X * ∑ j : Fin (N + 1),
          C ((weightedGreenKernel b N * markedShiftKernel as N r) i j) *
            weightedShiftTilingRow b as N r j := by
  let G := weightedGreenKernel b N
  let K := markedShiftKernel as N r
  have hG : ∀ i j, i < j → G i j = 0 := by
    intro a c hac
    exact weightedGreenKernel_apply_eq_zero_of_lt b N
      (Fin.mk_lt_mk.mp hac)
  have hK : ∀ i j, i < j → K i j = 0 := by
    intro a c hac
    exact markedShiftKernel_apply_eq_zero_of_le as N hr
      (Fin.mk_le_mk.mpr hac.le)
  have hKstrict : ∀ i j, i.val ≤ j.val → K i j = 0 :=
    fun a c => markedShiftKernel_apply_eq_zero_of_le as N hr
  have hGKlower : ∀ i j, i < j → (G * K) i j = 0 := by
    intro a c hac
    exact Matrix.mul_apply_eq_zero_of_lt_of_upper_zero G K hG hK hac
  have hGKdiag : ∀ i, (G * K) i i = 0 := by
    intro a
    exact Matrix.mul_apply_eq_zero_of_le_of_lower_strictLower G K hG
      hKstrict (le_refl a.val)
  have hreg (j : Fin (N + 1)) :
      regularizedKernelRow G K j = kernelRow G K j :=
    regularizedKernelRow_eq_kernelRow_of_diagonal_zero G K hG hK hGKdiag j
  change kernelRow G K i = _
  calc
    kernelRow G K i = regularizedKernelRow G K i := (hreg i).symm
    _ = C (G i 0) + X * ∑ j : Fin (N + 1),
        C (Matrix.strictLowerPart (G * K) i j) *
          regularizedKernelRow G K j := regularizedKernelRow_eq G K i
    _ = C (G i 0) + X * ∑ j : Fin (N + 1),
        C ((G * K) i j) * kernelRow G K j := by
      rw [Matrix.strictLowerPart_eq_self_of_lower_diagonal_zero
        (G * K) hGKlower hGKdiag]
      simp_rw [hreg]

/-- Resolving the Green-kernel row equation gives the finite nonstationary
vector recurrence. -/
theorem weightedShiftTilingRow_succ_eq
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) {N : ℕ}
    (s : Fin N) {r : ℕ} (hr : 0 < r) :
    weightedShiftTilingRow b as N r s.succ =
      C (b (s.val + 1)) * weightedShiftTilingRow b as N r s.castSucc +
        X * ∑ j : Fin (N + 1),
          C (markedShiftKernel as N r s.succ j) *
            weightedShiftTilingRow b as N r j := by
  have hsucc := weightedShiftTilingRow_eq_global b as N hr s.succ
  have hpred := weightedShiftTilingRow_eq_global b as N hr s.castSucc
  have hG0 : weightedGreenKernel b N s.succ 0 =
      b (s.val + 1) * weightedGreenKernel b N s.castSucc 0 := by
    rw [weightedGreenKernel_apply_succ]
    simp
  have hGK (j : Fin (N + 1)) :
      (weightedGreenKernel b N * markedShiftKernel as N r) s.succ j =
        markedShiftKernel as N r s.succ j + b (s.val + 1) *
          (weightedGreenKernel b N * markedShiftKernel as N r)
            s.castSucc j :=
    weightedGreenKernel_mul_apply_succ b s (markedShiftKernel as N r) j
  rw [hsucc, hpred, hG0]
  simp_rw [hGK, map_add, map_mul, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The finite recurrence with the marked-kernel entries resolved into their
ordered strict-selection coefficients. -/
theorem weightedShiftTilingRow_succ_eq_orderedOptionalRiseCoefficient
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) {N : ℕ}
    (s : Fin N) {r : ℕ} (hr : 0 < r) :
    weightedShiftTilingRow b as N r s.succ =
      C (b (s.val + 1)) * weightedShiftTilingRow b as N r s.castSucc +
        X * ∑ j : Fin (N + 1),
          C (if j.val + r ≤ s.succ.val then
              orderedOptionalRiseCoefficient as s.succ.val
                (s.succ.val - (j.val + r))
            else 0) * weightedShiftTilingRow b as N r j := by
  rw [weightedShiftTilingRow_succ_eq b as s hr]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient]

/-- The descending Green-path product is the ordinary product of the first
`n` positive-index background weights. -/
theorem descendingWeightProduct_self_eq_prod_range
    (b : ℕ → ℝ) (n : ℕ) :
    descendingWeightProduct b n n =
      ∏ k ∈ Finset.range n, b (k + 1) := by
  rw [descendingWeightProduct]
  calc
    ∏ t ∈ Finset.range n, b (n - t) =
        ∏ t ∈ Finset.range n, b ((n - 1 - t) + 1) := by
      apply Finset.prod_congr rfl
      intro t ht
      congr 1
      have htn := Finset.mem_range.mp ht
      lia
    _ = ∏ k ∈ Finset.range n, b (k + 1) :=
      Finset.prod_range_reflect (fun k => b (k + 1)) n

/-- Extending a descending path appends its new terminal weight. -/
theorem descendingWeightProduct_succ_length
    (w : ℕ → ℝ) (n j : ℕ) :
    descendingWeightProduct w n (j + 1) =
      descendingWeightProduct w n j * w (n - j) := by
  simp [descendingWeightProduct, Finset.prod_range_succ]

/-- Adding one descending step peels off the weight at the starting level. -/
theorem descendingWeightProduct_succ
    (w : ℕ → ℝ) {n j : ℕ} (hj : j < n) :
    descendingWeightProduct w n (j + 1) =
      w n * descendingWeightProduct w (n - 1) j := by
  induction j with
  | zero => simp [descendingWeightProduct]
  | succ j ih =>
      rw [descendingWeightProduct_succ_length, ih (by lia),
        descendingWeightProduct_succ_length]
      have hindex : n - (j + 1) = n - 1 - j := by lia
      rw [hindex]
      ring

/-- Elementary selection coefficient of a list of constant factor weights. -/
def constantOptionalRiseCoefficient : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: as, j + 1 =>
      constantOptionalRiseCoefficient as (j + 1) +
        a * constantOptionalRiseCoefficient as j

/-- Constant optional-rise coefficients are elementary selection sums. -/
theorem constantOptionalRiseCoefficient_eq_sum_sublistsLen
    (alphas : List ℝ) (j : ℕ) :
    constantOptionalRiseCoefficient alphas j =
      ((alphas.sublistsLen j).map List.prod).sum := by
  induction alphas generalizing j with
  | nil =>
      cases j <;> simp [constantOptionalRiseCoefficient]
  | cons a alphas ih =>
      cases j with
      | zero => simp [constantOptionalRiseCoefficient]
      | succ j =>
          rw [constantOptionalRiseCoefficient,
            List.sublistsLen_succ_cons, List.map_append,
            List.sum_append, ih, ih]
          simp only [List.map_map]
          congr 1
          change a * (List.map List.prod
              (List.sublistsLen j alphas)).sum =
            (List.map (fun bs => (a :: bs).prod)
              (List.sublistsLen j alphas)).sum
          simp_rw [List.prod_cons]
          rw [List.sum_map_mul_left]

/-- If every position-dependent factor separates as `a * w n`, then the
ordered coefficient separates into an elementary selection coefficient and a
single descending level-weight product. -/
theorem orderedOptionalRiseCoefficient_map_mul
    (alphas : List ℝ) (w : ℕ → ℝ) {n j : ℕ} (hj : j ≤ n) :
    orderedOptionalRiseCoefficient
        (alphas.map fun a n => a * w n) n j =
      constantOptionalRiseCoefficient alphas j *
        descendingWeightProduct w n j := by
  induction alphas generalizing n j with
  | nil =>
      cases j with
      | zero => simp [constantOptionalRiseCoefficient,
          descendingWeightProduct]
      | succ j => simp [constantOptionalRiseCoefficient,
          orderedOptionalRiseCoefficient]
  | cons a alphas ih =>
      cases j with
      | zero => simp [constantOptionalRiseCoefficient,
          descendingWeightProduct]
      | succ j =>
          have hn : 0 < n := by lia
          rw [List.map_cons, orderedOptionalRiseCoefficient,
            ite_eq_left hn, constantOptionalRiseCoefficient,
            ih hj, ih (show j ≤ n - 1 by lia),
            descendingWeightProduct_succ w (show j < n by lia)]
          ring

/-- The finite recurrence specialized to separated optional-rise weights
`a * w n`. -/
theorem weightedShiftTilingRow_succ_eq_separated
    (b : ℕ → ℝ) (alphas : List ℝ) (w : ℕ → ℝ) {N : ℕ}
    (s : Fin N) {r : ℕ} (hr : 0 < r) :
    weightedShiftTilingRow b (alphas.map fun a n => a * w n) N r s.succ =
      C (b (s.val + 1)) *
          weightedShiftTilingRow b (alphas.map fun a n => a * w n)
            N r s.castSucc +
        X * ∑ j : Fin (N + 1),
          C (if j.val + r ≤ s.succ.val then
              constantOptionalRiseCoefficient alphas
                  (s.succ.val - (j.val + r)) *
                descendingWeightProduct w s.succ.val
                  (s.succ.val - (j.val + r))
            else 0) *
              weightedShiftTilingRow b
                (alphas.map fun a n => a * w n) N r j := by
  rw [weightedShiftTilingRow_succ_eq_orderedOptionalRiseCoefficient
    b (alphas.map fun a n => a * w n) s hr]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + r ≤ s.succ.val
  · rw [ite_eq_left hj, ite_eq_left hj,
      orderedOptionalRiseCoefficient_map_mul alphas w
        (Nat.sub_le s.succ.val (j.val + r))]
  · rw [ite_eq_right hj, ite_eq_right hj]

/-- Nonnegative separated data give PF polynomial rows. -/
theorem weightedShiftTilingRow_separated_isPFPolynomial
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {alphas : List ℝ} (halphas : ∀ a ∈ alphas, 0 ≤ a)
    {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (N : ℕ) {r : ℕ} (hr : 0 < r) (i : Fin (N + 1)) :
    IsPFPolynomial
      (weightedShiftTilingRow b (alphas.map fun a n => a * w n) N r i) := by
  refine weightedShiftTilingRow_isPFPolynomial hb ?_ N hr i
  intro f hf n
  simp only [List.mem_map] at hf
  obtain ⟨a, ha, rfl⟩ := hf
  exact mul_nonneg (halphas a ha) (hw n)

/-- Consecutive rows of nonnegative separated data remain in proper position. -/
theorem prec0_weightedShiftTilingRow_separated_succ
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {alphas : List ℝ} (halphas : ∀ a ∈ alphas, 0 ≤ a)
    {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (N : ℕ) {r : ℕ} (hr : 0 < r) (i : Fin N) :
    Interl
      (weightedShiftTilingRow b (alphas.map fun a n => a * w n)
        N r i.castSucc)
      (weightedShiftTilingRow b (alphas.map fun a n => a * w n)
        N r i.succ) := by
  refine prec0_weightedShiftTilingRow_succ hb ?_ N hr i
  intro f hf n
  simp only [List.mem_map] at hf
  obtain ⟨a, ha, rfl⟩ := hf
  exact mul_nonneg (halphas a ha) (hw n)

/-- With two optional-rise factors, the displacement-`r` marked entry has
coefficient one. -/
theorem markedShiftKernel_pair_apply_displacement
    (u v : ℕ → ℝ) (N r : ℕ) (i j : Fin (N + 1))
    (hij : j.val + r = i.val) :
    markedShiftKernel [u, v] N r i j = 1 := by
  rw [markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient,
    ite_eq_left hij.le]
  simp [hij]

/-- With two optional-rise factors, the first extra lag has coefficient
`u n + v n`. -/
theorem markedShiftKernel_pair_apply_first_lag
    (u v : ℕ → ℝ) (N r : ℕ) (i j : Fin (N + 1))
    (hij : j.val + r + 1 = i.val) :
    markedShiftKernel [u, v] N r i j = u i.val + v i.val := by
  rw [markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient,
    ite_eq_left (show j.val + r ≤ i.val by lia)]
  have hlag : i.val - (j.val + r) = 1 := by lia
  rw [hlag, orderedOptionalRiseCoefficient_pair_one,
    ite_eq_left (show 0 < i.val by lia)]

/-- With two optional-rise factors, the second extra lag has the ordered
coefficient `u n * v (n - 1)`. -/
theorem markedShiftKernel_pair_apply_second_lag
    (u v : ℕ → ℝ) (N r : ℕ) (i j : Fin (N + 1))
    (hij : j.val + r + 2 = i.val) :
    markedShiftKernel [u, v] N r i j = u i.val * v (i.val - 1) := by
  rw [markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient,
    ite_eq_left (show j.val + r ≤ i.val by lia)]
  have hlag : i.val - (j.val + r) = 2 := by lia
  rw [hlag]
  exact orderedOptionalRiseCoefficient_pair_two u v
    (show 1 < i.val by lia)

/-- A two-factor marked kernel has no entries beyond its second extra lag. -/
theorem markedShiftKernel_pair_apply_eq_zero_of_second_lag_lt
    (u v : ℕ → ℝ) (N r : ℕ) (i j : Fin (N + 1))
    (hij : j.val + r + 2 < i.val) :
    markedShiftKernel [u, v] N r i j = 0 := by
  rw [markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient,
    ite_eq_left (show j.val + r ≤ i.val by lia)]
  exact orderedOptionalRiseCoefficient_eq_zero_of_length_lt [u, v]
    (show [u, v].length < i.val - (j.val + r) by simp; lia)

/-- Vanishing optional-rise weights leave only the mandatory marked shift. -/
theorem markedShiftKernel_eq_lowerShift_pow_of_weights_eq_zero
    (as : List (ℕ → ℝ)) (has : ∀ a ∈ as, ∀ n, a n = 0)
    (N r : ℕ) :
    markedShiftKernel as N r = lowerShift N ^ r := by
  have hoptional : optionalRiseMatrix as N = 1 := by
    ext i j
    rw [optionalRiseMatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases hji : j.val ≤ i.val
      · rw [ite_eq_left hji,
          orderedOptionalRiseCoefficient_eq_zero_of_weights as has
            (show 0 < i.val - j.val by lia)]
        simp [hij]
      · simp [hji, hij]
  rw [markedShiftKernel, hoptional, Matrix.one_mul]

/-- Hence zero optional-rise weights give the same polynomial rows as the
empty optional-factor list. -/
theorem weightedShiftTilingRow_eq_nil_of_weights_eq_zero
    (b : ℕ → ℝ) (as : List (ℕ → ℝ))
    (has : ∀ a ∈ as, ∀ n, a n = 0) (N r : ℕ)
    (i : Fin (N + 1)) :
    weightedShiftTilingRow b as N r i =
      weightedShiftTilingRow b [] N r i := by
  rw [weightedShiftTilingRow, weightedShiftTilingRow,
    markedShiftKernel_eq_lowerShift_pow_of_weights_eq_zero as has,
    markedShiftKernel_nil]

/-- The row sum of a two-factor marked kernel has exactly three terms once
all three displaced indices are available. -/
theorem sum_markedShiftKernel_pair
    (u v : ℕ → ℝ) (N r : ℕ) (i : Fin (N + 1))
    (hri : r + 2 ≤ i.val) (P : Fin (N + 1) → ℝ[X]) :
    (∑ j : Fin (N + 1), C (markedShiftKernel [u, v] N r i j) * P j) =
      P ⟨i.val - r, by lia⟩ +
        C (u i.val + v i.val) * P ⟨i.val - r - 1, by lia⟩ +
        C (u i.val * v (i.val - 1)) * P ⟨i.val - r - 2, by lia⟩ := by
  let j0 : Fin (N + 1) := ⟨i.val - r, by lia⟩
  let j1 : Fin (N + 1) := ⟨i.val - r - 1, by lia⟩
  let j2 : Fin (N + 1) := ⟨i.val - r - 2, by lia⟩
  have hj0 : j0.val + r = i.val := by simp only [j0]; lia
  have hj1 : j1.val + r + 1 = i.val := by simp only [j1]; lia
  have hj2 : j2.val + r + 2 = i.val := by simp only [j2]; lia
  have h01 : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; simp [j0, j1] at this; lia
  have h02 : j0 ≠ j2 := by intro h; have := congrArg Fin.val h; simp [j0, j2] at this; lia
  have h12 : j1 ≠ j2 := by intro h; have := congrArg Fin.val h; simp [j1, j2] at this; lia
  calc
    (∑ j : Fin (N + 1), C (markedShiftKernel [u, v] N r i j) * P j) =
        ∑ j ∈ ({j0, j1, j2} : Finset (Fin (N + 1))),
          C (markedShiftKernel [u, v] N r i j) * P j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      have hjne0 : j ≠ j0 := hj.1
      have hjne1 : j ≠ j1 := hj.2.1
      have hjne2 : j ≠ j2 := hj.2.2
      by_cases hle : j.val + r ≤ i.val
      · have hlt : j.val + r + 2 < i.val := by
          by_contra hnot
          have hbound : i.val ≤ j.val + r + 2 := by lia
          have hor : i.val = j.val + r ∨ i.val = j.val + r + 1 ∨
              i.val = j.val + r + 2 := by lia
          rcases hor with h | h | h
          · exact hjne0 (Fin.ext (by simp only [j0]; lia))
          · exact hjne1 (Fin.ext (by simp only [j1]; lia))
          · exact hjne2 (Fin.ext (by simp only [j2]; lia))
        rw [markedShiftKernel_pair_apply_eq_zero_of_second_lag_lt
          u v N r i j hlt, map_zero, zero_mul]
      · rw [markedShiftKernel_apply_eq_orderedOptionalRiseCoefficient,
          ite_eq_right hle, map_zero, zero_mul]
    _ = P j0 + C (u i.val + v i.val) * P j1 +
        C (u i.val * v (i.val - 1)) * P j2 := by
      simp [h01, h02, h12,
        markedShiftKernel_pair_apply_displacement u v N r i j0 hj0,
        markedShiftKernel_pair_apply_first_lag u v N r i j1 hj1,
        markedShiftKernel_pair_apply_second_lag u v N r i j2 hj2]
      ring
    _ = P ⟨i.val - r, by lia⟩ +
        C (u i.val + v i.val) * P ⟨i.val - r - 1, by lia⟩ +
        C (u i.val * v (i.val - 1)) * P ⟨i.val - r - 2, by lia⟩ := rfl

/-- Exact three-term marked part of the two-factor nonstationary recurrence. -/
theorem weightedShiftTilingRow_pair_succ_eq
    (b u v : ℕ → ℝ) {N : ℕ} (s : Fin N) {r : ℕ}
    (hr : 0 < r) (hri : r + 2 ≤ s.succ.val) :
    weightedShiftTilingRow b [u, v] N r s.succ =
      C (b (s.val + 1)) * weightedShiftTilingRow b [u, v] N r s.castSucc +
        X * (weightedShiftTilingRow b [u, v] N r
              ⟨s.succ.val - r, by lia⟩ +
          C (u s.succ.val + v s.succ.val) *
            weightedShiftTilingRow b [u, v] N r
              ⟨s.succ.val - r - 1, by lia⟩ +
          C (u s.succ.val * v (s.succ.val - 1)) *
            weightedShiftTilingRow b [u, v] N r
              ⟨s.succ.val - r - 2, by lia⟩) := by
  rw [weightedShiftTilingRow_succ_eq b [u, v] s hr,
    sum_markedShiftKernel_pair u v N r s.succ hri]

/-- The constant coefficient is the ordinary product of the background
weights at positive levels up to the row index. -/
theorem coeff_zero_weightedShiftTilingRow_eq_prod_range
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) (N r : ℕ)
    (i : Fin (N + 1)) :
    (weightedShiftTilingRow b as N r i).coeff 0 =
      ∏ k ∈ Finset.range i.val, b (k + 1) := by
  rw [coeff_zero_weightedShiftTilingRow,
    descendingWeightProduct_self_eq_prod_range]

/-- The row at level zero is the initial polynomial `1`. -/
@[simp]
theorem weightedShiftTilingRow_zero
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) (N : ℕ)
    {r : ℕ} (hr : 0 < r) :
    weightedShiftTilingRow b as N r 0 = 1 := by
  have hG : ∀ i j : Fin (N + 1), i < j →
      weightedGreenKernel b N i j = 0 := by
    intro i j hij
    exact weightedGreenKernel_apply_eq_zero_of_lt b N hij
  have hK : ∀ i j : Fin (N + 1), i.val ≤ j.val →
      markedShiftKernel as N r i j = 0 := by
    intro i j hij
    exact markedShiftKernel_apply_eq_zero_of_le as N hr hij
  have hdegree : (weightedShiftTilingRow b as N r 0).natDegree ≤ 0 :=
    natDegree_kernelRow_le_row (weightedGreenKernel b N)
      (markedShiftKernel as N r) hG hK 0
  rw [Polynomial.eq_C_of_natDegree_le_zero hdegree,
    coeff_zero_weightedShiftTilingRow]
  simp [descendingWeightProduct]

/-- If the mandatory shift is longer than the finite level range, every row
is the corresponding constant Green-path weight. -/
theorem weightedShiftTilingRow_eq_C_of_lt
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) {N r : ℕ}
    (hNr : N < r) (i : Fin (N + 1)) :
    weightedShiftTilingRow b as N r i =
      C (descendingWeightProduct b i.val i.val) := by
  rw [weightedShiftTilingRow,
    markedShiftKernel_eq_zero_of_lt as hNr,
    kernelRow_zero_kernel, weightedGreenKernel_apply]
  simp

/-- A zero background weight among levels `1, ..., i` forces the row's
constant coefficient to vanish. -/
theorem coeff_zero_weightedShiftTilingRow_eq_zero_of_weight_eq_zero
    (b : ℕ → ℝ) (as : List (ℕ → ℝ)) (N r : ℕ)
    (i : Fin (N + 1)) {k : ℕ} (hk : k < i.val) (hbk : b (k + 1) = 0) :
    (weightedShiftTilingRow b as N r i).coeff 0 = 0 := by
  rw [coeff_zero_weightedShiftTilingRow_eq_prod_range]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hk) hbk

/-- Under nonnegative marked weights and positive background weights, all roots
of every tiling row are strictly negative. -/
theorem weightedShiftTilingRow_roots_neg
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    {as : List (ℕ → ℝ)} (has : ∀ a ∈ as, ∀ n, 0 ≤ a n)
    (N : ℕ) {r : ℕ} (hr : 0 < r) (i : Fin (N + 1))
    (x : ℝ) (hx : x ∈ (weightedShiftTilingRow b as N r i).roots) :
    x < 0 := by
  exact (weightedShiftTilingRow_isPFPolynomial (fun n => (hb n).le)
    has N hr i).roots_neg_of_coeff_zero_ne
      (ne_of_gt (coeff_zero_weightedShiftTilingRow_pos hb as N r i)) x hx

end

end RealRooted.BrandenLeite
