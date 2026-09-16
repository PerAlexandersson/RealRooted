import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import RealRooted.Mathlib.LinearAlgebra.Matrix.StrictLower
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# Finite weighted lower shifts

This file defines the finite weighted lower shift used by position-dependent
tiling kernels.  Its strict-lower support makes the finite geometric sum an
exact two-sided resolvent, without an infinite matrix inverse.
-/

namespace RealRooted.BrandenLeite

noncomputable section

open scoped BigOperators

/-- The weighted lower shift on levels `0, ..., N`, with entry `b i` from
level `i - 1` to level `i`. -/
def weightedLowerShift {R : Type*} [Zero R]
    (b : ℕ → R) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j => if i.val = j.val + 1 then b i else 0

@[simp]
theorem weightedLowerShift_apply {R : Type*} [Zero R]
    (b : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    weightedLowerShift b N i j =
      if i.val = j.val + 1 then b i else 0 :=
  rfl

/-- The unweighted lower shift on levels `0, ..., N`. -/
def lowerShift {R : Type*} [Zero R] [One R]
    (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  weightedLowerShift (fun _ => 1) N

@[simp]
theorem lowerShift_apply {R : Type*} [Zero R] [One R]
    (N : ℕ) (i j : Fin (N + 1)) :
    lowerShift N i j = if i.val = j.val + 1 then 1 else 0 := by
  simp [lowerShift]

/-- A weighted lower shift vanishes on and above the diagonal. -/
theorem weightedLowerShift_apply_eq_zero_of_le
    {R : Type*} [Zero R] (b : ℕ → R) (N : ℕ)
    {i j : Fin (N + 1)} (hij : i.val ≤ j.val) :
    weightedLowerShift b N i j = 0 := by
  rw [weightedLowerShift_apply]
  simp [show i.val ≠ j.val + 1 by lia]

/-- Powers of a weighted lower shift have the sharp support displacement. -/
theorem weightedLowerShift_pow_apply_eq_zero_of_lt_add
    {R : Type*} [Semiring R] (b : ℕ → R) (N q : ℕ)
    {i j : Fin (N + 1)} (hij : i.val < j.val + q) :
    (weightedLowerShift b N ^ q) i j = 0 := by
  exact Matrix.pow_apply_eq_zero_of_lt_add_of_strictLower
    (weightedLowerShift b N)
    (fun i j hle => weightedLowerShift_apply_eq_zero_of_le b N hle) hij

/-- The weight of the unique descending path of length `q` ending at level
`i`; the support condition below ensures that none of the subtractions
truncate. -/
def descendingWeightProduct {R : Type*} [CommMonoid R]
    (b : ℕ → R) (i q : ℕ) : R :=
  ∏ t ∈ Finset.range q, b (i - t)

/-- A power of the weighted shift has a single possible path between any two
fixed levels. -/
theorem weightedLowerShift_pow_apply
    {R : Type*} [CommSemiring R] (b : ℕ → R) (N q : ℕ)
    (i j : Fin (N + 1)) :
    (weightedLowerShift b N ^ q) i j =
      if i.val = j.val + q then descendingWeightProduct b i.val q else 0 := by
  induction q generalizing i j with
  | zero =>
      by_cases hij : i = j
      · subst i
        simp [descendingWeightProduct]
      · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [hij, hval]
  | succ q ih =>
      rw [pow_succ, Matrix.mul_apply]
      by_cases hj : j.val + 1 < N + 1
      · let k : Fin (N + 1) := ⟨j.val + 1, hj⟩
        rw [Finset.sum_eq_single k]
        · rw [weightedLowerShift_apply, if_pos (by rfl), ih]
          by_cases hi : i.val = j.val + (q + 1)
          · rw [if_pos hi]
            have hik : i.val = k.val + q := by
              simp only [k]
              lia
            rw [if_pos hik, descendingWeightProduct,
              descendingWeightProduct, Finset.prod_range_succ]
            congr 1
            simp only [k]
            congr 1
            lia
          · rw [if_neg hi]
            have hik : i.val ≠ k.val + q := by
              simp only [k]
              lia
            rw [if_neg hik, zero_mul]
        · intro k' _ hk'
          rw [weightedLowerShift_apply]
          have hne : k'.val ≠ j.val + 1 := by
            intro heq
            exact hk' (Fin.ext (heq.trans (by rfl)))
          simp [hne]
        · simp
      · have hjmax : j.val = N := by lia
        have hzero (k : Fin (N + 1)) : weightedLowerShift b N k j = 0 := by
          rw [weightedLowerShift_apply]
          simp [show k.val ≠ j.val + 1 by lia]
        rw [Finset.sum_eq_zero (fun k _ => by rw [hzero k, mul_zero])]
        have hne : i.val ≠ j.val + (q + 1) := by lia
        rw [if_neg hne]

/-- On `N + 1` levels, every weighted lower shift is nilpotent at exponent
`N + 1`. -/
theorem weightedLowerShift_pow_card_eq_zero
    {R : Type*} [Semiring R] (b : ℕ → R) (N : ℕ) :
    weightedLowerShift b N ^ (N + 1) = 0 := by
  exact Matrix.pow_card_eq_zero_of_strictLower
    (weightedLowerShift b N)
    (fun i j hle => weightedLowerShift_apply_eq_zero_of_le b N hle)

/-- Nonnegative weights make the finite weighted shift totally nonnegative. -/
theorem weightedLowerShift_isTotallyNonneg
    {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
    {b : ℕ → R} (hb : ∀ i, 0 ≤ b i) (N : ℕ) :
    (weightedLowerShift b N).IsTotallyNonneg := by
  have heq : weightedLowerShift b N =
      Matrix.lowerBidiagonalFin (N + 1) 0 (fun j => b (j + 1)) := by
    ext i j
    rw [weightedLowerShift_apply, Matrix.lowerBidiagonalFin_apply]
    by_cases hij : i = j
    · subst i
      simp
    · by_cases hsucc : i.val = j.val + 1
      · simp [hij, hsucc]
      · simp [hij, hsucc]
  rw [heq]
  exact Matrix.isTotallyNonneg_lowerBidiagonalFin
    (N + 1) 0 (fun j => b (j + 1)) (by simp) (fun i => hb (i + 1))

/-- The elementary chip which adds `b (s+1)` times row `s` to row `s+1`. -/
def weightedLowerChip (b : ℕ → ℝ) {N : ℕ} (s : Fin N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.transvection s.succ s.castSucc (b (s.val + 1))

/-- Every nonnegative elementary weighted lower chip is totally
nonnegative. -/
theorem weightedLowerChip_isTotallyNonneg
    {b : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) {N : ℕ} (s : Fin N) :
    (weightedLowerChip b s).IsTotallyNonneg := by
  have heq : weightedLowerChip b s =
      Matrix.lowerBidiagonalFin (N + 1) (fun _ => 1)
        (fun j => if j = s.val then b (s.val + 1) else 0) := by
    ext i j
    simp only [weightedLowerChip, Matrix.transvection,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Matrix.lowerBidiagonalFin_apply]
    by_cases hij : i = j
    · subst i
      have hboth : ¬(s.succ = j ∧ s.castSucc = j) := by
        rintro ⟨h1, h2⟩
        exact (Fin.ne_of_gt s.castSucc_lt_succ) (h1.trans h2.symm)
      simp [hboth]
    · by_cases hsub : i.val = j.val + 1
      · by_cases hjs : j.val = s.val
        · have hj : j = s.castSucc := Fin.ext hjs
          have hi : i = s.succ := Fin.ext (by simpa [hjs] using hsub)
          subst i
          subst j
          simp [Fin.ne_of_gt s.castSucc_lt_succ]
        · have hsingle : ¬(s.succ = i ∧ s.castSucc = j) := by
            rintro ⟨_, hs'⟩
            exact hjs (by simpa using (congrArg Fin.val hs').symm)
          simp [hij, hsub, hjs, hsingle]
      · have hsingle : ¬(s.succ = i ∧ s.castSucc = j) := by
          rintro ⟨hi, hj⟩
          apply hsub
          rw [← hi, ← hj]
          simp
        simp [hij, hsub, hsingle]
  rw [heq]
  exact Matrix.isTotallyNonneg_lowerBidiagonalFin
    (N + 1) (fun _ => 1)
      (fun j => if j = s.val then b (s.val + 1) else 0)
      (by simp) (by
        intro j
        by_cases hjs : j = s.val
        · simp [hjs, hb]
        · simp [hjs])

/-- Left multiplication by a weighted lower chip performs the corresponding
adjacent row addition. -/
theorem weightedLowerChip_mul_apply
    (b : ℕ → ℝ) {N : ℕ} (s : Fin N)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (i j : Fin (N + 1)) :
    (weightedLowerChip b s * A) i j =
      if i = s.succ then
        A i j + b (s.val + 1) * A s.castSucc j
      else A i j := by
  by_cases his : i = s.succ
  · subst i
    simp [weightedLowerChip]
  · rw [if_neg his]
    exact Matrix.transvection_mul_apply_of_ne
      s.succ s.castSucc i j his (b (s.val + 1)) A

/-- Multiplication by the weighted shift reads the preceding row. -/
theorem weightedLowerShift_mul_apply_succ
    (b : ℕ → ℝ) {N : ℕ} (s : Fin N)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (j : Fin (N + 1)) :
    (weightedLowerShift b N * A) s.succ j =
      b (s.val + 1) * A s.castSucc j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s.castSucc]
  · simp [weightedLowerShift_apply]
  · intro k _ hks
    rw [weightedLowerShift_apply, if_neg, zero_mul]
    intro heq
    apply hks
    exact Fin.ext (by simpa using heq.symm)
  · simp

/-- The finite Green kernel `I + B + ... + B^N`. -/
def weightedGreenKernel {R : Type*} [Semiring R]
    (b : ℕ → R) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.finiteGeomSum (weightedLowerShift b N) (N + 1)

/-- Explicit path-product entry of the finite Green kernel. -/
theorem weightedGreenKernel_apply
    {R : Type*} [CommSemiring R] (b : ℕ → R) (N : ℕ)
    (i j : Fin (N + 1)) :
    weightedGreenKernel b N i j =
      if j.val ≤ i.val then
        descendingWeightProduct b i.val (i.val - j.val)
      else 0 := by
  rw [weightedGreenKernel, Matrix.finiteGeomSum]
  rw [Matrix.sum_apply]
  simp_rw [weightedLowerShift_pow_apply]
  by_cases hji : j.val ≤ i.val
  · rw [if_pos hji]
    let q := i.val - j.val
    have hq : q ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      dsimp only [q]
      lia
    rw [Finset.sum_eq_single q]
    · rw [if_pos]
      dsimp only [q]
      lia
    · intro q' hq' hne
      rw [if_neg]
      intro heq
      apply hne
      dsimp only [q]
      lia
    · exact fun h => (h hq).elim
  · rw [if_neg hji]
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg]
    intro heq
    exact hji (by lia)

/-- The finite Green kernel is lower triangular. -/
theorem weightedGreenKernel_apply_eq_zero_of_lt
    {R : Type*} [CommSemiring R] (b : ℕ → R) (N : ℕ)
    {i j : Fin (N + 1)} (hij : i < j) :
    weightedGreenKernel b N i j = 0 := by
  rw [weightedGreenKernel_apply, if_neg]
  exact fun h => (not_le_of_gt (Fin.mk_lt_mk.mp hij)) h

/-- Every finite Green kernel has diagonal one. -/
@[simp]
theorem weightedGreenKernel_apply_self
    {R : Type*} [CommSemiring R] (b : ℕ → R) (N : ℕ)
    (i : Fin (N + 1)) :
    weightedGreenKernel b N i i = 1 := by
  simp [weightedGreenKernel_apply, descendingWeightProduct]

/-- The finite Green kernel is a right inverse of `I - B`. -/
theorem weightedGreenKernel_mul_one_sub
    {R : Type*} [Ring R] (b : ℕ → R) (N : ℕ) :
    weightedGreenKernel b N * (1 - weightedLowerShift b N) = 1 := by
  apply Matrix.finiteGeomSum_mul_one_sub_of_pow_eq_zero
  exact weightedLowerShift_pow_card_eq_zero b N

/-- The finite Green kernel is a left inverse of `I - B`. -/
theorem one_sub_mul_weightedGreenKernel
    {R : Type*} [Ring R] (b : ℕ → R) (N : ℕ) :
    (1 - weightedLowerShift b N) * weightedGreenKernel b N = 1 := by
  apply Matrix.one_sub_mul_finiteGeomSum_of_pow_eq_zero
  exact weightedLowerShift_pow_card_eq_zero b N

/-- Consecutive Green-kernel rows satisfy the elementary weighted prefix
recurrence. -/
theorem weightedGreenKernel_apply_succ
    (b : ℕ → ℝ) {N : ℕ} (s : Fin N) (j : Fin (N + 1)) :
    weightedGreenKernel b N s.succ j =
      (if s.succ = j then 1 else 0) +
        b (s.val + 1) * weightedGreenKernel b N s.castSucc j := by
  have h := congrArg (fun A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ =>
      A s.succ j) (one_sub_mul_weightedGreenKernel b N)
  rw [Matrix.sub_mul, Matrix.one_mul] at h
  have hentry :
      weightedGreenKernel b N s.succ j -
          (weightedLowerShift b N * weightedGreenKernel b N) s.succ j =
        if s.succ = j then 1 else 0 := by
    simpa only [Matrix.sub_apply, Matrix.one_apply] using h
  rw [weightedLowerShift_mul_apply_succ] at hentry
  exact (sub_eq_iff_eq_add).mp hentry

/-- The first `k` adjacent chips, in descending matrix-product order. -/
def weightedLowerChipPrefix (b : ℕ → ℝ) (N : ℕ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => 1
  | k + 1 =>
      if hk : k < N then
        weightedLowerChip b (⟨k, hk⟩ : Fin N) *
          weightedLowerChipPrefix b N k
      else weightedLowerChipPrefix b N k

/-- The chip prefix agrees with the Green kernel through row `k` and with the
identity on all later rows. -/
theorem weightedLowerChipPrefix_apply
    (b : ℕ → ℝ) (N : ℕ) {k : ℕ} (hk : k ≤ N)
    (i j : Fin (N + 1)) :
    weightedLowerChipPrefix b N k i j =
      if i.val ≤ k then weightedGreenKernel b N i j
      else (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j := by
  induction k generalizing i j with
  | zero =>
      rw [weightedLowerChipPrefix]
      by_cases hi : i.val ≤ 0
      · have hi0 : i.val = 0 := by lia
        rw [if_pos hi]
        by_cases hij : i = j
        · subst j
          simp
        · have hjpos : 0 < j.val := by
            have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
            lia
          rw [weightedGreenKernel_apply_eq_zero_of_lt b N
            (Fin.mk_lt_mk.mpr (by lia))]
          simp [hij]
      · rw [if_neg hi]
  | succ k ih =>
      have hkN : k < N := Nat.lt_of_succ_le hk
      rw [weightedLowerChipPrefix, dif_pos hkN,
        weightedLowerChip_mul_apply]
      let s : Fin N := ⟨k, hkN⟩
      by_cases his : i = s.succ
      · rw [if_pos his]
        subst i
        have hs_le : s.succ.val ≤ k + 1 := by simp [s]
        rw [if_pos hs_le, ih (Nat.le_of_lt hkN),
          ih (Nat.le_of_lt hkN)]
        simp only [s, Fin.val_succ, Fin.val_castSucc]
        rw [if_neg (by lia), if_pos (by lia)]
        rw [Matrix.one_apply]
        simpa [s] using (weightedGreenKernel_apply_succ b s j).symm
      · rw [if_neg his, ih (Nat.le_of_lt hkN)]
        by_cases hik : i.val ≤ k
        · rw [if_pos hik, if_pos (by lia)]
        · have hnext : ¬i.val ≤ k + 1 := by
            intro hle
            have hieq : i.val = k + 1 := by lia
            exact his (Fin.ext (by simpa [s] using hieq))
          rw [if_neg hik, if_neg hnext]

/-- Every bounded elementary-chip prefix is totally nonnegative. -/
theorem weightedLowerChipPrefix_isTotallyNonneg
    {b : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) (N : ℕ)
    {k : ℕ} (hk : k ≤ N) :
    (weightedLowerChipPrefix b N k).IsTotallyNonneg := by
  induction k with
  | zero =>
      have h := (Matrix.IsTotallyNonneg.one (R := ℝ)).submatrix
        (f := fun i : Fin (N + 1) => i.val)
        (g := fun i : Fin (N + 1) => i.val)
        Fin.val_strictMono Fin.val_strictMono
      simpa [weightedLowerChipPrefix,
        Matrix.submatrix_one Fin.val Fin.val_injective] using h
  | succ k ih =>
      have hkN : k < N := Nat.lt_of_succ_le hk
      rw [weightedLowerChipPrefix, dif_pos hkN]
      exact (weightedLowerChip_isTotallyNonneg hb ⟨k, hkN⟩).mul
        (ih (Nat.le_of_lt hkN))

/-- The explicit descending product of all adjacent weighted lower chips. -/
def weightedLowerChipProduct (b : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  weightedLowerChipPrefix b N N

/-- The finite geometric Green kernel is exactly the descending elementary
chip product. -/
theorem weightedGreenKernel_eq_weightedLowerChipProduct
    (b : ℕ → ℝ) (N : ℕ) :
    weightedGreenKernel b N = weightedLowerChipProduct b N := by
  ext i j
  rw [weightedLowerChipProduct,
    weightedLowerChipPrefix_apply b N (le_refl N),
    if_pos (Nat.le_of_lt_succ i.isLt)]

/-- Nonnegative weights make the finite Green kernel totally nonnegative. -/
theorem weightedGreenKernel_isTotallyNonneg
    {b : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) (N : ℕ) :
    (weightedGreenKernel b N).IsTotallyNonneg := by
  rw [weightedGreenKernel_eq_weightedLowerChipProduct]
  exact weightedLowerChipPrefix_isTotallyNonneg hb N (le_refl N)

/-- On the single level `N = 0`, the Green kernel and empty chip product are
both the identity. -/
theorem weightedGreenKernel_zero (b : ℕ → ℝ) :
    weightedGreenKernel b 0 = 1 := by
  rw [weightedGreenKernel_eq_weightedLowerChipProduct]
  rfl

end

end RealRooted.BrandenLeite
