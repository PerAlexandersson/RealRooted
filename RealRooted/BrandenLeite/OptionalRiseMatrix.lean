import RealRooted.BrandenLeite.WeightedShift

/-!
# Position-dependent optional-rise matrices

This file packages fixed-order products of matrices `I + D*S`, where each
diagonal weight family may depend on the current level.  The ordering matters:
choosing a lower-shift entry changes the level read by every later factor.
-/

namespace RealRooted.BrandenLeite

noncomputable section

/-- One position-dependent optional-rise factor `I + D*S`. -/
def optionalRiseMatrixFactor (a : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  1 + weightedLowerShift a N

@[simp]
theorem optionalRiseMatrixFactor_apply
    (a : ℕ → ℝ) (N : ℕ) (i j : Fin (N + 1)) :
    optionalRiseMatrixFactor a N i j =
      if i = j then 1 else if i.val = j.val + 1 then a i else 0 := by
  rw [optionalRiseMatrixFactor, Matrix.add_apply,
    Matrix.one_apply, weightedLowerShift_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- A nonnegative optional-rise factor is totally nonnegative. -/
theorem optionalRiseMatrixFactor_isTotallyNonneg
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (N : ℕ) :
    (optionalRiseMatrixFactor a N).IsTotallyNonneg := by
  have heq : optionalRiseMatrixFactor a N =
      Matrix.lowerBidiagonalFin (N + 1) (fun _ => 1)
        (fun j => a (j + 1)) := by
    ext i j
    rw [optionalRiseMatrixFactor_apply,
      Matrix.lowerBidiagonalFin_apply]
    by_cases hij : i = j
    · simp [hij]
    · by_cases hsub : i.val = j.val + 1
      · simp [hij, hsub]
      · simp [hij, hsub]
  rw [heq]
  exact Matrix.isTotallyNonneg_lowerBidiagonalFin
    (N + 1) (fun _ => 1) (fun j => a (j + 1))
      (by simp) (fun j => ha (j + 1))

/-- Left multiplication by one optional-rise factor either stays at the
current level or reads the preceding row. -/
theorem optionalRiseMatrixFactor_mul_apply
    (a : ℕ → ℝ) (N : ℕ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (i j : Fin (N + 1)) :
    (optionalRiseMatrixFactor a N * A) i j =
      A i j + if 0 < i.val then
        a i * A ⟨i.val - 1, by lia⟩ j
      else 0 := by
  rw [optionalRiseMatrixFactor, Matrix.add_mul,
    Matrix.one_mul, Matrix.add_apply]
  by_cases hi : 0 < i.val
  · rw [ite_eq_left hi]
    let s : Fin N := ⟨i.val - 1, by lia⟩
    have his : s.succ = i := Fin.ext (by simp [s]; lia)
    rw [← his, weightedLowerShift_mul_apply_succ]
    simp [s]
  · rw [ite_eq_right hi, add_zero]
    have hsum : (weightedLowerShift a N * A) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k hk
      rw [weightedLowerShift_apply, ite_eq_right, zero_mul]
      lia
    rw [hsum, add_zero]

/-- Fixed-order product of position-dependent optional-rise factors. -/
def optionalRiseMatrix (as : List (ℕ → ℝ)) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (as.map fun a => optionalRiseMatrixFactor a N).prod

@[simp]
theorem optionalRiseMatrix_nil (N : ℕ) :
    optionalRiseMatrix [] N = 1 := by
  simp [optionalRiseMatrix]

@[simp]
theorem optionalRiseMatrix_cons
    (a : ℕ → ℝ) (as : List (ℕ → ℝ)) (N : ℕ) :
    optionalRiseMatrix (a :: as) N =
      optionalRiseMatrixFactor a N * optionalRiseMatrix as N := by
  simp [optionalRiseMatrix]

/-- A fixed-order product of nonnegative optional-rise factors is totally
nonnegative. -/
theorem optionalRiseMatrix_isTotallyNonneg
    {as : List (ℕ → ℝ)} (has : ∀ a ∈ as, ∀ n, 0 ≤ a n) (N : ℕ) :
    (optionalRiseMatrix as N).IsTotallyNonneg := by
  induction as with
  | nil =>
      simp [optionalRiseMatrix, Matrix.IsTotallyNonneg.one]
  | cons a as ih =>
      rw [optionalRiseMatrix_cons]
      exact (optionalRiseMatrixFactor_isTotallyNonneg
        (fun n => has a (by simp) n) N).mul
          (ih (fun a ha n => has a (by simp [ha]) n))

/-- Ordered selection coefficients.  In the second summand the first factor
is selected, so all later selections are read one level lower. -/
def orderedOptionalRiseCoefficient : List (ℕ → ℝ) → ℕ → ℕ → ℝ
  | [], _, 0 => 1
  | [], _, _ + 1 => 0
  | _ :: _, _, 0 => 1
  | a :: as, n, j + 1 =>
      orderedOptionalRiseCoefficient as n (j + 1) +
        if 0 < n then
          a n * orderedOptionalRiseCoefficient as (n - 1) j
        else 0

/-- Weight of one strictly ordered selection of rise factors.  Each selected
factor lowers the level read by the next selected factor. -/
def strictRiseSelectionWeight : List (ℕ → ℝ) → ℕ → ℝ
  | [], _ => 1
  | a :: as, n =>
      if 0 < n then a n * strictRiseSelectionWeight as (n - 1) else 0

@[simp]
theorem orderedOptionalRiseCoefficient_zero
    (as : List (ℕ → ℝ)) (n : ℕ) :
    orderedOptionalRiseCoefficient as n 0 = 1 := by
  cases as <;> rfl

/-- One cannot select more rises than there are factors. -/
theorem orderedOptionalRiseCoefficient_eq_zero_of_length_lt
    (as : List (ℕ → ℝ)) {n j : ℕ} (h : as.length < j) :
    orderedOptionalRiseCoefficient as n j = 0 := by
  induction as generalizing n j with
  | nil =>
      cases j with
      | zero => simp at h
      | succ j => rfl
  | cons a as ih =>
      cases j with
      | zero => simp at h
      | succ j =>
          rw [orderedOptionalRiseCoefficient]
          have hj : as.length < j := by simp at h; lia
          rw [ih (by lia)]
          by_cases hn : 0 < n
          · rw [ite_eq_left hn, ih hj, mul_zero, add_zero]
          · rw [ite_eq_right hn, add_zero]

/-- One cannot make more strict rises than the starting level permits. -/
theorem orderedOptionalRiseCoefficient_eq_zero_of_lt
    (as : List (ℕ → ℝ)) {n j : ℕ} (h : n < j) :
    orderedOptionalRiseCoefficient as n j = 0 := by
  induction as generalizing n j with
  | nil =>
      cases j with
      | zero => simp at h
      | succ j => rfl
  | cons a as ih =>
      cases j with
      | zero => simp at h
      | succ j =>
          rw [orderedOptionalRiseCoefficient, ih h]
          by_cases hn : 0 < n
          · rw [ite_eq_left hn, ih (by lia), mul_zero, add_zero]
          · rw [ite_eq_right hn, add_zero]

/-- Positive-lag coefficients vanish when every optional-rise weight is zero. -/
theorem orderedOptionalRiseCoefficient_eq_zero_of_weights
    (as : List (ℕ → ℝ))
    (has : ∀ a ∈ as, ∀ n, a n = 0) {n j : ℕ} (hj : 0 < j) :
    orderedOptionalRiseCoefficient as n j = 0 := by
  induction as generalizing n j with
  | nil =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      rfl
  | cons a as ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      rw [orderedOptionalRiseCoefficient,
        ih (fun b hb m => has b (by simp [hb]) m) (by simp),
        has a (by simp) n]
      simp

/-- The ordered coefficient is the finite sum over all length-`j` sublists of
the factor list.  Such sublists are precisely the strictly increasing choices
of factor positions, and `strictRiseSelectionWeight` evaluates their successive
factors at levels `n`, `n - 1`, ..., in that order. -/
theorem orderedOptionalRiseCoefficient_eq_sum_sublistsLen
    (as : List (ℕ → ℝ)) (n j : ℕ) :
    orderedOptionalRiseCoefficient as n j =
      ((as.sublistsLen j).map fun bs =>
        strictRiseSelectionWeight bs n).sum := by
  induction as generalizing n j with
  | nil =>
      cases j <;>
        simp [orderedOptionalRiseCoefficient, strictRiseSelectionWeight]
  | cons a as ih =>
      cases j with
      | zero =>
          simp [orderedOptionalRiseCoefficient, strictRiseSelectionWeight]
      | succ j =>
          rw [orderedOptionalRiseCoefficient,
            List.sublistsLen_succ_cons, List.map_append, List.sum_append,
            ih]
          simp only [List.map_map]
          by_cases hn : 0 < n
          · rw [ite_eq_left hn, ih]
            congr 1
            change a n *
                (List.map (fun bs => strictRiseSelectionWeight bs (n - 1))
                  (List.sublistsLen j as)).sum =
              (List.map (fun bs => strictRiseSelectionWeight (a :: bs) n)
                (List.sublistsLen j as)).sum
            simp_rw [strictRiseSelectionWeight, ite_eq_left hn]
            rw [List.sum_map_mul_left]
          · rw [ite_eq_right hn]
            have hsum : (List.map
                ((fun bs => strictRiseSelectionWeight bs n) ∘ List.cons a)
                  (List.sublistsLen j as)).sum = 0 := by
              change (List.map
                (fun bs => strictRiseSelectionWeight (a :: bs) n)
                  (List.sublistsLen j as)).sum = 0
              simp_rw [strictRiseSelectionWeight, ite_eq_right hn]
              simp
            rw [hsum, add_zero]

@[simp]
theorem orderedOptionalRiseCoefficient_pair_one
    (a b : ℕ → ℝ) (n : ℕ) :
    orderedOptionalRiseCoefficient [a, b] n 1 =
      if 0 < n then a n + b n else 0 := by
  by_cases hn : 0 < n <;>
    simp [orderedOptionalRiseCoefficient, hn, add_comm]

theorem orderedOptionalRiseCoefficient_pair_two
    (a b : ℕ → ℝ) {n : ℕ} (hn : 1 < n) :
    orderedOptionalRiseCoefficient [a, b] n 2 = a n * b (n - 1) := by
  have hn0 : 0 < n := by lia
  have hn1 : 0 < n - 1 := by lia
  simp [orderedOptionalRiseCoefficient, hn0, hn1]

/-- Matrix entries are the ordered selection coefficients. -/
theorem optionalRiseMatrix_apply
    (as : List (ℕ → ℝ)) (N : ℕ) (i j : Fin (N + 1)) :
    optionalRiseMatrix as N i j =
      if j.val ≤ i.val then
        orderedOptionalRiseCoefficient as i.val (i.val - j.val)
      else 0 := by
  induction as generalizing i j with
  | nil =>
      rw [optionalRiseMatrix_nil]
      by_cases hij : i = j
      · subst j
        simp
      · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
        rcases lt_or_gt_of_ne hval with hijlt | hjilt
        · rw [ite_eq_right (Nat.not_le_of_lt hijlt)]
          simp [hij]
        · rw [ite_eq_left (Nat.le_of_lt hjilt)]
          have hsub : 0 < i.val - j.val := Nat.sub_pos_of_lt hjilt
          obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hsub.ne'
          rw [hq]
          simp [hij, orderedOptionalRiseCoefficient]
  | cons a as ih =>
      rw [optionalRiseMatrix_cons,
        optionalRiseMatrixFactor_mul_apply]
      by_cases hji : j.val ≤ i.val
      · rw [ite_eq_left hji]
        by_cases hij : i = j
        · subst j
          rw [ih, ite_eq_left (le_refl i.val)]
          by_cases hi : 0 < i.val
          · rw [ite_eq_left hi, ih, ite_eq_right (by simp; lia)]
            simp
          · rw [ite_eq_right hi]
            simp
        · have hji' : j.val < i.val := lt_of_le_of_ne hji (Ne.symm
            (fun h => hij (Fin.ext h)))
          have hi : 0 < i.val := lt_of_le_of_lt (Nat.zero_le j.val) hji'
          let p : Fin (N + 1) := ⟨i.val - 1, by lia⟩
          have hjp : j.val ≤ p.val := by simp only [p]; lia
          rw [ite_eq_left hi, ih, ih, ite_eq_left hji, ite_eq_left hjp]
          have hlag : i.val - j.val = (i.val - j.val - 1) + 1 := by
            lia
          rw [hlag, orderedOptionalRiseCoefficient]
          congr 2
          · lia
      · rw [ite_eq_right hji]
        have hijlt : i.val < j.val := Nat.lt_of_not_ge hji
        rw [ih, ite_eq_right (Nat.not_le_of_lt hijlt)]
        by_cases hi : 0 < i.val
        · rw [ite_eq_left hi, ih, ite_eq_right]
          · simp
          · simp
            lia
        · rw [ite_eq_right hi, add_zero]

@[simp]
theorem optionalRiseMatrix_apply_self
    (as : List (ℕ → ℝ)) (N : ℕ) (i : Fin (N + 1)) :
    optionalRiseMatrix as N i i = 1 := by
  simp [optionalRiseMatrix_apply]

theorem optionalRiseMatrix_apply_eq_zero_of_lt
    (as : List (ℕ → ℝ)) (N : ℕ) {i j : Fin (N + 1)}
    (h : i.val < j.val) :
    optionalRiseMatrix as N i j = 0 := by
  rw [optionalRiseMatrix_apply, ite_eq_right (Nat.not_le_of_lt h)]

/-- Direct matrix-entry form of the ordered strict-selection formula. -/
theorem optionalRiseMatrix_apply_eq_sum_sublistsLen
    (as : List (ℕ → ℝ)) (N : ℕ) {i j : Fin (N + 1)}
    (h : j.val ≤ i.val) :
    optionalRiseMatrix as N i j =
      ((as.sublistsLen (i.val - j.val)).map fun bs =>
        strictRiseSelectionWeight bs i.val).sum := by
  rw [optionalRiseMatrix_apply, ite_eq_left h,
    orderedOptionalRiseCoefficient_eq_sum_sublistsLen]

/-- The ordered product is lower unitriangular, expressed by its two defining
entry conditions on the finite index type. -/
theorem optionalRiseMatrix_lower_unitriangular
    (as : List (ℕ → ℝ)) (N : ℕ) :
    (∀ i j : Fin (N + 1), i.val < j.val →
      optionalRiseMatrix as N i j = 0) ∧
    ∀ i : Fin (N + 1), optionalRiseMatrix as N i i = 1 := by
  exact ⟨fun i j => optionalRiseMatrix_apply_eq_zero_of_lt as N,
    optionalRiseMatrix_apply_self as N⟩

end

end RealRooted.BrandenLeite
