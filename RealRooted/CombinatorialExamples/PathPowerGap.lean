import RealRooted.Mathlib.Algebra.LinearRecurrence.Subsequence
import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# Gap recurrences for path-power clique polynomials

The path-power family `Q (N + k) = Q (N + k - 1) + Y * Q N` (`k = 3, 4`) is the orbit of a
companion matrix, so by `LinearRecurrence.ofMatrix_pow_isSolution_subsequence` every `p`-step
subsequence satisfies the recurrence of `charpoly (A ^ p)`. This file computes those
characteristic polynomials for the cases used by the path-power row tactic,
`(k, p) = (3, 2), (3, 3), (4, 3), (4, 4)`, and recovers the corresponding gap recurrences.
-/

open Finset Polynomial
open scoped Matrix

noncomputable section

namespace RealRooted.PathPowerGap

variable {R : Type*} [CommRing R]

/-- Companion matrix for `u (n + 3) = u (n + 2) + y * u n`. -/
def companionThree (y : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; 0, 0, 1; y, 0, 1]

/-- Companion matrix for `u (n + 4) = u (n + 3) + y * u n`. -/
def companionFour (y : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; y, 0, 0, 1]

/-- State vector for a third-order scalar recurrence. -/
def stateThree (u : ℕ → R) (n : ℕ) : Fin 3 → R :=
  ![u n, u (n + 1), u (n + 2)]

/-- State vector for a fourth-order scalar recurrence. -/
def stateFour (u : ℕ → R) (n : ℕ) : Fin 4 → R :=
  ![u n, u (n + 1), u (n + 2), u (n + 3)]

/-- The scalar recurrence `u (n + 3) = u (n + 2) + y * u n` is represented by
`companionThree y`. -/
theorem stateThree_succ_eq_mulVec {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 3) = u (n + 2) + y * u n) (n : ℕ) :
    stateThree u (n + 1) = companionThree y *ᵥ stateThree u n := by
  ext i
  fin_cases i
  · simp [stateThree, companionThree, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [stateThree, companionThree, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simpa [stateThree, companionThree, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, add_comm] using hu n

/-- The scalar recurrence `u (n + 4) = u (n + 3) + y * u n` is represented by
`companionFour y`. -/
theorem stateFour_succ_eq_mulVec {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 4) = u (n + 3) + y * u n) (n : ℕ) :
    stateFour u (n + 1) = companionFour y *ᵥ stateFour u n := by
  ext i
  fin_cases i
  · simp [stateFour, companionFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [stateFour, companionFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [stateFour, companionFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simpa [stateFour, companionFour, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, add_comm] using hu n

/-- Every arithmetic subsequence of a cubic path-power recurrence has the
characteristic recurrence of the corresponding companion-matrix power. -/
theorem companionThree_pow_isSolution_subsequence {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 3) = u (n + 2) + y * u n) (p c : ℕ) :
    (LinearRecurrence.ofMatrix (companionThree y ^ p)).IsSolution
      fun m ↦ u (p * m + c) := by
  simpa only [stateThree, Matrix.cons_val_zero] using
    LinearRecurrence.ofMatrix_pow_isSolution_subsequence
      (companionThree y) (stateThree u) (stateThree_succ_eq_mulVec hu) p c 0

/-- Every arithmetic subsequence of a quartic path-power recurrence has the
characteristic recurrence of the corresponding companion-matrix power. -/
theorem companionFour_pow_isSolution_subsequence {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 4) = u (n + 3) + y * u n) (p c : ℕ) :
    (LinearRecurrence.ofMatrix (companionFour y ^ p)).IsSolution
      fun m ↦ u (p * m + c) := by
  simpa only [stateFour, Matrix.cons_val_zero] using
    LinearRecurrence.ofMatrix_pow_isSolution_subsequence
      (companionFour y) (stateFour u) (stateFour_succ_eq_mulVec hu) p c 0

/-- Characteristic polynomial of the square of the cubic path-power companion. -/
theorem charpoly_companionThree_sq (y : R) :
    ((companionThree y) ^ 2).charpoly =
      X ^ 3 - X ^ 2 - C (2 * y) * X - C (y ^ 2) := by
  have hpow : companionThree y ^ 2 = !![0, 0, 1; y, 0, 1; y, y, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [companionThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hpow]
  norm_num [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three]
  simp only [map_ofNat]
  ring

/-- Characteristic polynomial of the cube of the cubic path-power companion. -/
theorem charpoly_companionThree_cube (y : R) :
    ((companionThree y) ^ 3).charpoly =
      X ^ 3 - C (1 + 3 * y) * X ^ 2 + C (3 * y ^ 2) * X - C (y ^ 3) := by
  have hpow : companionThree y ^ 3 = !![y, 0, 1; y, y, 1; y, y, y + 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [companionThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hpow]
  norm_num [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three]
  simp only [map_ofNat]
  ring

/-- Characteristic polynomial of the cube of the quartic path-power companion. -/
theorem charpoly_companionFour_cube (y : R) :
    ((companionFour y) ^ 3).charpoly =
      X ^ 4 - X ^ 3 - C (3 * y) * X ^ 2 - C (3 * y ^ 2) * X - C (y ^ 3) := by
  have hpow : companionFour y ^ 3 =
      !![0, 0, 0, 1; y, 0, 0, 1; y, y, 0, 1; y, y, y, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [companionFour, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hpow]
  norm_num [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  simp only [map_ofNat]
  ring

/-- Characteristic polynomial of the fourth power of the quartic path-power companion. -/
theorem charpoly_companionFour_pow_four (y : R) :
    ((companionFour y) ^ 4).charpoly =
      X ^ 4 - C (1 + 4 * y) * X ^ 3 + C (6 * y ^ 2) * X ^ 2 -
        C (4 * y ^ 3) * X + C (y ^ 4) := by
  have hpow : companionFour y ^ 4 =
      !![y, 0, 0, 1; y, y, 0, 1; y, y, y, 1; y, y, y, y + 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [companionFour, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hpow]
  norm_num [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  simp only [map_ofNat]
  ring

private theorem charpoly_companionFour_pow_four_eq_sum_monomial (y : R) :
    ((companionFour y) ^ 4).charpoly =
      monomial 0 (y ^ 4) + monomial 1 (-(4 * y ^ 3)) +
        monomial 2 (6 * y ^ 2) + monomial 3 (-(1 + 4 * y)) + monomial 4 1 := by
  rw [charpoly_companionFour_pow_four]
  simp only [← C_mul_X_pow_eq_monomial]
  simp only [map_ofNat, map_neg, map_add, map_mul, map_pow, map_one]
  ring

/-- Computed order-three recurrence for the even subsequence. -/
def threeGapTwo (y : R) : LinearRecurrence R :=
  ⟨3, ![y ^ 2, 2 * y, 1]⟩

/-- Computed order-three recurrence for the third-section subsequence. -/
def threeGapThree (y : R) : LinearRecurrence R :=
  ⟨3, ![y ^ 3, -(3 * y ^ 2), 1 + 3 * y]⟩

/-- Computed order-four recurrence for the third-section subsequence. -/
def fourGapThree (y : R) : LinearRecurrence R :=
  ⟨4, ![y ^ 3, 3 * y ^ 2, 3 * y, 1]⟩

/-- Computed order-four recurrence for the fourth-section subsequence. -/
def fourGapFour (y : R) : LinearRecurrence R :=
  ⟨4, ![-(y ^ 4), 4 * y ^ 3, -(6 * y ^ 2), 1 + 4 * y]⟩

private theorem ofMatrix_companionThree_sq (y : R) :
    LinearRecurrence.ofMatrix (companionThree y ^ 2) = threeGapTwo y := by
  unfold LinearRecurrence.ofMatrix threeGapTwo
  congr 1
  funext i
  rw [charpoly_companionThree_sq]
  fin_cases i <;>
    simp only [coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C] <;>
    norm_num

private theorem ofMatrix_companionThree_cube (y : R) :
    LinearRecurrence.ofMatrix (companionThree y ^ 3) = threeGapThree y := by
  unfold LinearRecurrence.ofMatrix threeGapThree
  congr 1
  funext i
  rw [charpoly_companionThree_cube]
  fin_cases i <;>
    simp only [coeff_sub, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] <;> norm_num

private theorem ofMatrix_companionFour_cube (y : R) :
    LinearRecurrence.ofMatrix (companionFour y ^ 3) = fourGapThree y := by
  unfold LinearRecurrence.ofMatrix fourGapThree
  congr 1
  funext i
  rw [charpoly_companionFour_cube]
  fin_cases i <;>
    simp only [coeff_sub, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X,
      coeff_C] <;> norm_num

private theorem ofMatrix_companionFour_pow_four (y : R) :
    LinearRecurrence.ofMatrix (companionFour y ^ 4) = fourGapFour y := by
  unfold LinearRecurrence.ofMatrix fourGapFour
  congr 1
  funext i
  rw [charpoly_companionFour_pow_four_eq_sum_monomial]
  fin_cases i <;> simp only [coeff_add, coeff_monomial] <;> norm_num

/-- The even subsequence of a cubic path-power recurrence satisfies
`s (n + 3) = s (n + 2) + 2 y s (n + 1) + y² s n`. -/
theorem threeGapTwo_isSolution {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 3) = u (n + 2) + y * u n) (c : ℕ) :
    (threeGapTwo y).IsSolution fun m ↦ u (2 * m + c) := by
  rw [← ofMatrix_companionThree_sq]
  exact companionThree_pow_isSolution_subsequence hu 2 c

/-- The third-section subsequence of a cubic path-power recurrence satisfies
the computed third-order Graeffe recurrence. -/
theorem threeGapThree_isSolution {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 3) = u (n + 2) + y * u n) (c : ℕ) :
    (threeGapThree y).IsSolution fun m ↦ u (3 * m + c) := by
  rw [← ofMatrix_companionThree_cube]
  exact companionThree_pow_isSolution_subsequence hu 3 c

/-- The third-section subsequence of a quartic path-power recurrence satisfies
the computed fourth-order Graeffe recurrence. -/
theorem fourGapThree_isSolution {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 4) = u (n + 3) + y * u n) (c : ℕ) :
    (fourGapThree y).IsSolution fun m ↦ u (3 * m + c) := by
  rw [← ofMatrix_companionFour_cube]
  exact companionFour_pow_isSolution_subsequence hu 3 c

/-- The fourth-section subsequence of a quartic path-power recurrence satisfies
the computed fourth-order Graeffe recurrence. -/
theorem fourGapFour_isSolution {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 4) = u (n + 3) + y * u n) (c : ℕ) :
    (fourGapFour y).IsSolution fun m ↦ u (4 * m + c) := by
  rw [← ofMatrix_companionFour_pow_four]
  exact companionFour_pow_isSolution_subsequence hu 4 c

/-- Companion matrix for `u (n + k) = u (n + k - 1) + y * u n`.
The definition also covers the degenerate dimensions zero and one. -/
def companion (k : ℕ) (y : R) : Matrix (Fin k) (Fin k) R := fun i j ↦
  if i.val + 1 < k then
    if j.val = i.val + 1 then 1 else 0
  else
    (if j.val = 0 then y else 0) + if j.val + 1 = k then 1 else 0

/-- Consecutive length-`k` state vector of a scalar sequence. -/
def state (k : ℕ) (u : ℕ → R) (n : ℕ) : Fin k → R := fun i ↦ u (n + i)

/-- The general path-power lag recurrence is represented by `companion k y`. -/
theorem state_succ_eq_companion_mulVec {k : ℕ} (hk : 2 ≤ k) {y : R} {u : ℕ → R}
    (hu : ∀ n, u (n + k) = u (n + k - 1) + y * u n) (n : ℕ) :
    state k u (n + 1) = companion k y *ᵥ state k u n := by
  ext i
  by_cases hi : i.val + 1 < k
  · have hsum :
        (∑ j : Fin k, (if j.val = i.val + 1 then 1 else 0) * u (n + j)) =
          u (n + 1 + i.val) := by
      rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
      · simp
        congr 1
        lia
      · intro b _ hb
        split_ifs with hbval
        · exact (hb (Fin.ext hbval)).elim
        · simp
      · simp
    simpa only [state, companion, Matrix.mulVec, dotProduct, hi, ite_true,
      one_mul, zero_mul] using hsum.symm
  · have hilast : i.val + 1 = k := by lia
    let last : Fin k := ⟨k - 1, by lia⟩
    have hfirst : (∑ j : Fin k, if j.val = 0 then y * u (n + j) else 0) =
        y * u n := by
      rw [Finset.sum_eq_single (⟨0, by lia⟩ : Fin k)]
      · simp
      · intro b _ hb
        split_ifs with hbval
        · exact (hb (Fin.ext hbval)).elim
        · simp
      · simp
    have hlast : (∑ j : Fin k, if j.val + 1 = k then u (n + j) else 0) =
        u (n + k - 1) := by
      rw [Finset.sum_eq_single last]
      · rw [ite_eq_left (by simp only [last]; lia)]
        congr 1
        simp only [last]
        lia
      · intro b _ hb
        split_ifs with hbval
        · have : b = last := by
            apply Fin.ext
            simp only [last]
            lia
          exact (hb this).elim
        · simp
      · simp
    have hindex : i.val + (n + 1) = n + k := by lia
    simpa [state, companion, Matrix.mulVec, dotProduct, hi, hilast, add_mul,
      Finset.sum_add_distrib, hfirst, hlast, last, hindex, add_comm,
      Nat.add_assoc] using hu n

/-- Every arithmetic subsequence of a general path-power lag recurrence
satisfies the characteristic recurrence of the powered companion matrix. -/
theorem companion_pow_isSolution_subsequence {k : ℕ} (hk : 2 ≤ k) {y : R}
    {u : ℕ → R} (hu : ∀ n, u (n + k) = u (n + k - 1) + y * u n)
    (p c : ℕ) :
    (LinearRecurrence.ofMatrix (companion k y ^ p)).IsSolution
      fun m ↦ u (p * m + c) := by
  simpa only [state, Nat.add_zero] using
    LinearRecurrence.ofMatrix_pow_isSolution_subsequence
    (companion k y) (state k u) (state_succ_eq_companion_mulVec hk hu) p c
      ⟨0, by lia⟩

private theorem companion_three (y : R) : companion 3 y = companionThree y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companion, companionThree]

private theorem companion_four (y : R) : companion 4 y = companionFour y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companion, companionFour]

/-- Computable coefficient list for the `p`-step path-power recurrence of
order `k`, in increasing shift order.  Integer polynomials make concrete
instances reducible by `norm_num` after expanding the characteristic polynomial. -/
def coefficientList (k p : ℕ) : List ℤ[X] :=
  (List.range k).map fun i ↦ -((companion k (X : ℤ[X]) ^ p).charpoly.coeff i)

/-- The evaluator returns the cubic even-section coefficients. -/
theorem coefficientList_three_two :
    coefficientList 3 2 = [X ^ 2, 2 * X, 1] := by
  rw [coefficientList, companion_three, charpoly_companionThree_sq]
  norm_num [-map_pow, List.range, List.range.loop, List.map, coeff_C_mul_X_pow,
    coeff_mul_X_pow']

/-- The evaluator returns the cubic third-section coefficients. -/
theorem coefficientList_three_three :
    coefficientList 3 3 = [X ^ 3, -(3 * X ^ 2), 1 + 3 * X] := by
  rw [coefficientList, companion_three, charpoly_companionThree_cube]
  norm_num [-map_pow, List.range, List.range.loop, List.map, coeff_C_mul_X_pow,
    coeff_mul_X_pow']

/-- The evaluator returns the quartic third-section coefficients. -/
theorem coefficientList_four_three :
    coefficientList 4 3 = [X ^ 3, 3 * X ^ 2, 3 * X, 1] := by
  rw [coefficientList, companion_four, charpoly_companionFour_cube]
  norm_num [-map_pow, List.range, List.range.loop, List.map, coeff_C_mul_X_pow,
    coeff_mul_X_pow']

/-- The evaluator returns the quartic fourth-section coefficients. -/
theorem coefficientList_four_four :
    coefficientList 4 4 = [-(X ^ 4), 4 * X ^ 3, -(6 * X ^ 2), 1 + 4 * X] := by
  rw [coefficientList, companion_four,
    charpoly_companionFour_pow_four_eq_sum_monomial]
  norm_num [-map_pow, List.range, List.range.loop, List.map, coeff_monomial]

private abbrev Q := RealRooted.pathPowerCliquePolynomial

private theorem Q_three_add_three (n : ℕ) :
    Q 3 (n + 3) = Q 3 (n + 2) + X * Q 3 n := by
  simpa only [show n + 3 - 1 = n + 2 by lia] using
    RealRooted.pathPowerCliquePolynomial_add_lag 3 n (by norm_num)

private theorem Q_four_add_four (n : ℕ) :
    Q 4 (n + 4) = Q 4 (n + 3) + X * Q 4 n := by
  simpa only [show n + 4 - 1 = n + 3 by lia] using
    RealRooted.pathPowerCliquePolynomial_add_lag 4 n (by norm_num)

/-- The cubic path-power even-section recurrence obtained from the general
Cayley--Hamilton subsequence theorem. -/
theorem pathPowerCliquePolynomial_three_gap_two (m : ℕ) :
    Q 3 (m + 6) = Q 3 (m + 4) + 2 * X * Q 3 (m + 2) + X ^ 2 * Q 3 m := by
  have h := threeGapTwo_isSolution Q_three_add_three m 0
  change Q 3 (2 * (0 + 3) + m) =
    ∑ i : Fin 3, ![X ^ 2, 2 * X, 1] i * Q 3 (2 * (0 + i) + m) at h
  rw [Fin.sum_univ_three] at h
  norm_num at h
  rw [Nat.add_comm m 6, Nat.add_comm m 4, Nat.add_comm m 2]
  linear_combination h

/-- The cubic path-power third-section recurrence obtained from the general
Cayley--Hamilton subsequence theorem. -/
theorem pathPowerCliquePolynomial_three_gap_three (m : ℕ) :
    Q 3 (m + 9) =
      (1 + 3 * X) * Q 3 (m + 6) - 3 * X ^ 2 * Q 3 (m + 3) + X ^ 3 * Q 3 m := by
  have h := threeGapThree_isSolution Q_three_add_three m 0
  change Q 3 (3 * (0 + 3) + m) =
    ∑ i : Fin 3, ![X ^ 3, -(3 * X ^ 2), 1 + 3 * X] i *
      Q 3 (3 * (0 + i) + m) at h
  rw [Fin.sum_univ_three] at h
  norm_num at h
  rw [Nat.add_comm m 9, Nat.add_comm m 6, Nat.add_comm m 3]
  linear_combination h

/-- The quartic path-power third-section recurrence obtained from the general
Cayley--Hamilton subsequence theorem. -/
theorem pathPowerCliquePolynomial_four_gap_three (m : ℕ) :
    Q 4 (m + 12) = Q 4 (m + 9) + 3 * X * Q 4 (m + 6) +
      3 * X ^ 2 * Q 4 (m + 3) + X ^ 3 * Q 4 m := by
  have h := fourGapThree_isSolution Q_four_add_four m 0
  change Q 4 (3 * (0 + 4) + m) =
    ∑ i : Fin 4, ![X ^ 3, 3 * X ^ 2, 3 * X, 1] i *
      Q 4 (3 * (0 + i) + m) at h
  rw [Fin.sum_univ_four] at h
  norm_num at h
  rw [Nat.add_comm m 12, Nat.add_comm m 9, Nat.add_comm m 6,
    Nat.add_comm m 3]
  linear_combination h

/-- The quartic path-power fourth-section recurrence obtained from the general
Cayley--Hamilton subsequence theorem. -/
theorem pathPowerCliquePolynomial_four_gap_four (m : ℕ) :
    Q 4 (m + 16) =
      (1 + 4 * X) * Q 4 (m + 12) - 6 * X ^ 2 * Q 4 (m + 8) +
        4 * X ^ 3 * Q 4 (m + 4) - X ^ 4 * Q 4 m := by
  have h := fourGapFour_isSolution Q_four_add_four m 0
  change Q 4 (4 * (0 + 4) + m) =
    ∑ i : Fin 4, ![-(X ^ 4), 4 * X ^ 3, -(6 * X ^ 2), 1 + 4 * X] i *
      Q 4 (4 * (0 + i) + m) at h
  rw [Fin.sum_univ_four] at h
  norm_num at h
  rw [Nat.add_comm m 16, Nat.add_comm m 12, Nat.add_comm m 8,
    Nat.add_comm m 4]
  linear_combination h

end RealRooted.PathPowerGap
