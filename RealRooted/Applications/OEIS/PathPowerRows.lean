module

public import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# OEIS rows from reflected path-power subsequences

We identify seven pure-lag OEIS row recurrences with degree-padded reciprocal
shifts of the path-power polynomials.  Four gap recurrences supply the needed
Graeffe identities.  The identifications then give real-rootedness and strict
consecutive interlacing from the path-power clique theorem.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.PathPowerRows

private abbrev Q := RealRooted.pathPowerCliquePolynomial

private theorem Q_rec (k m : ℕ) (hk : 2 ≤ k) :
    Q k (m + k) = Q k (m + k - 1) + X * Q k m := by
  exact RealRooted.pathPowerCliquePolynomial_add_lag k m hk

private theorem Q_four_rec (m : ℕ) :
    Q 4 (m + 4) = Q 4 (m + 3) + X * Q 4 m := by
  simpa only [show m + 4 - 1 = m + 3 by lia] using Q_rec 4 m (by norm_num)

private theorem Q_three_rec (m : ℕ) :
    Q 3 (m + 3) = Q 3 (m + 2) + X * Q 3 m := by
  simpa only [show m + 3 - 1 = m + 2 by lia] using Q_rec 3 m (by norm_num)

private theorem Q_three_gap_three (m : ℕ) :
    Q 3 (m + 9) =
      (1 + 3 * X) * Q 3 (m + 6) - 3 * X ^ 2 * Q 3 (m + 3) +
        X ^ 3 * Q 3 m := by
  have h0 := Q_rec 3 m (by norm_num)
  have h1 := Q_rec 3 (m + 1) (by norm_num)
  have h2 := Q_rec 3 (m + 2) (by norm_num)
  have h3 := Q_rec 3 (m + 3) (by norm_num)
  have h4 := Q_rec 3 (m + 4) (by norm_num)
  have h5 := Q_rec 3 (m + 5) (by norm_num)
  have h6 := Q_rec 3 (m + 6) (by norm_num)
  grind

private theorem Q_three_gap_two (m : ℕ) :
    Q 3 (m + 6) = Q 3 (m + 4) + 2 * X * Q 3 (m + 2) + X ^ 2 * Q 3 m := by
  have h0 := Q_rec 3 m (by norm_num)
  have h2 := Q_rec 3 (m + 2) (by norm_num)
  have h3 := Q_rec 3 (m + 3) (by norm_num)
  grind

private theorem Q_four_gap_three (m : ℕ) :
    Q 4 (m + 12) = Q 4 (m + 9) + 3 * X * Q 4 (m + 6) +
      3 * X ^ 2 * Q 4 (m + 3) + X ^ 3 * Q 4 m := by
  rw [show m + 12 = (m + 8) + 4 by lia, Q_four_rec]
  rw [show m + 11 = (m + 7) + 4 by lia, Q_four_rec]
  rw [show m + 10 = (m + 6) + 4 by lia, Q_four_rec]
  rw [show m + 9 = (m + 5) + 4 by lia, Q_four_rec]
  rw [show m + 8 = (m + 4) + 4 by lia, Q_four_rec]
  rw [show m + 7 = (m + 3) + 4 by lia, Q_four_rec]
  rw [show m + 6 = (m + 2) + 4 by lia, Q_four_rec]
  rw [show m + 5 = (m + 1) + 4 by lia, Q_four_rec]
  rw [show m + 4 = m + 4 by lia, Q_four_rec]
  ring

private theorem Q_four_gap_four (m : ℕ) :
    Q 4 (m + 16) =
      (1 + 4 * X) * Q 4 (m + 12) - 6 * X ^ 2 * Q 4 (m + 8) +
        4 * X ^ 3 * Q 4 (m + 4) - X ^ 4 * Q 4 m := by
  rw [show m + 16 = (m + 12) + 4 by lia, Q_four_rec]
  rw [show m + 15 = (m + 11) + 4 by lia, Q_four_rec]
  rw [show m + 14 = (m + 10) + 4 by lia, Q_four_rec]
  rw [show m + 13 = (m + 9) + 4 by lia, Q_four_rec]
  rw [show m + 12 = (m + 8) + 4 by lia, Q_four_rec]
  rw [show m + 11 = (m + 7) + 4 by lia, Q_four_rec]
  rw [show m + 10 = (m + 6) + 4 by lia, Q_four_rec]
  rw [show m + 9 = (m + 5) + 4 by lia, Q_four_rec]
  rw [show m + 8 = (m + 4) + 4 by lia, Q_four_rec]
  rw [show m + 7 = (m + 3) + 4 by lia, Q_four_rec]
  rw [show m + 6 = (m + 2) + 4 by lia, Q_four_rec]
  rw [show m + 5 = (m + 1) + 4 by lia, Q_four_rec]
  rw [show m + 4 = m + 4 by lia, Q_four_rec]
  ring

/-- The third-section Graeffe recurrence for the cubic path-power family. -/
theorem pathPowerCliquePolynomial_three_gap_three (m : ℕ) :
    RealRooted.pathPowerCliquePolynomial 3 (m + 9) =
      (1 + 3 * X) * RealRooted.pathPowerCliquePolynomial 3 (m + 6) -
        3 * X ^ 2 * RealRooted.pathPowerCliquePolynomial 3 (m + 3) +
          X ^ 3 * RealRooted.pathPowerCliquePolynomial 3 m :=
  Q_three_gap_three m

/-- The even-section Graeffe recurrence for the cubic path-power family. -/
theorem pathPowerCliquePolynomial_three_gap_two (m : ℕ) :
    RealRooted.pathPowerCliquePolynomial 3 (m + 6) =
      RealRooted.pathPowerCliquePolynomial 3 (m + 4) +
        2 * X * RealRooted.pathPowerCliquePolynomial 3 (m + 2) +
          X ^ 2 * RealRooted.pathPowerCliquePolynomial 3 m :=
  Q_three_gap_two m

/-- The third-section Graeffe recurrence for the quartic path-power family. -/
theorem pathPowerCliquePolynomial_four_gap_three (m : ℕ) :
    RealRooted.pathPowerCliquePolynomial 4 (m + 12) =
      RealRooted.pathPowerCliquePolynomial 4 (m + 9) +
        3 * X * RealRooted.pathPowerCliquePolynomial 4 (m + 6) +
          3 * X ^ 2 * RealRooted.pathPowerCliquePolynomial 4 (m + 3) +
            X ^ 3 * RealRooted.pathPowerCliquePolynomial 4 m :=
  Q_four_gap_three m

/-- The fourth-section Graeffe recurrence for the quartic path-power family. -/
theorem pathPowerCliquePolynomial_four_gap_four (m : ℕ) :
    RealRooted.pathPowerCliquePolynomial 4 (m + 16) =
      (1 + 4 * X) * RealRooted.pathPowerCliquePolynomial 4 (m + 12) -
        6 * X ^ 2 * RealRooted.pathPowerCliquePolynomial 4 (m + 8) +
          4 * X ^ 3 * RealRooted.pathPowerCliquePolynomial 4 (m + 4) -
            X ^ 4 * RealRooted.pathPowerCliquePolynomial 4 m :=
  Q_four_gap_four m

private theorem Q_zero : Q 3 0 = 1 := by
  ext i
  rw [RealRooted.coeff_pathPowerCliquePolynomial, coeff_one]
  rcases i with _ | i
  · simp
  · norm_cast
    simp

private theorem Q_two : Q 3 2 = 1 := by
  ext i
  rw [RealRooted.coeff_pathPowerCliquePolynomial, coeff_one]
  rcases i with _ | i
  · simp
  · simp only [Nat.succ_ne_zero, ite_false]
    norm_cast
    apply Nat.choose_eq_zero_of_lt
    lia

private theorem Q_four_zero : Q 4 0 = 1 := by
  ext i
  rw [RealRooted.coeff_pathPowerCliquePolynomial, coeff_one]
  rcases i with _ | i
  · simp
  · norm_cast
    simp

private theorem degree_Q_three_three_le (c n : ℕ) (hc : c = 0 ∨ c = 2) :
    (Q 3 (3 * n + c)).natDegree ≤ n := by
  have h := RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
    3 3 c n (by norm_num) (by norm_num) (by norm_num)
  rcases hc with rfl | rfl
  · simpa [Q_zero] using h
  · simpa [Q_two] using h

private theorem degree_Q_three_two_le (n : ℕ) :
    (Q 3 (2 * n)).natDegree ≤ n := by
  simpa [Q_zero] using
    (RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
      3 2 0 n (by norm_num) (by norm_num) (by norm_num))

private theorem degree_Q_four_three_le (n : ℕ) :
    (Q 4 (3 * n)).natDegree ≤ n := by
  simpa [Q_four_zero] using
    (RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
      4 3 0 n (by norm_num) (by norm_num) (by norm_num))

private theorem degree_Q_four_four_le (n : ℕ) :
    (Q 4 (4 * n)).natDegree ≤ n := by
  simpa [Q_four_zero] using
    (RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
      4 4 0 n (by norm_num) (by norm_num) (by norm_num))

private theorem degree_Q_three_one_le (n : ℕ) : (Q 3 n).natDegree ≤ n := by
  simpa [Q_zero] using
    (RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
      3 1 0 n (by norm_num) (by norm_num) (by norm_num))

private theorem reflect_linear_three :
    reflect 1 (1 + 3 * X : ℝ[X]) = 3 + X := by
  ext i
  rcases i with _ | _ | i <;>
    simp [Polynomial.coeff_reflect, Polynomial.revAt_le,
      Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_X]

private theorem reflect_linear_four :
    reflect 1 (1 + 4 * X : ℝ[X]) = 4 + X := by
  ext i
  rcases i with _ | _ | i <;>
    simp [Polynomial.coeff_reflect, Polynomial.revAt_le,
      Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_X]

private theorem reflect_three_X_sq : reflect 2 (3 * X ^ 2 : ℝ[X]) = 3 := by
  rw [show (3 : ℝ[X]) = C 3 from (map_ofNat C 3).symm,
    reflect_C_mul_X_pow]
  simp

private theorem reflect_six_X_sq : reflect 2 (6 * X ^ 2 : ℝ[X]) = 6 := by
  rw [show (6 : ℝ[X]) = C 6 from (map_ofNat C 6).symm,
    reflect_C_mul_X_pow]
  simp

private theorem reflect_four_X_cube : reflect 3 (4 * X ^ 3 : ℝ[X]) = 4 := by
  rw [show (4 : ℝ[X]) = C 4 from (map_ofNat C 4).symm,
    reflect_C_mul_X_pow]
  simp

private theorem reflect_X_sq : reflect 2 (X ^ 2 : ℝ[X]) = 1 := by simp

private theorem reflect_X_cube : reflect 3 (X ^ 3 : ℝ[X]) = 1 := by simp

private theorem reflect_X_four : reflect 4 (X ^ 4 : ℝ[X]) = 1 := by simp

private theorem reflect_two_X : reflect 2 (2 * X : ℝ[X]) = 2 * X := by
  ext i
  rcases i with _ | _ | _ | i <;>
    simp [Polynomial.coeff_reflect, Polynomial.revAt_le,
      Polynomial.revAt_eq_self_of_lt, coeff_X]

private theorem reflect_three_X : reflect 2 (3 * X : ℝ[X]) = 3 * X := by
  ext i
  rcases i with _ | _ | _ | i <;>
    simp [Polynomial.coeff_reflect, Polynomial.revAt_le,
      Polynomial.revAt_eq_self_of_lt, coeff_X]

private theorem reflect_three_X_sq_padded :
    reflect 3 (3 * X ^ 2 : ℝ[X]) = 3 * X := by
  ext i
  rcases i with _ | _ | _ | _ | i <;>
    simp [Polynomial.coeff_reflect, Polynomial.revAt_le,
      Polynomial.revAt_eq_self_of_lt, coeff_X, coeff_X_pow]

private theorem reflect_X_sq_padded : reflect 3 (X ^ 2 : ℝ[X]) = X := by
  ext i
  rcases i with _ | _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, coeff_X]

private theorem reflect_X_cube_padded : reflect 4 (X ^ 3 : ℝ[X]) = X := by
  ext i
  rcases i with _ | _ | _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, coeff_X]

private theorem reflect_X_padded : reflect 3 (X : ℝ[X]) = X ^ 2 := by
  ext i
  rcases i with _ | _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, Polynomial.revAt_eq_self_of_lt, coeff_X]

private theorem reflect_four_X_middle : reflect 2 (4 * X : ℝ[X]) = 4 * X := by
  ext i
  rcases i with _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, Polynomial.revAt_eq_self_of_lt, coeff_X]

private theorem reflect_two_X_six : reflect 2 (6 * X : ℝ[X]) = 6 * X := by
  ext i
  rcases i with _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, Polynomial.revAt_eq_self_of_lt, coeff_X]

private theorem reflect_two_X_sq_six : reflect 2 (6 * X ^ 2 : ℝ[X]) = 6 := by
  rw [show (6 : ℝ[X]) = C 6 from (map_ofNat C 6).symm,
    reflect_C_mul_X_pow]
  simp

private theorem reflect_two_X_five : reflect 2 (5 * X : ℝ[X]) = 5 * X := by
  ext i
  rcases i with _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, Polynomial.revAt_eq_self_of_lt, coeff_X]

private theorem reflect_three_X_nine : reflect 3 (9 * X : ℝ[X]) = 9 * X ^ 2 := by
  ext i
  rcases i with _ | _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, Polynomial.revAt_eq_self_of_lt, coeff_X, coeff_X_pow]

private theorem reflect_three_X_sq_fifteen :
    reflect 3 (15 * X ^ 2 : ℝ[X]) = 15 * X := by
  ext i
  rcases i with _ | _ | _ | _ | i <;>
    simp [Polynomial.revAt_le, Polynomial.revAt_eq_self_of_lt, coeff_X, coeff_X_pow]

private theorem reflected_three_gap_three (c n : ℕ) (hc : c = 0 ∨ c = 2) :
    RealRooted.reciprocalShift (n + 3) (Q 3 (3 * (n + 3) + c)) =
      (3 + X) * RealRooted.reciprocalShift (n + 2) (Q 3 (3 * (n + 2) + c)) -
        3 * RealRooted.reciprocalShift (n + 1) (Q 3 (3 * (n + 1) + c)) +
          RealRooted.reciprocalShift n (Q 3 (3 * n + c)) := by
  rw [show 3 * (n + 3) + c = (3 * n + c) + 9 by lia,
    show 3 * (n + 2) + c = (3 * n + c) + 6 by lia,
    show 3 * (n + 1) + c = (3 * n + c) + 3 by lia]
  rw [RealRooted.reciprocalShift, Q_three_gap_three, reflect_add, reflect_sub]
  rw [show 3 * n + c + 6 = 3 * (n + 2) + c by lia,
    show 3 * n + c + 3 = 3 * (n + 1) + c by lia]
  rw [show n + 3 = 1 + (n + 2) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_three_three_le c (n + 2) hc)]
  rw [show 1 + (n + 2) = 2 + (n + 1) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_three_three_le c (n + 1) hc)]
  rw [show 2 + (n + 1) = 3 + n by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_three_three_le c n hc)]
  rw [reflect_linear_three, reflect_three_X_sq, reflect_X_cube]
  simp only [RealRooted.reciprocalShift]
  ring

private theorem reflected_three_gap_two (n : ℕ) :
    RealRooted.reciprocalShift (n + 3) (Q 3 (2 * (n + 3))) =
      X * RealRooted.reciprocalShift (n + 2) (Q 3 (2 * (n + 2))) +
        2 * X * RealRooted.reciprocalShift (n + 1) (Q 3 (2 * (n + 1))) +
          X * RealRooted.reciprocalShift n (Q 3 (2 * n)) := by
  rw [show 2 * (n + 3) = 2 * n + 6 by lia,
    show 2 * (n + 2) = 2 * n + 4 by lia,
    show 2 * (n + 1) = 2 * n + 2 by lia]
  rw [RealRooted.reciprocalShift, Q_three_gap_two, reflect_add, reflect_add]
  rw [show 2 * n + 4 = 2 * (n + 2) by lia,
    show 2 * n + 2 = 2 * (n + 1) by lia]
  rw [show n + 3 = (n + 2) + 1 by lia,
    Polynomial.reflect_succ _ (degree_Q_three_two_le (n + 2))]
  rw [show (n + 2) + 1 = 2 + (n + 1) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_three_two_le (n + 1))]
  rw [show 2 + (n + 1) = 3 + n by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_three_two_le n)]
  rw [reflect_two_X, reflect_X_sq_padded]
  simp only [RealRooted.reciprocalShift]
  ring

private theorem reflected_four_gap_three (n : ℕ) :
    RealRooted.reciprocalShift (n + 4) (Q 4 (3 * (n + 4))) =
      X * RealRooted.reciprocalShift (n + 3) (Q 4 (3 * (n + 3))) +
        3 * X * RealRooted.reciprocalShift (n + 2) (Q 4 (3 * (n + 2))) +
          3 * X * RealRooted.reciprocalShift (n + 1) (Q 4 (3 * (n + 1))) +
            X * RealRooted.reciprocalShift n (Q 4 (3 * n)) := by
  rw [show 3 * (n + 4) = 3 * n + 12 by lia,
    show 3 * (n + 3) = 3 * n + 9 by lia,
    show 3 * (n + 2) = 3 * n + 6 by lia,
    show 3 * (n + 1) = 3 * n + 3 by lia]
  rw [RealRooted.reciprocalShift, Q_four_gap_three, reflect_add, reflect_add,
    reflect_add]
  rw [show 3 * n + 9 = 3 * (n + 3) by lia,
    show 3 * n + 6 = 3 * (n + 2) by lia,
    show 3 * n + 3 = 3 * (n + 1) by lia]
  rw [show n + 4 = (n + 3) + 1 by lia,
    Polynomial.reflect_succ _ (degree_Q_four_three_le (n + 3))]
  rw [show (n + 3) + 1 = 2 + (n + 2) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_three_le (n + 2))]
  rw [show 2 + (n + 2) = 3 + (n + 1) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_three_le (n + 1))]
  rw [show 3 + (n + 1) = 4 + n by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_three_le n)]
  rw [reflect_three_X, reflect_three_X_sq_padded, reflect_X_cube_padded]
  simp only [RealRooted.reciprocalShift]
  ring

private theorem reflected_four_gap_four (n : ℕ) :
    RealRooted.reciprocalShift (n + 4) (Q 4 (4 * (n + 4))) =
      (4 + X) * RealRooted.reciprocalShift (n + 3) (Q 4 (4 * (n + 3))) -
        6 * RealRooted.reciprocalShift (n + 2) (Q 4 (4 * (n + 2))) +
          4 * RealRooted.reciprocalShift (n + 1) (Q 4 (4 * (n + 1))) -
            RealRooted.reciprocalShift n (Q 4 (4 * n)) := by
  rw [show 4 * (n + 4) = 4 * n + 16 by lia,
    show 4 * (n + 3) = 4 * n + 12 by lia,
    show 4 * (n + 2) = 4 * n + 8 by lia,
    show 4 * (n + 1) = 4 * n + 4 by lia]
  rw [RealRooted.reciprocalShift, Q_four_gap_four, reflect_sub, reflect_add,
    reflect_sub]
  rw [show 4 * n + 12 = 4 * (n + 3) by lia,
    show 4 * n + 8 = 4 * (n + 2) by lia,
    show 4 * n + 4 = 4 * (n + 1) by lia]
  rw [show n + 4 = 1 + (n + 3) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_four_le (n + 3))]
  rw [show 1 + (n + 3) = 2 + (n + 2) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_four_le (n + 2))]
  rw [show 2 + (n + 2) = 3 + (n + 1) by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_four_le (n + 1))]
  rw [show 3 + (n + 1) = 4 + n by lia,
    reflect_mul _ _ (by compute_degree!) (degree_Q_four_four_le n)]
  rw [reflect_linear_four, reflect_six_X_sq, reflect_four_X_cube, reflect_X_four]
  simp only [RealRooted.reciprocalShift]
  ring

private theorem reflected_three_gap_one_padded (n : ℕ) :
    RealRooted.reciprocalShift (n + 4) (Q 3 (n + 3)) =
      X * RealRooted.reciprocalShift (n + 3) (Q 3 (n + 2)) +
        X ^ 2 * RealRooted.reciprocalShift (n + 1) (Q 3 n) := by
  rw [Q_three_rec]
  rw [RealRooted.reciprocalShift, reflect_add]
  rw [show n + 4 = (n + 3) + 1 by lia,
    Polynomial.reflect_succ _ ((degree_Q_three_one_le (n + 2)).trans (by lia))]
  rw [show (n + 3) + 1 = 3 + (n + 1) by lia,
    reflect_mul _ _ (by compute_degree!) ((degree_Q_three_one_le n).trans (by lia))]
  simp only [RealRooted.reciprocalShift]
  rw [reflect_X_padded]
  ring

/-- OEIS A109955, copied from its pure-lag row recurrence. -/
def a109955 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => (3 + X) * a109955 (n + 2) - 3 * a109955 (n + 1) + a109955 n

/-- OEIS A127893, copied from its pure-lag row recurrence. -/
def a127893 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 + X
  | 2 => 6 + 6 * X + X ^ 2
  | n + 3 => (3 + X) * a127893 (n + 2) - 3 * a127893 (n + 1) + a127893 n

/-- OEIS A206294, copied from its pure-lag row recurrence. -/
def a206294 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 3 * X + X ^ 2
  | 3 => 6 * X + 6 * X ^ 2 + X ^ 3
  | n + 4 => (3 + X) * a206294 (n + 3) - 3 * a206294 (n + 2) + a206294 (n + 1)

/-- OEIS A109960, copied from its pure-lag row recurrence. -/
def a109960 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | 3 => 1 + 15 * X + 9 * X ^ 2 + X ^ 3
  | n + 4 => (4 + X) * a109960 (n + 3) - 6 * a109960 (n + 2) +
      4 * a109960 (n + 1) - a109960 n

/-- OEIS A116088, copied from its pure-lag row recurrence. -/
def a116088 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 2 * X + X ^ 2
  | n + 3 => X * a116088 (n + 2) + 2 * X * a116088 (n + 1) + X * a116088 n

/-- OEIS A116089, copied from its pure-lag row recurrence. -/
def a116089 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 3 * X + X ^ 2
  | 3 => 3 * X + 6 * X ^ 2 + X ^ 3
  | n + 4 => X * a116089 (n + 3) + 3 * X * a116089 (n + 2) +
      3 * X * a116089 (n + 1) + X * a116089 n

/-- OEIS A277627, copied from its pure-lag row recurrence. -/
def a277627 : ℕ → ℝ[X]
  | 0 => X
  | 1 => X ^ 2
  | 2 => X ^ 3
  | n + 3 => X * a277627 (n + 2) + X ^ 2 * a277627 n

/-- A109955 is the reflected third section of the cubic path-power family. -/
theorem a109955_eq_reciprocalShift (n : ℕ) :
    a109955 n = RealRooted.reciprocalShift n
      (RealRooted.pathPowerCliquePolynomial 3 (3 * n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · norm_num [a109955, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift]
      · norm_num [a109955, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        ring
      · norm_num [a109955, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        rw [reflect_four_X_middle]
        ring
      · rw [a109955, ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
        exact (reflected_three_gap_three 0 n (Or.inl rfl)).symm

/-- A127893 is the offset-two reflected third section of the cubic family. -/
theorem a127893_eq_reciprocalShift (n : ℕ) :
    a127893 n = RealRooted.reciprocalShift n
      (RealRooted.pathPowerCliquePolynomial 3 (3 * n + 2)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · norm_num [a127893, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
      · norm_num [a127893, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        ext i
        rcases i with _ | _ | i <;>
          norm_num [Polynomial.coeff_reflect, Polynomial.revAt_le,
            Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_mul, coeff_X]
      · norm_num [a127893, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        rw [reflect_two_X_six,
          show ((Nat.choose 4 2 : ℕ) : ℝ[X]) = 6 by norm_num [Nat.choose],
          reflect_two_X_sq_six]
        ring
      · rw [a127893, ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
        exact (reflected_three_gap_three 2 n (Or.inr rfl)).symm

/-- Positive-index A206294 rows are `X` times the preceding A127893 row. -/
theorem a206294_succ_eq_X_mul_a127893 (n : ℕ) :
    a206294 (n + 1) = X * a127893 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · simp only [a206294, a127893, mul_one]
      · rw [a206294, a127893]
        ring
      · rw [a206294, a127893]
        ring
      · rw [show a206294 (n + 3 + 1) = a206294 (n + 4) by rfl, a206294,
          ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia), a127893]
        ring

/-- A206294 is the padded reflected subsequence at indices `3n - 1`. -/
theorem a206294_eq_reciprocalShift (n : ℕ) :
    a206294 n = RealRooted.reciprocalShift n
      (RealRooted.pathPowerCliquePolynomial 3 (3 * n - 1)) := by
  rcases n with _ | n
  · norm_num [a206294, Q, RealRooted.pathPowerCliquePolynomial,
      RealRooted.reciprocalShift]
  · rw [a206294_succ_eq_X_mul_a127893, a127893_eq_reciprocalShift]
    rw [show 3 * (n + 1) - 1 = 3 * n + 2 by lia]
    change X * reflect n (Q 3 (3 * n + 2)) = reflect (n + 1) (Q 3 (3 * n + 2))
    rw [Polynomial.reflect_succ _ (degree_Q_three_three_le 2 n (Or.inr rfl))]
    ring

/-- A109960 is the reflected fourth section of the quartic path-power family. -/
theorem a109960_eq_reciprocalShift (n : ℕ) :
    a109960 n = RealRooted.reciprocalShift n
      (RealRooted.pathPowerCliquePolynomial 4 (4 * n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · norm_num [a109960, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift]
      · norm_num [a109960, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        ext i
        rcases i with _ | _ | _ | i <;>
          norm_num [Polynomial.coeff_reflect, Polynomial.revAt_le,
            Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_mul, coeff_one,
            coeff_X, coeff_X_pow]
      · norm_num [a109960, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        rw [reflect_two_X_five]
        ring
      · norm_num [a109960, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        rw [reflect_three_X_nine,
          show ((Nat.choose 6 2 : ℕ) : ℝ[X]) = 15 by norm_num [Nat.choose],
          reflect_three_X_sq_fifteen]
        ring
      · rw [a109960, ih (n + 3) (by lia), ih (n + 2) (by lia),
          ih (n + 1) (by lia), ih n (by lia)]
        exact (reflected_four_gap_four n).symm

/-- A116088 is the reflected even subsequence of the cubic path-power family. -/
theorem a116088_eq_reciprocalShift (n : ℕ) :
    a116088 n = RealRooted.reciprocalShift n
      (RealRooted.pathPowerCliquePolynomial 3 (2 * n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · norm_num [a116088, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift]
      · norm_num [a116088, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
      · norm_num [a116088, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        ext i
        rcases i with _ | _ | _ | i <;>
          norm_num [Polynomial.coeff_reflect, Polynomial.revAt_le,
            Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_mul, coeff_X, coeff_X_pow]
      · rw [a116088, ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]
        exact (reflected_three_gap_two n).symm

/-- A116089 is the reflected third section of the quartic path-power family. -/
theorem a116089_eq_reciprocalShift (n : ℕ) :
    a116089 n = RealRooted.reciprocalShift n
      (RealRooted.pathPowerCliquePolynomial 4 (3 * n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · norm_num [a116089, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift]
      · norm_num [a116089, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
      · norm_num [a116089, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        ext i
        rcases i with _ | _ | _ | i <;>
          norm_num [Polynomial.coeff_reflect, Polynomial.revAt_le,
            Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_mul, coeff_X, coeff_X_pow]
      · norm_num [a116089, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
        ext i
        rcases i with _ | _ | _ | _ | i <;>
          norm_num [Polynomial.coeff_reflect, Polynomial.revAt_le,
            Polynomial.revAt_eq_self_of_lt, coeff_add, coeff_mul, coeff_X, coeff_X_pow]
      · rw [a116089, ih (n + 3) (by lia), ih (n + 2) (by lia),
          ih (n + 1) (by lia), ih n (by lia)]
        exact (reflected_four_gap_three n).symm

/-- A277627 is the path-power family reflected with one extra zero of padding. -/
theorem a277627_eq_reciprocalShift (n : ℕ) :
    a277627 n = RealRooted.reciprocalShift (n + 1)
      (RealRooted.pathPowerCliquePolynomial 3 n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · norm_num [a277627, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift]
      · norm_num [a277627, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
      · norm_num [a277627, Q, RealRooted.pathPowerCliquePolynomial,
          RealRooted.reciprocalShift, Finset.sum_range_succ]
      · rw [a277627, ih (n + 2) (by lia), ih n (by lia)]
        exact (reflected_three_gap_one_padded n).symm

/-- Every A109955 row is real-rooted. -/
theorem splits_a109955 (n : ℕ) : (a109955 n).Splits := by
  rw [a109955_eq_reciprocalShift]
  have h := RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
    3 3 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_zero] using h

/-- Consecutive A109955 rows are in strict interlacing position. -/
theorem strictInterl_a109955 (n : ℕ) :
    RealRooted.StrictInterl (a109955 n) (a109955 (n + 1)) := by
  rw [a109955_eq_reciprocalShift, a109955_eq_reciprocalShift]
  have h := RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
    3 3 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_zero] using h

/-- Every A127893 row is real-rooted. -/
theorem splits_a127893 (n : ℕ) : (a127893 n).Splits := by
  rw [a127893_eq_reciprocalShift]
  have h := RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
    3 3 2 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_two] using h

/-- Consecutive A127893 rows are in strict interlacing position. -/
theorem strictInterl_a127893 (n : ℕ) :
    RealRooted.StrictInterl (a127893 n) (a127893 (n + 1)) := by
  rw [a127893_eq_reciprocalShift, a127893_eq_reciprocalShift]
  have h := RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
    3 3 2 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_two] using h

/-- Every A206294 row is real-rooted. -/
theorem splits_a206294 (n : ℕ) : (a206294 n).Splits := by
  rcases n with _ | n
  · simp [a206294]
  · rw [a206294_succ_eq_X_mul_a127893]
    exact Polynomial.Splits.X.mul (splits_a127893 n)

/-- Consecutive A206294 rows are in strict interlacing position. -/
theorem strictInterl_a206294 (n : ℕ) :
    RealRooted.StrictInterl (a206294 n) (a206294 (n + 1)) := by
  rcases n with _ | n
  · rw [show a206294 0 = 1 from rfl, show a206294 1 = X from rfl]
    exact (RealRooted.interlaces_one_linear (p := (X : ℝ[X])) (by simp)).toStrictInterl
  · rw [a206294_succ_eq_X_mul_a127893, a206294_succ_eq_X_mul_a127893]
    exact RealRooted.StrictInterl.mul_common_factor
      (strictInterl_a127893 n) X_ne_zero Polynomial.Splits.X

/-- Every A109960 row is real-rooted. -/
theorem splits_a109960 (n : ℕ) : (a109960 n).Splits := by
  rw [a109960_eq_reciprocalShift]
  have h := RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
    4 4 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_four_zero] using h

/-- Consecutive A109960 rows are in strict interlacing position. -/
theorem strictInterl_a109960 (n : ℕ) :
    RealRooted.StrictInterl (a109960 n) (a109960 (n + 1)) := by
  rw [a109960_eq_reciprocalShift, a109960_eq_reciprocalShift]
  have h := RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
    4 4 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_four_zero] using h

/-- Every A116088 row is real-rooted. -/
theorem splits_a116088 (n : ℕ) : (a116088 n).Splits := by
  rw [a116088_eq_reciprocalShift]
  have h := RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
    3 2 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_zero] using h

/-- Consecutive A116088 rows are in strict interlacing position. -/
theorem strictInterl_a116088 (n : ℕ) :
    RealRooted.StrictInterl (a116088 n) (a116088 (n + 1)) := by
  rw [a116088_eq_reciprocalShift, a116088_eq_reciprocalShift]
  have h := RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
    3 2 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_zero] using h

/-- Every A116089 row is real-rooted. -/
theorem splits_a116089 (n : ℕ) : (a116089 n).Splits := by
  rw [a116089_eq_reciprocalShift]
  have h := RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
    4 3 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_four_zero] using h

/-- Consecutive A116089 rows are in strict interlacing position. -/
theorem strictInterl_a116089 (n : ℕ) :
    RealRooted.StrictInterl (a116089 n) (a116089 (n + 1)) := by
  rw [a116089_eq_reciprocalShift, a116089_eq_reciprocalShift]
  have h := RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
    4 3 0 n (by norm_num) (by norm_num) (by norm_num)
  simpa [Q_four_zero] using h

private theorem a277627_eq_X_mul_reciprocalShift (n : ℕ) :
    a277627 n = X * RealRooted.reciprocalShift n (Q 3 n) := by
  rw [a277627_eq_reciprocalShift]
  change reflect (n + 1) (Q 3 n) = X * reflect n (Q 3 n)
  rw [Polynomial.reflect_succ _ (degree_Q_three_one_le n)]
  ring

/-- Every A277627 row is real-rooted. -/
theorem splits_a277627 (n : ℕ) : (a277627 n).Splits := by
  rw [a277627_eq_X_mul_reciprocalShift]
  have h := RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
    3 1 0 n (by norm_num) (by norm_num) (by norm_num)
  exact Polynomial.Splits.X.mul (by simpa [Q_zero] using h)

/-- Consecutive A277627 rows are in strict interlacing position. -/
theorem strictInterl_a277627 (n : ℕ) :
    RealRooted.StrictInterl (a277627 n) (a277627 (n + 1)) := by
  rw [a277627_eq_X_mul_reciprocalShift, a277627_eq_X_mul_reciprocalShift]
  have h := RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
    3 1 0 n (by norm_num) (by norm_num) (by norm_num)
  exact RealRooted.StrictInterl.mul_common_factor
    (by simpa [Q_zero] using h)
    X_ne_zero Polynomial.Splits.X

end RealRooted.PathPowerRows
