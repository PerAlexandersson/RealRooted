module

public import RealRooted.Graph.IndependencePolynomial.CubicParent

/-!
# Three rows from the cubic parent

The downstream definitions of A184883, A114123, and A216182 are the three
normalizations below of the coefficients of

`1 / (1 + t - X t² + X t³)`.

A184883 is the even subsequence.  A114123 reverses each even coefficient
polynomial.  A216182 reverses the sign-corrected odd coefficient polynomial.
The real-rootedness statements follow from `CubicParent.polynomial_splits`
and preservation of splitting under coefficient reversal.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.CubicParentRows

/-- The A184883 row polynomial, realized as the even cubic-parent coefficient. -/
def a184883 (n : ℕ) : ℝ[X] :=
  CubicParent.polynomial (2 * n)

/-- The A114123 row polynomial, with the recurrence used by the downstream row file. -/
def a114123 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | n + 3 =>
      (2 + X) * a114123 (n + 2) +
        (-1 + 2 * X) * a114123 (n + 1) + X * a114123 n

/-- The A216182 row polynomial, with the recurrence used by the downstream row file. -/
def a216182 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 + X
  | 2 => 5 + 7 * X + X ^ 2
  | n + 3 =>
      (2 + X) * a216182 (n + 2) +
        (-1 + 2 * X) * a216182 (n + 1) + X * a216182 n

/-- The A184883 model satisfies its downstream order-three recurrence. -/
theorem a184883_add_three (n : ℕ) :
    a184883 (n + 3) =
      (1 + 2 * X) * a184883 (n + 2) +
        (2 * X - X ^ 2) * a184883 (n + 1) + X ^ 2 * a184883 n := by
  unfold a184883
  simpa only [show 2 * (n + 3) = 2 * n + 6 by lia,
    show 2 * (n + 2) = 2 * n + 4 by lia,
    show 2 * (n + 1) = 2 * n + 2 by lia] using
      CubicParent.polynomial_add_six (2 * n)

private lemma a114123_natDegree_le : ∀ n : ℕ, (a114123 n).natDegree ≤ n
  | 0 => by simp [a114123]
  | 1 => by rw [a114123]; compute_degree!
  | 2 => by rw [a114123]; compute_degree!
  | n + 3 => by
      rw [a114123]
      refine (natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
      · exact natDegree_mul_le.trans (by
          have hfactor : (2 + X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
          exact (Nat.add_le_add hfactor (a114123_natDegree_le (n + 2))).trans (by lia))
      · exact natDegree_mul_le.trans (by
          have hfactor : (-1 + 2 * X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
          exact (Nat.add_le_add hfactor (a114123_natDegree_le (n + 1))).trans (by lia))
      · exact natDegree_mul_le.trans (by
          exact (Nat.add_le_add natDegree_X_le (a114123_natDegree_le n)).trans (by lia))

private lemma a216182_natDegree_le : ∀ n : ℕ, (a216182 n).natDegree ≤ n
  | 0 => by simp [a216182]
  | 1 => by rw [a216182]; compute_degree!
  | 2 => by rw [a216182]; compute_degree!
  | n + 3 => by
      rw [a216182]
      refine (natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
      · exact natDegree_mul_le.trans (by
          have hfactor : (2 + X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
          exact (Nat.add_le_add hfactor (a216182_natDegree_le (n + 2))).trans (by lia))
      · exact natDegree_mul_le.trans (by
          have hfactor : (-1 + 2 * X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
          exact (Nat.add_le_add hfactor (a216182_natDegree_le (n + 1))).trans (by lia))
      · exact natDegree_mul_le.trans (by
          exact (Nat.add_le_add natDegree_X_le (a216182_natDegree_le n)).trans (by lia))

private lemma reflect_one_two_add_X :
    reflect 1 (2 + X : ℝ[X]) = 1 + 2 * X := by
  rw [show (2 + X : ℝ[X]) = C 2 * X ^ 0 + C 1 * X ^ 1 by
      norm_num [map_ofNat],
    reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  simp only [revAt_le (by lia : 0 ≤ 1), revAt_le (by lia : 1 ≤ 1)]
  norm_num [map_ofNat]
  ring

private lemma reflect_two_neg_one_add_two_X :
    reflect 2 (-1 + 2 * X : ℝ[X]) = -1 * X ^ 2 + 2 * X := by
  rw [show (-1 + 2 * X : ℝ[X]) = C (-1) * X ^ 0 + C 2 * X ^ 1 by
      norm_num [map_ofNat],
    reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  simp only [revAt_le (by lia : 0 ≤ 2), revAt_le (by lia : 1 ≤ 2)]
  norm_num [map_ofNat]

private lemma reflect_three_X : reflect 3 (X : ℝ[X]) = X ^ 2 := by
  rw [show (X : ℝ[X]) = C 1 * X ^ 1 by simp, reflect_C_mul_X_pow]
  simp

private lemma reflect_recurrence
    (r : ℕ → ℝ[X])
    (hdeg : ∀ n, (r n).natDegree ≤ n)
    (hrec : ∀ n, r (n + 3) =
      (2 + X) * r (n + 2) + (-1 + 2 * X) * r (n + 1) + X * r n)
    (n : ℕ) :
    reflect (n + 3) (r (n + 3)) =
      (1 + 2 * X) * reflect (n + 2) (r (n + 2)) +
        (2 * X - X ^ 2) * reflect (n + 1) (r (n + 1)) +
          X ^ 2 * reflect n (r n) := by
  have h1 := reflect_mul (2 + X : ℝ[X]) (r (n + 2))
    (F := 1) (G := n + 2) (by compute_degree!) (hdeg (n + 2))
  have h2 := reflect_mul (-1 + 2 * X : ℝ[X]) (r (n + 1))
    (F := 2) (G := n + 1) (by compute_degree!) (hdeg (n + 1))
  have h3 := reflect_mul (X : ℝ[X]) (r n)
    (F := 3) (G := n) (by simp) (hdeg n)
  have h1' : reflect (n + 3) ((2 + X) * r (n + 2)) =
      reflect 1 (2 + X) * reflect (n + 2) (r (n + 2)) := by
    simpa only [show n + 3 = 1 + (n + 2) by lia] using h1
  have h2' : reflect (n + 3) ((-1 + 2 * X) * r (n + 1)) =
      reflect 2 (-1 + 2 * X) * reflect (n + 1) (r (n + 1)) := by
    simpa only [show n + 3 = 2 + (n + 1) by lia] using h2
  have h3' : reflect (n + 3) (X * r n) =
      reflect 3 X * reflect n (r n) := by
    simpa only [show n + 3 = 3 + n by lia] using h3
  rw [hrec, reflect_add, reflect_add, h1', h2', h3',
    reflect_one_two_add_X, reflect_two_neg_one_add_two_X, reflect_three_X]
  ring

private lemma cubicParent_three : CubicParent.polynomial 3 = -1 - 3 * X := by
  have h := CubicParent.polynomial_add_three 0
  norm_num at h
  rw [h]
  ring

private lemma cubicParent_four :
    CubicParent.polynomial 4 = 1 + 5 * X + X ^ 2 := by
  have h := CubicParent.polynomial_add_three 1
  norm_num at h
  rw [h, cubicParent_three]
  ring

private lemma cubicParent_five :
    CubicParent.polynomial 5 = -1 - 7 * X - 5 * X ^ 2 := by
  have h := CubicParent.polynomial_add_three 2
  norm_num at h
  rw [h, cubicParent_three, cubicParent_four]
  ring

private lemma reflect_one_one_add_X :
    reflect 1 (1 + X : ℝ[X]) = 1 + X := by
  rw [show (1 + X : ℝ[X]) = C 1 * X ^ 0 + C 1 * X ^ 1 by simp,
    reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  simp only [revAt_le (by lia : 0 ≤ 1), revAt_le (by lia : 1 ≤ 1)]
  simp
  ring

private lemma reflect_two_one_add_five_X_add_X_sq :
    reflect 2 (1 + 5 * X + X ^ 2 : ℝ[X]) = 1 + 5 * X + X ^ 2 := by
  rw [show (1 + 5 * X + X ^ 2 : ℝ[X]) =
      (C 1 * X ^ 0 + C 5 * X ^ 1) + C 1 * X ^ 2 by norm_num [map_ofNat],
    reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow]
  simp only [revAt_le (by lia : 0 ≤ 2), revAt_le (by lia : 1 ≤ 2),
    revAt_le (by lia : 2 ≤ 2)]
  norm_num [map_ofNat]
  ring

private lemma reflect_one_three_add_X :
    reflect 1 (3 + X : ℝ[X]) = 1 + 3 * X := by
  rw [show (3 + X : ℝ[X]) = C 3 * X ^ 0 + C 1 * X ^ 1 by
      norm_num [map_ofNat],
    reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  simp only [revAt_le (by lia : 0 ≤ 1), revAt_le (by lia : 1 ≤ 1)]
  norm_num [map_ofNat]
  ring

private lemma reflect_two_five_add_seven_X_add_X_sq :
    reflect 2 (5 + 7 * X + X ^ 2 : ℝ[X]) = 1 + 7 * X + 5 * X ^ 2 := by
  rw [show (5 + 7 * X + X ^ 2 : ℝ[X]) =
      (C 5 * X ^ 0 + C 7 * X ^ 1) + C 1 * X ^ 2 by norm_num [map_ofNat],
    reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow]
  simp only [revAt_le (by lia : 0 ≤ 2), revAt_le (by lia : 1 ≤ 2),
    revAt_le (by lia : 2 ≤ 2)]
  norm_num [map_ofNat]
  ring

/-- Reflecting A114123 at its row index gives A184883. -/
theorem reflect_a114123_eq_a184883 :
    ∀ n : ℕ, reflect n (a114123 n) = a184883 n
  | 0 => by simp [a114123, a184883]
  | 1 => by simp only [a114123, a184883, Nat.reduceMul, CubicParent.polynomial_two,
      reflect_one_one_add_X]
  | 2 => by simp only [a114123, a184883, Nat.reduceMul, cubicParent_four,
      reflect_two_one_add_five_X_add_X_sq]
  | n + 3 => by
      rw [reflect_recurrence a114123 a114123_natDegree_le (fun k => by rw [a114123])]
      rw [reflect_a114123_eq_a184883 (n + 2),
        reflect_a114123_eq_a184883 (n + 1), reflect_a114123_eq_a184883 n,
        a184883_add_three]

private def oddModel (n : ℕ) : ℝ[X] :=
  C (-1) * CubicParent.polynomial (2 * n + 1)

private lemma oddModel_add_three (n : ℕ) :
    oddModel (n + 3) =
      (1 + 2 * X) * oddModel (n + 2) +
        (2 * X - X ^ 2) * oddModel (n + 1) + X ^ 2 * oddModel n := by
  unfold oddModel
  have h := CubicParent.polynomial_add_six (2 * n + 1)
  simp only [show 2 * (n + 3) + 1 = (2 * n + 1) + 6 by lia,
    show 2 * (n + 2) + 1 = (2 * n + 1) + 4 by lia,
    show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by lia] at *
  rw [h]
  ring

/-- Reflecting A216182 at its row index gives the sign-corrected odd parent coefficient. -/
theorem reflect_a216182_eq_odd_parent :
    ∀ n : ℕ, reflect n (a216182 n) =
      C (-1) * CubicParent.polynomial (2 * n + 1)
  | 0 => by simp [a216182]
  | 1 => by
      simp only [a216182, Nat.reduceMul, Nat.reduceAdd, cubicParent_three,
        reflect_one_three_add_X]
      norm_num [map_neg, map_one]
      ring
  | 2 => by
      simp only [a216182, Nat.reduceMul, Nat.reduceAdd, cubicParent_five,
        reflect_two_five_add_seven_X_add_X_sq]
      norm_num [map_neg, map_one]
      ring
  | n + 3 => by
      rw [reflect_recurrence a216182 a216182_natDegree_le (fun k => by rw [a216182])]
      rw [reflect_a216182_eq_odd_parent (n + 2),
        reflect_a216182_eq_odd_parent (n + 1), reflect_a216182_eq_odd_parent n]
      simpa only [oddModel] using (oddModel_add_three n).symm

/-- Every A184883 row polynomial splits over `ℝ`. -/
theorem a184883_splits (n : ℕ) : (a184883 n).Splits := by
  exact CubicParent.polynomial_splits (2 * n)

/-- Every A114123 row polynomial splits over `ℝ`. -/
theorem a114123_splits (n : ℕ) : (a114123 n).Splits := by
  apply (Polynomial.splits_reflect_iff (a114123_natDegree_le n)).1
  rw [reflect_a114123_eq_a184883]
  exact a184883_splits n

/-- Every A216182 row polynomial splits over `ℝ`. -/
theorem a216182_splits (n : ℕ) : (a216182 n).Splits := by
  apply (Polynomial.splits_reflect_iff (a216182_natDegree_le n)).1
  rw [reflect_a216182_eq_odd_parent]
  exact (CubicParent.polynomial_splits (2 * n + 1)).C_mul (-1)

end RealRooted.CubicParentRows
