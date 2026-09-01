import RealRooted.NarayanaTransformation.Rectangular

/-!
# Generalized Narayana recurrence identities
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

theorem narayanaPolynomial_one (m : ℕ) :
    narayanaPolynomial m 1 = X + C 1 := by
  ext k
  simp only [coeff_add, coeff_X, coeff_C]
  rcases k with _ | _ | _ <;> simp

theorem narayanaPolynomial_two (m : ℕ) :
    narayanaPolynomial m 2 = X ^ 2 + C (2 * ((m : ℝ) + 2) / ((m : ℝ) + 1)) * X + C 1 := by
  ext k
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  rcases k with _ | _ | _ | _
  · simp
  · simp [narayanaTransformCoeff]
    ring
  · simp
  · simp

theorem natDegree_narayanaPolynomial (m n : ℕ) :
    (narayanaPolynomial m n).natDegree = n := by
  have : (narayanaPolynomial m n).coeff n ≠ 0 := by simp
  exact le_antisymm (natDegree_narayanaPolynomial_le m n) (le_natDegree_of_ne_zero this)

theorem leadingCoeff_narayanaPolynomial (m n : ℕ) :
    (narayanaPolynomial m n).leadingCoeff = 1 := by
  simp [leadingCoeff, natDegree_narayanaPolynomial]

theorem narayanaPolynomial_ne_zero (m n : ℕ) :
    narayanaPolynomial m n ≠ 0 := by
  simp [← leadingCoeff_ne_zero, leadingCoeff_narayanaPolynomial]

theorem hasPosLeadingCoeff_narayanaPolynomial (m n : ℕ) :
    HasPosLeadingCoeff (narayanaPolynomial m n) := by
  simp [HasPosLeadingCoeff, leadingCoeff_narayanaPolynomial]

theorem narayanaPolynomial_eval_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) (m n : ℕ) :
    0 < (narayanaPolynomial m n).eval x := by
  dsimp [narayanaPolynomial]
  rw [eval_finsetSum, ← sum_erase_add _ _ (mem_range.mpr (Nat.succ_pos n))]
  refine add_pos_of_nonneg_of_pos (sum_nonneg fun k _ => ?_) ?_
  · simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact mul_nonneg (narayanaTransformCoeff_nonneg m n k) (pow_nonneg hx k)
  · simp

theorem narayanaPolynomial_eval_one_pos (m n : ℕ) :
    0 < (narayanaPolynomial m n).eval 1 :=
  narayanaPolynomial_eval_pos_of_nonneg zero_le_one m n

theorem narayanaPolynomial_root_nonpos {m n : ℕ} {r : ℝ}
    (hr : (narayanaPolynomial m n).IsRoot r) : r ≤ 0 := by
  by_contra h
  exact (narayanaPolynomial_eval_pos_of_nonneg (not_le.mp h).le m n).ne' hr

theorem factorial_cast_ne_zero (n : ℕ) :
    (n.factorial : ℝ) ≠ 0 := by
  positivity

lemma factorial_succ_cast (n : ℕ) :
    ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
  rw [Nat.factorial_succ n]
  push_cast
  rfl

lemma factorial_succ_succ_cast (n : ℕ) :
    ((n + 2).factorial : ℝ) = (n + 2) * (n + 1) * n.factorial := by
  rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  ring

lemma factorial_cast_pred {n : ℕ} (hn : n ≠ 0) :
    (n.factorial : ℝ) = n * (n - 1).factorial := by
  have h : n = n - 1 + 1 := by lia
  nth_rw 1 [h]
  rw [Nat.factorial_succ]
  push_cast
  rw [h]
  push_cast
  rfl

private lemma deriv_lag_poly_identity (n m k : ℝ) :
    (n + 2 * m + 2) * (n + 2) * (n + 2 + m) =
      (n + 2 * m + 2 + 2 * k) * (n + 2 - k) * (n + 2 + m - k) +
        (3 * n + 2 * m + 6 - 2 * k) * k * (m + k) := by
  ring

private lemma pure_poly_identity (n m k : ℝ) :
    (n + 2 * m + 2) * (n + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) =
      (2 * n + 2 * m + 3) * ((n + 1) * (n + 1 + m) * (n + 2 - k) * (n + 2 + m - k) +
        (n + 1) * (n + 1 + m) * k * (m + k)) -
        (n + 1) * ((n + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) -
          2 * (n + 2 - k) * (n + 2 + m - k) * k * (m + k) +
          k * (k - 1) * (m + k) * (m + k - 1)) := by
  ring

lemma narayanaTransformCoeff_deriv_lag_rec (m n k : ℕ) (hkpos : k ≠ 0) (hk : k ≤ n + 1) :
    ((n : ℝ) + 2 * m + 2) * narayanaTransformCoeff m (n + 2) k =
      ((n : ℝ) + 2 * m + 2 + 2 * k) * narayanaTransformCoeff m (n + 1) k +
        ((3 * n : ℝ) + 2 * m + 6 - 2 * k) *
          narayanaTransformCoeff m (n + 1) (k - 1) := by
  let F : ℝ := (Nat.factorial (n + 1) : ℝ) * Nat.factorial (n + 1 + m) * Nat.factorial m /
    ((Nat.factorial (n + 2 - k) : ℝ) * Nat.factorial (n + 2 + m - k) * Nat.factorial k *
      Nat.factorial (m + k))
  have hF_eq₁ :
      (narayanaTransformCoeff m (n + 2) k : ℝ) =
        ((n : ℝ) + 2) * (n + 2 + m) * F := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 2) k (by lia)]
    dsimp only [F]
    rw [show n + 1 + m = n + m + 1 by ring]
    field_simp [factorial_cast_ne_zero]
    rw [factorial_succ_cast (n + 1), show n + 2 + m = n + m + 1 + 1 by ring,
      factorial_succ_cast (n + m + 1)]
    push_cast
    ring
  have hF_eq₂ : (narayanaTransformCoeff m (n + 1) k : ℝ) =
    ((n : ℝ) + 2 - k) * (n + 2 + m - k) * F := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) k hk]
    dsimp only [F]
    field_simp [factorial_cast_ne_zero]
    rw [show n + 2 - k = (n + 1 - k) + 1 by lia, factorial_succ_cast (n + 1 - k)]
    rw [show n + 2 + m - k = (n + 1 + m - k) + 1 by lia, factorial_succ_cast (n + 1 + m - k)]
    rw [Nat.cast_sub hk, Nat.cast_sub (by lia : k ≤ n + 1 + m)]
    push_cast
    ring
  have hF_eq₃ : (narayanaTransformCoeff m (n + 1) (k - 1) : ℝ) = (k : ℝ) * (m + k) * F := by
    have h₆ : m + (k - 1) = m + k - 1 := by lia
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) (k - 1) (by lia)]
    dsimp only [F]
    have h₄ : n + 1 - (k - 1) = n + 2 - k := by lia
    have h₅ : n + 1 + m - (k - 1) = n + 2 + m - k := by lia
    rw [h₄, h₅, h₆]
    field_simp [factorial_cast_ne_zero]
    rw [factorial_cast_pred hkpos, factorial_cast_pred (by lia : m + k ≠ 0)]
    push_cast
    ring
  rw [hF_eq₁, hF_eq₂, hF_eq₃]
  have h_poly := deriv_lag_poly_identity (n : ℝ) (m : ℝ) (k : ℝ)
  rw [show ((n : ℝ) + 2 * m + 2) * (((n : ℝ) + 2) * (n + 2 + m) * F) =
    ((n : ℝ) + 2 * m + 2) * (n + 2) * (n + 2 + m) * F by ring]
  rw [show ((n : ℝ) + 2 * m + 2 + 2 * k) * (((n : ℝ) + 2 - k) * (n + 2 + m - k) * F) +
    ((3 * n : ℝ) + 2 * m + 6 - 2 * k) * ((k : ℝ) * (m + k) * F) =
    (((n : ℝ) + 2 * m + 2 + 2 * k) * (n + 2 - k) * (n + 2 + m - k) +
      ((3 * n : ℝ) + 2 * m + 6 - 2 * k) * k * (m + k)) * F by ring]
  rw [h_poly]

theorem coeff_narayanaPolynomial_deriv_lag_rec (m n k : ℕ) (hkpos : k ≠ 0) :
    ((n : ℝ) + 2 * m + 2) * (narayanaPolynomial m (n + 2)).coeff k =
      ((n : ℝ) + 2 * m + 2 + 2 * k) * (narayanaPolynomial m (n + 1)).coeff k +
        ((3 * n : ℝ) + 2 * m + 6 - 2 * k) *
          (narayanaPolynomial m (n + 1)).coeff (k - 1) := by
  rcases le_or_gt k (n + 2) with hk | hk
  · rw [coeff_narayanaPolynomial_of_le hk]
    have : k - 1 ≤ n + 1 := by lia
    rcases le_or_gt k (n + 1) with hk | hk
    · rw [coeff_narayanaPolynomial_of_le hk, coeff_narayanaPolynomial_of_le this]
      exact narayanaTransformCoeff_deriv_lag_rec m n k hkpos hk
    · obtain rfl : k = n + 2 := by lia
      change _ = _ + _ * (narayanaPolynomial m (n + 1)).coeff (n + 1)
      rw [narayanaTransformCoeff_self,
        coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self (n + 1)),
        coeff_narayanaPolynomial_of_le le_rfl, narayanaTransformCoeff_self]
      push_cast
      ring
  · rw [coeff_narayanaPolynomial_of_lt hk,
      coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k),
      coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k - 1)]
    ring

theorem narayanaPolynomial_deriv_lag_rec (m n : ℕ) :
    C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2) =
      (C ((n : ℝ) + 2 * m + 2) + C ((3 * n : ℝ) + 2 * m + 4) * X) *
          narayanaPolynomial m (n + 1) +
        (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2) *
          (narayanaPolynomial m (n + 1)).derivative := by
  ext k
  rw [add_mul, sub_mul, mul_assoc, mul_assoc]
  rcases k with _ | _ | k
  · simp
  · rw [coeff_C_mul, coeff_narayanaPolynomial_deriv_lag_rec m n 1 one_ne_zero]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative, sq,
      mul_assoc, coeff_X_mul_zero]
    ring
  · rw [coeff_C_mul, coeff_narayanaPolynomial_deriv_lag_rec m n (k + 2) (by lia)]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative, sq,
      mul_assoc]
    push_cast
    ring

lemma narayanaTransformCoeff_pure_rec (m n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) + 2 * m + 2) * narayanaTransformCoeff m (n + 2) k =
      ((2 * n : ℝ) + 2 * m + 3) *
          (narayanaTransformCoeff m (n + 1) k +
            narayanaTransformCoeff m (n + 1) (k - 1)) -
        ((n : ℝ) + 1) *
          (narayanaTransformCoeff m n k -
            2 * narayanaTransformCoeff m n (k - 1) +
            narayanaTransformCoeff m n (k - 2)) := by
  let G : ℝ := (Nat.factorial n : ℝ) * Nat.factorial (n + m) * Nat.factorial m /
    ((Nat.factorial (n + 2 - k) : ℝ) * Nat.factorial (n + 2 + m - k) * Nat.factorial k *
      Nat.factorial (m + k))
  have hG₁ : (narayanaTransformCoeff m (n + 2) k : ℝ) =
      ((n : ℝ) + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) * G := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 2) k (by lia)]
    have h₁ := factorial_succ_succ_cast n
    have h₂ : ((n + 2 + m).factorial : ℝ) = (n + 2 + m) * (n + 1 + m) * (n + m).factorial := by
      rw [show n + 2 + m = n + m + 2 by ring, factorial_succ_succ_cast]
      push_cast
      ring
    dsimp only [G]
    field_simp [factorial_cast_ne_zero]
    rw [h₁, h₂]
    ring
  have hG₂ : (narayanaTransformCoeff m (n + 1) k : ℝ) =
      ((n : ℝ) + 1) * (n + 1 + m) * (n + 2 - k) * (n + 2 + m - k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) k (by lia)]
    have h₁ := factorial_succ_cast n
    have h₂ : ((n + 1 + m).factorial : ℝ) = (n + 1 + m) * (n + m).factorial := by
      rw [show n + 1 + m = n + m + 1 by ring, factorial_succ_cast (n + m)]
      push_cast
      ring
    have h₃ : ((n + 2 - k).factorial : ℝ) = ((n : ℝ) + 2 - k) * (n + 1 - k).factorial := by
      rw [show n + 2 - k = (n + 1 - k) + 1 by lia, factorial_succ_cast (n + 1 - k),
        Nat.cast_sub (by lia : k ≤ n + 1)]
      push_cast
      ring
    have h₄ : ((n + 2 + m - k).factorial : ℝ) =
      ((n : ℝ) + 2 + m - k) * (n + 1 + m - k).factorial := by
      rw [show n + 2 + m - k = (n + 1 + m - k) + 1 by lia, factorial_succ_cast (n + 1 + m - k),
        Nat.cast_sub (by lia : k ≤ n + 1 + m)]
      push_cast
      ring
    dsimp only [G]
    field_simp [factorial_cast_ne_zero]
    rw [h₁, h₂, h₃, h₄]
    ring
  have hG₃ : (narayanaTransformCoeff m (n + 1) (k - 1) : ℝ) =
      ((n : ℝ) + 1) * (n + 1 + m) * (k : ℝ) * (m + k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) (k - 1) (by lia)]
    have h₁ := factorial_succ_cast n
    have h₂ : ((n + 1 + m).factorial : ℝ) = (n + 1 + m) * (n + m).factorial := by
      rw [show n + 1 + m = n + m + 1 by ring, factorial_succ_cast (n + m)]
      push_cast
      ring
    have h₃ := factorial_cast_pred (by lia : k ≠ 0)
    have h₄ := factorial_cast_pred (by lia : m + k ≠ 0)
    dsimp only [G]
    have h₅ : n + 1 - (k - 1) = n + 2 - k := by lia
    have h₆ : n + 1 + m - (k - 1) = n + 2 + m - k := by lia
    have h₇ : m + k - 1 = m + (k - 1) := by lia
    field_simp [factorial_cast_ne_zero]
    rw [h₅, h₆, h₁, h₂, h₃, h₄, h₇]
    push_cast
    ring
  have hG₄ : (narayanaTransformCoeff m n k : ℝ) =
      ((n : ℝ) + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m n k hkn]
    have h₁ : ((n + 2 - k).factorial : ℝ) =
      ((n : ℝ) + 2 - k) * ((n : ℝ) + 1 - k) * (n - k).factorial := by
      rw [show n + 2 - k = (n - k) + 2 by lia, factorial_succ_succ_cast (n - k), Nat.cast_sub hkn]
      ring
    have h₂ : ((n + 2 + m - k).factorial : ℝ) =
      ((n : ℝ) + 2 + m - k) * ((n : ℝ) + 1 + m - k) * (n + m - k).factorial := by
      rw [show n + 2 + m - k = (n + m - k) + 2 by lia, factorial_succ_succ_cast (n + m - k),
        Nat.cast_sub (by lia : k ≤ n + m), Nat.cast_add]
      ring
    dsimp only [G]
    field_simp [factorial_cast_ne_zero]
    rw [h₁, h₂]
    ring
  have hG₅ : (narayanaTransformCoeff m n (k - 1) : ℝ) =
      ((n : ℝ) + 2 - k) * (n + 2 + m - k) * (k : ℝ) * (m + k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m n (k - 1) (by lia)]
    have h₁ : ((n + 2 - k).factorial : ℝ) =
      ((n : ℝ) + 2 - k) * (n + 1 - k).factorial := by
      rw [show n + 2 - k = (n + 1 - k) + 1 by lia, factorial_succ_cast (n + 1 - k),
        Nat.cast_sub (by lia : k ≤ n + 1)]
      push_cast
      ring
    have h₂ : ((n + 2 + m - k).factorial : ℝ) =
      ((n : ℝ) + 2 + m - k) * (n + 1 + m - k).factorial := by
      rw [show n + 2 + m - k = (n + 1 + m - k) + 1 by lia, factorial_succ_cast (n + 1 + m - k),
        Nat.cast_sub (by lia : k ≤ n + 1 + m)]
      push_cast
      ring
    have h₃ := factorial_cast_pred (by lia : k ≠ 0)
    have h₄ := factorial_cast_pred (by lia : m + k ≠ 0)
    dsimp only [G]
    have h₅ : n - (k - 1) = n + 1 - k := by lia
    have h₆ : n + m - (k - 1) = n + 1 + m - k := by lia
    have h₇ : m + k - 1 = m + (k - 1) := by lia
    field_simp [factorial_cast_ne_zero]
    rw [h₅, h₆, h₁, h₂, h₃, h₄, h₇]
    push_cast
    ring
  have hG₆ : (narayanaTransformCoeff m n (k - 2) : ℝ) =
      (k : ℝ) * (k - 1) * (m + k) * (m + k - 1) * G := by
    rw [narayanaTransformCoeff_eq_factorial m n (k - 2) (by lia)]
    have h₁ : (k.factorial : ℝ) = k * (k - 1) * (k - 2).factorial := by
      conv_lhs => rw [show k = (k - 2) + 2 by lia]
      rw [factorial_succ_succ_cast]
      rw [Nat.cast_sub hk]
      ring
    have h₂ : ((m + k).factorial : ℝ) =
      (m + k) * (m + k - 1) * (m + (k - 2)).factorial := by
      conv_lhs => rw [show m + k = m + (k - 2) + 2 by lia]
      rw [factorial_succ_succ_cast]
      push_cast
      rw [Nat.cast_sub hk]
      ring
    dsimp only [G]
    have h₃ : n - (k - 2) = n + 2 - k := by lia
    have h₄ : n + m - (k - 2) = n + 2 + m - k := by lia
    field_simp [factorial_cast_ne_zero]
    rw [h₃, h₄, h₁, h₂]
    ring
  rw [hG₁, hG₂, hG₃, hG₄, hG₅, hG₆]
  have h_poly := pure_poly_identity (n : ℝ) (m : ℝ) (k : ℝ)
  rw [show ((n : ℝ) + 2 * m + 2) * (((n : ℝ) + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) * G) =
    ((n : ℝ) + 2 * m + 2) * (n + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) * G by ring]
  rw [show ((2 * n : ℝ) + 2 * m + 3) * (((n : ℝ) + 1) * (n + 1 + m) * (n + 2 - k) *
    (n + 2 + m - k) * G + ((n : ℝ) + 1) * (n + 1 + m) * (k : ℝ) * (m + k) * G) -
    ((n : ℝ) + 1) * (((n : ℝ) + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) * G -
      2 * (((n : ℝ) + 2 - k) * (n + 2 + m - k) * (k : ℝ) * (m + k) * G) +
      (k : ℝ) * (k - 1) * (m + k) * (m + k - 1) * G) =
    (((2 * n : ℝ) + 2 * m + 3) * ((n + 1) * (n + 1 + m) * (n + 2 - k) * (n + 2 + m - k) +
      (n + 1) * (n + 1 + m) * k * (m + k)) -
      ((n : ℝ) + 1) * ((n + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) -
        2 * (n + 2 - k) * (n + 2 + m - k) * k * (m + k) +
        k * (k - 1) * (m + k) * (m + k - 1))) * G by ring]
  rw [h_poly]

lemma coeff_narayanaPolynomial_pure_rec_boundary (m n : ℕ) (hn : n ≠ 0) :
    ((n : ℝ) + 2 * m + 2) * (narayanaPolynomial m (n + 2)).coeff (n + 1) =
    ((2 * n : ℝ) + 2 * m + 3) *
      ((narayanaPolynomial m (n + 1)).coeff (n + 1) +
        (narayanaPolynomial m (n + 1)).coeff n) -
    ((n : ℝ) + 1) *
      ((narayanaPolynomial m n).coeff (n + 1) -
        2 * (narayanaPolynomial m n).coeff n +
        (narayanaPolynomial m n).coeff (n - 1)) := by
  rw [coeff_narayanaPolynomial_of_le (Nat.le_succ (n + 1)),
    coeff_narayanaPolynomial_of_le le_rfl,
    coeff_narayanaPolynomial_of_le (Nat.le_succ n),
    coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self n),
    coeff_narayanaPolynomial_of_le le_rfl,
    coeff_narayanaPolynomial_of_le (Nat.sub_le n 1)]
  rw [narayanaTransformCoeff_self (m := m) (n := n + 1),
        narayanaTransformCoeff_self (m := m) (n := n),
    narayanaTransformCoeff_eq_factorial m (n + 2) (n + 1) (Nat.le_succ (n + 1)),
    narayanaTransformCoeff_eq_factorial m (n + 1) n (Nat.le_succ n),
    narayanaTransformCoeff_eq_factorial m n (n - 1) (Nat.sub_le n 1)]
  have heq₃ : n + 2 - (n + 1) = 1 := by lia
  have heq₄ : n + 2 + m - (n + 1) = m + 1 := by lia
  have heq₅ : n + 1 - n = 1 := by lia
  have heq₆ : n + 1 + m - n = m + 1 := by lia
  have heq₇ : n - (n - 1) = 1 := by lia
  have heq₈ : n + m - (n - 1) = m + 1 := by lia
  rw [heq₃, heq₄, heq₅, heq₆, heq₇, heq₈, Nat.factorial_one]
  have hn₂_fac := factorial_succ_succ_cast n
  have hn₁_fac := factorial_succ_cast n
  have hn₂m_fac : ((n + 2 + m).factorial : ℝ) =
      (n + 2 + m) * (n + 1 + m) * (n + m).factorial := by
    rw [show n + 2 + m = n + m + 2 by ring, factorial_succ_succ_cast]
    push_cast
    ring
  have hn₁m_fac : ((n + 1 + m).factorial : ℝ) =
      (n + 1 + m) * (n + m).factorial := by
    rw [show n + 1 + m = n + m + 1 by ring, factorial_succ_cast (n + m)]
    push_cast
    ring
  have hn_fac := factorial_cast_pred hn
  have hnm_fac : ((n + m).factorial : ℝ) =
      (n + m) * (m + (n - 1)).factorial := by
    rw [show n + m = m + (n - 1) + 1 by lia, factorial_succ_cast (m + (n - 1))]
    push_cast
    rw [Nat.cast_sub (by lia : 1 ≤ n)]
    ring
  have hmn_fac : ((m + n).factorial : ℝ) =
      (m + n) * (m + (n - 1)).factorial := by
    rw [show m + n = m + (n - 1) + 1 by lia, factorial_succ_cast (m + (n - 1))]
    push_cast
    rw [Nat.cast_sub (by lia : 1 ≤ n)]
    ring
  have hm_fac := factorial_succ_cast m
  have hmn₁_fac : ((m + (n + 1)).factorial : ℝ) =
      (m + n + 1) * (n + m).factorial := by
    rw [show m + (n + 1) = m + n + 1 by ring, show n + m = m + n by ring,
      factorial_succ_cast (m + n)]
    push_cast
    ring
  simp only [hn₂_fac, hn₁_fac, hn₂m_fac, hn₁m_fac, hmn₁_fac, hn_fac,
    hnm_fac, hmn_fac, hm_fac]
  have : (Nat.factorial m : ℝ) ≠ 0 := factorial_cast_ne_zero m
  have : (Nat.factorial (n - 1) : ℝ) ≠ 0 := factorial_cast_ne_zero (n - 1)
  have : (Nat.factorial (m + (n - 1)) : ℝ) ≠ 0 :=
    factorial_cast_ne_zero (m + (n - 1))
  have : (n : ℝ) ≠ 0 := by positivity
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  have : (m : ℝ) + n ≠ 0 := by positivity
  have : (n : ℝ) + m ≠ 0 := by positivity
  generalize (Nat.factorial m : ℝ) = Fm at *
  generalize (Nat.factorial (n - 1) : ℝ) = Fn₁ at *
  generalize (Nat.factorial (m + (n - 1)) : ℝ) = Fmn₁ at *
  field_simp
  push_cast
  ring

theorem coeff_narayanaPolynomial_pure_rec (m n k : ℕ) (hk : 2 ≤ k) :
    ((n : ℝ) + 2 * m + 2) * (narayanaPolynomial m (n + 2)).coeff k =
      ((2 * n : ℝ) + 2 * m + 3) *
          ((narayanaPolynomial m (n + 1)).coeff k +
            (narayanaPolynomial m (n + 1)).coeff (k - 1)) -
        ((n : ℝ) + 1) *
          ((narayanaPolynomial m n).coeff k -
            2 * (narayanaPolynomial m n).coeff (k - 1) +
            (narayanaPolynomial m n).coeff (k - 2)) := by
  rcases le_or_gt k n with hkn | hnk
  · have hkn₁ : k ≤ n + 1 := by lia
    have hkn₂ : k ≤ n + 2 := by lia
    have hk₁n : k - 1 ≤ n := by lia
    have hk₂n : k - 2 ≤ n := by lia
    have hk₁n₁ : k - 1 ≤ n + 1 := by lia
    rw [coeff_narayanaPolynomial_of_le hkn₂, coeff_narayanaPolynomial_of_le hkn₁,
      coeff_narayanaPolynomial_of_le hk₁n₁, coeff_narayanaPolynomial_of_le hkn,
      coeff_narayanaPolynomial_of_le hk₁n, coeff_narayanaPolynomial_of_le hk₂n]
    exact narayanaTransformCoeff_pure_rec m n k hk hkn
  · rcases eq_or_lt_of_le (by lia : n + 1 ≤ k) with rfl | hk
    · exact coeff_narayanaPolynomial_pure_rec_boundary m n (by lia)
    · rcases eq_or_lt_of_le (by lia : n + 2 ≤ k) with rfl | hk
      · change _ = _ * (_ + (narayanaPolynomial m (n + 1)).coeff (n + 1)) -
          _ * (_ - 2 * (narayanaPolynomial m n).coeff (n + 1) + (narayanaPolynomial m n).coeff n)
        rw [coeff_narayanaPolynomial_of_le le_rfl,
          narayanaTransformCoeff_self,
          coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self (n + 1)),
          coeff_narayanaPolynomial_of_le le_rfl,
          coeff_narayanaPolynomial_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self n)),
          coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self n),
          coeff_narayanaPolynomial_of_le le_rfl]
        rw [narayanaTransformCoeff_self, narayanaTransformCoeff_self]
        ring
      · rw [coeff_narayanaPolynomial_of_lt hk,
          coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k),
          coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k - 1),
          coeff_narayanaPolynomial_of_lt (by lia : n < k),
          coeff_narayanaPolynomial_of_lt (by lia : n < k - 1),
          coeff_narayanaPolynomial_of_lt (by lia : n < k - 2)]
        simp

theorem narayanaPolynomial_pure_rec (m n : ℕ) :
    C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2) =
      C ((2 * n : ℝ) + 2 * m + 3) * ((1 + X) * narayanaPolynomial m (n + 1)) -
        C ((n : ℝ) + 1) * ((1 - X) ^ 2 * narayanaPolynomial m n) := by
  ext k
  have h₁ : (1 + X : ℝ[X]) * narayanaPolynomial m (n + 1) =
      narayanaPolynomial m (n + 1) + X * narayanaPolynomial m (n + 1) := by ring
  have h₂ : (1 - X : ℝ[X]) ^ 2 * narayanaPolynomial m n =
      narayanaPolynomial m n - C 2 * (X * narayanaPolynomial m n) +
        X ^ 2 * narayanaPolynomial m n := by
    rw [C_ofNat 2]
    ring
  rw [h₁, h₂, mul_add, mul_add, mul_sub]
  rcases k with _ | _ | k
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero, sq, mul_assoc,
      coeff_narayanaPolynomial_of_le, narayanaTransformCoeff_zero_right, Nat.zero_le]
    ring
  · rcases n with rfl | n
    · simp only [CharP.cast_eq_zero, zero_add, mul_zero, map_one,
        narayanaPolynomial_zero_right, mul_one, one_mul, coeff_sub, coeff_add, coeff_mul_X,
        coeff_C_zero, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, add_zero,
        coeff_C_mul, coeff_X_mul, coeff_one]
      rw [coeff_narayanaPolynomial_of_le (Nat.le_succ 1), coeff_narayanaPolynomial_of_le le_rfl]
      rw [narayanaTransformCoeff_self]
      dsimp [narayanaTransformCoeff]
      simp
      field_simp
      ring
    · have hcoeff₁ (N : ℕ) (hN : N ≠ 0) :
            narayanaTransformCoeff m N 1 = (N : ℝ) * (N + m) / (m + 1) := by
        dsimp [narayanaTransformCoeff]
        simp
      simp [hcoeff₁, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, sq, mul_assoc,
        coeff_narayanaPolynomial_of_le, narayanaTransformCoeff_zero_right, add_mul, mul_add]
      field_simp
      ring
  · have hk_ge : 2 ≤ k + 2 := by lia
    rw [coeff_C_mul, coeff_narayanaPolynomial_pure_rec m n (k + 2) hk_ge]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, sq, mul_assoc]
    push_cast
    ring

end RealRooted
