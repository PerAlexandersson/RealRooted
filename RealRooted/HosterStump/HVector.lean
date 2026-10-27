module

public import RealRooted.HosterStump.PosetBasic
public import RealRooted.Mathlib.Algebra.Polynomial.Coeff

/-!
# The `h`-vector determines the `f`-vector

For `h_k` the coefficients of `∑ i ≤ n, f_i X^i (1 - X)^(n - i)` we prove
`f_i = ∑ k ≤ n, h_k * C(n - k, n - i)` for `i ≤ n` (Hoster--Stump, (F4) of the poset proof of
identity (1.3)); `fVec_eq_sum_hVec` is the specialization to the `f`-vector of a poset.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted.HosterStump

/-- The coefficient of `X ^ k` in `X ^ j * (1 - X) ^ N`. -/
private lemma coeff_X_pow_mul_one_sub_X_pow (j N k : ℕ) :
    (X ^ j * (1 - X : ℝ[X]) ^ N).coeff k =
      if j ≤ k then (-1 : ℝ) ^ (k - j) * (N.choose (k - j) : ℝ) else 0 := by
  rw [coeff_X_pow_mul', Polynomial.coeff_one_sub_X_pow]

/-- Substituting `X ↦ X / (1 + X)` (homogenized) undoes `X ^ j * (1 - X) ^ (n - j)`. -/
private lemma sum_coeff_X_pow_mul_one_sub_X_pow (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ range (n + 1), C ((X ^ j * (1 - X : ℝ[X]) ^ (n - j)).coeff k) * X ^ k *
      (1 + X) ^ (n - k) = X ^ j := by
  rw [← sum_range_add_sum_Ico _ (by lia : j ≤ n + 1)]
  rw [sum_eq_zero (s := range j)]
  · rw [zero_add, sum_Ico_eq_sum_range]
    have hN : n + 1 - j = (n - j) + 1 := by lia
    rw [hN]
    have h1 := add_pow (-X : ℝ[X]) (1 + X) (n - j)
    rw [show (-X + (1 + X) : ℝ[X]) = 1 by ring, one_pow] at h1
    calc _ = ∑ m ∈ range (n - j + 1), X ^ j *
            ((-X : ℝ[X]) ^ m * (1 + X) ^ (n - j - m) * (((n - j).choose m : ℕ) : ℝ[X])) := by
          refine sum_congr rfl fun m _ => ?_
          rw [coeff_X_pow_mul_one_sub_X_pow]
          simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left,
            show n - (j + m) = n - j - m by lia, C_mul, C_pow, C_neg, C_1, map_natCast,
            neg_pow (X : ℝ[X]) m]
          ring
      _ = X ^ j := by rw [← mul_sum, ← h1, mul_one]
  · intro k hk
    rw [mem_range] at hk
    have hk' : ¬ j ≤ k := by lia
    rw [coeff_X_pow_mul_one_sub_X_pow]
    simp only [hk', ↓reduceIte, map_zero, zero_mul]

/-- Polynomial form of the inversion: if `h_k` are the coefficients of
`∑ j ≤ n, f_j X^j (1 - X)^(n - j)`, then `∑ k ≤ n, h_k X^k (1 + X)^(n - k) = ∑ j ≤ n, f_j X^j`. -/
private lemma sum_coeff_mul_X_pow_mul_one_add_X_pow (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ range (n + 1), C ((∑ j ∈ range (n + 1), C (f j) * X ^ j * (1 - X) ^ (n - j)).coeff k) *
      X ^ k * (1 + X) ^ (n - k) = ∑ j ∈ range (n + 1), C (f j) * X ^ j := by
  have h1 : ∀ k : ℕ, (∑ j ∈ range (n + 1), C (f j) * X ^ j * (1 - X : ℝ[X]) ^ (n - j)).coeff k =
      ∑ j ∈ range (n + 1), f j * (X ^ j * (1 - X : ℝ[X]) ^ (n - j)).coeff k := by
    intro k
    rw [finsetSum_coeff]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc, coeff_C_mul]
  simp only [h1, map_sum, map_mul, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have key := sum_coeff_X_pow_mul_one_sub_X_pow n j hjn
  calc _ = C (f j) * ∑ k ∈ range (n + 1),
        C ((X ^ j * (1 - X : ℝ[X]) ^ (n - j)).coeff k) * X ^ k * (1 + X) ^ (n - k) := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ = C (f j) * X ^ j := by rw [key]

/-- The coefficient of `X ^ i` in `X ^ k * (1 + X) ^ (n - k)`, for `k ≤ n` and `i ≤ n`. -/
private lemma coeff_X_pow_mul_one_add_X_pow (n k i : ℕ) (hk : k ≤ n) (hi : i ≤ n) :
    (X ^ k * (1 + X : ℝ[X]) ^ (n - k)).coeff i = ((n - k).choose (n - i) : ℝ) := by
  rw [coeff_X_pow_mul', coeff_one_add_X_pow]
  by_cases h : k ≤ i
  · simp only [h, ↓reduceIte]
    rw [← Nat.choose_symm (by lia : i - k ≤ n - k)]
    congr 2
    lia
  · have h' : n - k < n - i := by lia
    simp only [h, ↓reduceIte, Nat.choose_eq_zero_of_lt h', Nat.cast_zero]

/-- Inversion of the `h`-vector transform: if `h_k` are the coefficients of
`∑ j ≤ n, f_j X^j (1 - X)^(n - j)`, then `f_i = ∑ k ≤ n, h_k * C(n - k, n - i)` for `i ≤ n`. -/
theorem sum_coeff_mul_choose (n : ℕ) (f : ℕ → ℝ) (i : ℕ) (hi : i ≤ n) :
    ∑ k ∈ range (n + 1), (∑ j ∈ range (n + 1), C (f j) * X ^ j * (1 - X) ^ (n - j)).coeff k *
      (Nat.choose (n - k) (n - i) : ℝ) = f i := by
  have h := congrArg (fun p : ℝ[X] => p.coeff i)
    (sum_coeff_mul_X_pow_mul_one_add_X_pow n f)
  generalize (∑ j ∈ range (n + 1), C (f j) * X ^ j * (1 - X : ℝ[X]) ^ (n - j)) = g at h ⊢
  simp only [finsetSum_coeff, mul_assoc, coeff_C_mul] at h
  have h2 : ∀ k ∈ range (n + 1), g.coeff k * (X ^ k * (1 + X : ℝ[X]) ^ (n - k)).coeff i =
      g.coeff k * (Nat.choose (n - k) (n - i) : ℝ) := fun k hk => by
    rw [coeff_X_pow_mul_one_add_X_pow n k i (Nat.lt_succ_iff.mp (mem_range.mp hk)) hi]
  rw [sum_congr rfl h2] at h
  simp only [coeff_X_pow, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range,
    Nat.lt_succ_iff, hi, ↓reduceIte] at h
  exact h

/-- Hoster--Stump (F4): the `f`-vector of a graded poset of rank `n` in terms of its
`h`-vector, `f_i = ∑ k ≤ n, h_k * C(n - k, n - i)` for `i ≤ n`. -/
theorem fVec_eq_sum_hVec {P : Type*} [Fintype P] (n : ℕ) (rk : P → ℕ) (i : ℕ) (hi : i ≤ n) :
    (fVec rk i : ℝ) = ∑ k ∈ range (n + 1), hVec n rk k * (Nat.choose (n - k) (n - i) : ℝ) :=
  (sum_coeff_mul_choose n (fun j => (fVec rk j : ℝ)) i hi).symm

end RealRooted.HosterStump

end
