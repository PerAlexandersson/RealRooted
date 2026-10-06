module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic bounds for Chebyshev polynomials on `[-1, 1]`

We prove the Pell identity `T_(n+1)² + (1 - X²) U_n² = 1`, the sum identities
`U_(j+1) - U_j = 1 - 2(1 - X) ∑_(i ≤ j) U_i` and
`U_(2m) = 2m + 1 - 4(1 - X²) ∑_(i < m) U_i²`, the composition identity
`U_(2m+1) = 2X · U_m(T_2)`, and the following bounds for `|x| ≤ 1` over a linearly
ordered field:

* `abs_eval_T_le_one`: `|T_n(x)| ≤ 1`;
* `abs_eval_U_le`: `|U_n(x)| ≤ n + 1`;
* `abs_eval_U_two_mul_add_one_le`: `|U_(2m+1)(x)| ≤ (2m + 2) |x|`;
* `abs_eval_U_two_mul_le`: `|U_(2m)(x)| ≤ 1 + 2m x²`.

The proofs are algebraic: no trigonometric parametrization is used.
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Finset

section CommRing

variable (R : Type*) [CommRing R]

/-- The Cassini-type identity `U_n² + U_(n+1)² - 2X U_n U_(n+1) = 1`. -/
theorem U_sq_add_U_sq (n : ℤ) :
    U R n ^ 2 + U R (n + 1) ^ 2 - 2 * X * U R n * U R (n + 1) = 1 := by
  have h := congrArg (fun p : R[X] ↦ p.comp (2 * X)) (S_sq_add_S_sq R n)
  simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp, one_comp,
    S_comp_two_mul_X] at h
  linear_combination h

/-- The Pell identity `T_(n+1)² + (1 - X²) U_n² = 1`. -/
theorem T_sq_add_one_sub_X_sq_mul_U_sq (n : ℤ) :
    T R (n + 1) ^ 2 + (1 - X ^ 2) * U R n ^ 2 = 1 := by
  have hT : T R (n + 1) = U R (n + 1) - X * U R n := by
    simpa using T_eq_U_sub_X_mul_U R (n + 1)
  rw [hT]
  linear_combination U_sq_add_U_sq R n

/-- `U_(n+2) + U_(n-2) = 2 T_2 U_n`. -/
theorem U_add_two_add_U_sub_two (n : ℤ) :
    U R (n + 2) + U R (n - 2) = 2 * T R 2 * U R n := by
  have h1 := U_add_two R n
  have h2 := U_add_one R n
  have h3 := U_sub_two R n
  rw [T_two]
  linear_combination h1 + h3 + 2 * X * h2

/-- `U_(2m+1) = 2X · U_m(T_2)`. -/
theorem U_two_mul_add_one (m : ℕ) :
    U R (2 * m + 1) = 2 * X * (U R m).comp (T R 2) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [U_one]
  | one =>
    have h3 : U R 3 = 2 * X * U R 2 - U R 1 := by
      rw [show (3 : ℤ) = 1 + 2 by norm_num, U_add_two]
      norm_num
    norm_num [h3, U_two, U_one, T_two]
    ring
  | more m ih ih1 =>
    have h := U_add_two_add_U_sub_two R (2 * (m + 1 : ℕ) + 1)
    have hU : (U R ((m + 2 : ℕ) : ℤ)) = 2 * X * U R ((m + 1 : ℕ) : ℤ) - U R (m : ℕ) := by
      simp
    rw [hU, sub_comp, mul_comp, mul_comp, X_comp, ofNat_comp]
    have e1 : ((2 * (m + 1 : ℕ) + 1 : ℤ) + 2) = (2 * ((m + 2 : ℕ) : ℤ) + 1) := by push_cast; ring
    have e2 : ((2 * (m + 1 : ℕ) + 1 : ℤ) - 2) = (2 * (m : ℤ) + 1) := by push_cast; ring
    rw [e1, e2, ih, ih1] at h
    linear_combination h

/-- `U_(j+1) - U_j = 1 - 2(1 - X) ∑_(i ≤ j) U_i`. -/
theorem U_succ_sub_U (j : ℕ) :
    U R (j + 1) - U R j = 1 - 2 * (1 - X) * ∑ i ∈ range (j + 1), U R i := by
  induction j with
  | zero => simp [U_one]; ring
  | succ j ih =>
    have h : U R ((j + 1 : ℕ) + 1) = 2 * X * U R (j + 1 : ℕ) - U R j := by
      simp [add_assoc]
    rw [sum_range_succ, h]
    push_cast at ih ⊢
    linear_combination ih

/-- `U_(2m) = 2m + 1 - 4(1 - X²) ∑_(i < m) U_i²`. -/
theorem U_two_mul_eq_sub_sum_sq (m : ℕ) :
    U R (2 * m) = 2 * (m : R[X]) + 1 - 4 * (1 - X ^ 2) * ∑ i ∈ range m, U R i ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hU : U R (2 * (m + 1 : ℕ)) = 2 * T R (2 * (m + 1 : ℕ)) + U R (2 * m) := by
      have := U_eq_two_mul_T_add_U R (2 * m)
      push_cast
      rw [show 2 * ((m : ℤ) + 1) = 2 * m + 2 by ring]
      exact this
    have hT : 2 * T R ((m + 1 : ℕ)) * T R ((m + 1 : ℕ)) = T R (2 * (m + 1 : ℕ)) + T R 0 := by
      have := T_mul_T R ((m + 1 : ℕ)) ((m + 1 : ℕ))
      rw [sub_self, ← two_mul] at this
      exact this
    have hP := T_sq_add_one_sub_X_sq_mul_U_sq R m
    rw [hU, sum_range_succ, ih]
    push_cast at hT hP ⊢
    rw [T_zero] at hT
    linear_combination (-2) * hT + 4 * hP

end CommRing

section Order

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem one_sub_sq_mul_eval_U_sq_le_one (n : ℤ) (x : K) :
    (1 - x ^ 2) * (U K n).eval x ^ 2 ≤ 1 := by
  have h := congrArg (eval x) (T_sq_add_one_sub_X_sq_mul_U_sq K n)
  simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X] at h
  nlinarith [sq_nonneg ((T K (n + 1)).eval x)]

theorem abs_eval_T_le_one (n : ℤ) {x : K} (hx : |x| ≤ 1) : |(T K n).eval x| ≤ 1 := by
  have h := congrArg (eval x) (T_sq_add_one_sub_X_sq_mul_U_sq K (n - 1))
  simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_add_cancel] at h
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have hle : (T K n).eval x ^ 2 ≤ 1 := by nlinarith [sq_nonneg ((U K (n - 1)).eval x)]
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

theorem abs_eval_U_le (n : ℕ) {x : K} (hx : |x| ≤ 1) : |(U K n).eval x| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := congrArg (eval x) (U_eq_X_mul_U_add_T K n)
    simp only [eval_add, eval_mul, eval_X] at h
    push_cast
    rw [h]
    calc |x * (U K n).eval x + (T K (n + 1)).eval x|
        ≤ |x| * |(U K n).eval x| + |(T K (n + 1)).eval x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (n + 1) + 1 := by
          gcongr
          · exact abs_eval_T_le_one _ hx
      _ = n + 1 + 1 := by ring

/-- `|U_(2m+1)(x)| ≤ (2m + 2) |x|` for `|x| ≤ 1`. -/
theorem abs_eval_U_two_mul_add_one_le (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |(U K (2 * m + 1)).eval x| ≤ (2 * m + 2) * |x| := by
  rw [U_two_mul_add_one, eval_mul, eval_mul, eval_comp, T_two]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
  have hy : |2 * x ^ 2 - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg x, sq_abs x, sq_nonneg x]
  have hU := abs_eval_U_le (K := K) m hy
  rw [abs_mul, abs_mul, abs_two]
  calc 2 * |x| * |(U K m).eval (2 * x ^ 2 - 1)| ≤ 2 * |x| * (m + 1) := by gcongr
    _ = (2 * m + 2) * |x| := by ring

/-- `U_i(x) ≥ 1` for `i < m` when `0 ≤ x ≤ 1` and `4 m² (1 - x²) < 1`. -/
private theorem one_le_eval_U_of_small {m : ℕ} {x : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : 4 * (m : K) ^ 2 * (1 - x ^ 2) < 1) :
    ∀ i < m, 1 ≤ (U K i).eval x := by
  have habs : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hx1⟩
  have hlin : 1 - x ≤ 1 - x ^ 2 := by nlinarith
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have ih' := ih (by lia)
    have h := congrArg (eval x) (U_succ_sub_U K i)
    simp only [eval_sub, eval_mul, eval_one, eval_X, eval_ofNat, eval_finsetSum] at h
    push_cast at h ⊢
    have hsum : ∑ j ∈ range (i + 1), (U K j).eval x ≤ ∑ j ∈ range (i + 1), ((j : K) + 1) :=
      sum_le_sum fun j _ ↦ (le_abs_self _).trans (abs_eval_U_le j habs)
    have hgauss : ∑ j ∈ range (i + 1), ((j : K) + 1) ≤ (m : K) ^ 2 := by
      have hcard : ∀ j ∈ range (i + 1), (j : K) + 1 ≤ m := fun j hj ↦ by
        have : j + 1 ≤ m := by have := mem_range.mp hj; lia
        exact_mod_cast this
      calc ∑ j ∈ range (i + 1), ((j : K) + 1) ≤ ∑ _j ∈ range (i + 1), (m : K) := sum_le_sum hcard
        _ = (i + 1) * m := by simp
        _ ≤ m * m := by
          have : (i + 1 : K) ≤ m := by exact_mod_cast hi.le
          nlinarith [(m.cast_nonneg : (0 : K) ≤ m)]
        _ = (m : K) ^ 2 := by ring
    have hpos : 0 ≤ 1 - x := by linarith
    have : 2 * (1 - x) * ∑ j ∈ range (i + 1), (U K j).eval x < 1 := by
      have hm2 : 0 ≤ (m : K) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left (hsum.trans hgauss) hpos]
    linarith

/-- `|U_(2m)(x)| ≤ 1 + 2m x²` for `|x| ≤ 1`. -/
theorem abs_eval_U_two_mul_le (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |(U K (2 * m)).eval x| ≤ 1 + 2 * m * x ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm1 : (1 : K) ≤ m := by exact_mod_cast hm
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  set y : K := 1 - x ^ 2 with hy_def
  have hy0 : 0 ≤ y := by linarith
  have hA : 0 < 1 + 2 * m * x ^ 2 := by positivity
  rcases le_or_gt 1 (4 * (m : K) ^ 2 * y) with hbig | hsmall
  · -- `y U² ≤ 1 ≤ y A²`
    have hyU := one_sub_sq_mul_eval_U_sq_le_one (2 * (m : ℤ)) x
    have hyA : 1 ≤ y * (1 + 2 * m * x ^ 2) ^ 2 := by
      have hfac : y * (1 + 2 * m * x ^ 2) ^ 2 - 1 =
          (1 - y) * ((4 * m ^ 2 * y - 1) * (1 - y) + (4 * m - 1) * y) := by
        rw [hy_def]; ring
      have h1 : 0 ≤ (4 * (m : K) ^ 2 * y - 1) * (1 - y) :=
        mul_nonneg (by linarith) (by rw [hy_def]; nlinarith)
      have h2 : 0 ≤ (4 * (m : K) - 1) * y := mul_nonneg (by linarith) hy0
      nlinarith [mul_nonneg (show (0 : K) ≤ 1 - y by rw [hy_def]; nlinarith) (add_nonneg h1 h2)]
    have hypos : 0 < y := by
      rcases hy0.eq_or_lt with h | h
      · rw [← h] at hbig; simp at hbig; linarith
      · exact h
    have hsq : (U K (2 * (m : ℤ))).eval x ^ 2 ≤ (1 + 2 * m * x ^ 2) ^ 2 :=
      le_of_mul_le_mul_left (by rw [← hy_def] at hyU; linarith) hypos
    exact abs_le_of_sq_le_sq' hsq hA.le |>.elim (fun h1 h2 ↦ abs_le.mpr ⟨h1, h2⟩)
  · -- near `±1`: reduce to `0 ≤ x` by parity
    have key : ∀ z : K, 0 ≤ z → z ≤ 1 → 4 * (m : K) ^ 2 * (1 - z ^ 2) < 1 →
        |(U K (2 * m)).eval z| ≤ 1 + 2 * m * z ^ 2 := by
      intro z hz0 hz1 hzs
      have habs : |z| ≤ 1 := abs_le.mpr ⟨by linarith, hz1⟩
      have hone := one_le_eval_U_of_small hz0 hz1 hzs
      have h := congrArg (eval z) (U_two_mul_eq_sub_sum_sq K m)
      simp only [eval_sub, eval_add, eval_mul, eval_one, eval_X, eval_pow, eval_ofNat,
        eval_natCast, eval_finsetSum] at h
      have hlow : (m : K) ≤ ∑ i ∈ range m, (U K i).eval z ^ 2 := by
        calc (m : K) = ∑ _i ∈ range m, (1 : K) := by simp
          _ ≤ ∑ i ∈ range m, (U K i).eval z ^ 2 :=
            sum_le_sum fun i hi ↦ by nlinarith [hone i (mem_range.mp hi)]
      have hupp : ∑ i ∈ range m, (U K i).eval z ^ 2 ≤ (m : K) * (m : K) ^ 2 := by
        calc ∑ i ∈ range m, (U K i).eval z ^ 2 ≤ ∑ _i ∈ range m, (m : K) ^ 2 := by
              refine sum_le_sum fun i hi ↦ ?_
              have hb := abs_eval_U_le i habs
              have hi' : (i : K) + 1 ≤ m := by
                have := mem_range.mp hi; exact_mod_cast this
              have := sq_le_sq' (by linarith [neg_abs_le ((U K i).eval z)])
                ((le_abs_self _).trans (hb.trans hi'))
              linarith
          _ = (m : K) * (m : K) ^ 2 := by simp
      have hz2 : 0 ≤ 1 - z ^ 2 := by nlinarith
      rw [h, abs_le]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hupp hz2]
      · nlinarith [mul_le_mul_of_nonneg_left hlow hz2]
    rcases le_total 0 x with hx0 | hx0
    · exact key x hx0 (abs_le.mp hx).2 hsmall
    · have hev : (U K (2 * (m : ℤ))).eval (-x) = (U K (2 * (m : ℤ))).eval x := by
        have h := U_eval_neg (R := K) (2 * m) x
        push_cast at h
        rw [h, Int.negOnePow_two_mul, Units.val_one, Int.cast_one, one_mul]
      have hk := key (-x) (by linarith) (by linarith [(abs_le.mp hx).1])
        (by rw [neg_sq]; exact hsmall)
      rwa [hev, neg_sq] at hk

end Order

end Polynomial.Chebyshev
