import RealRooted.CombinatorialExamples.BigDescents321.SigmaSign
import RealRooted.CombinatorialExamples.BigDescents321.Backward

/-!
# Positivity of `F_n` at the zeros of `G_(n-2)`

Let `n = k + 2 ≥ 25` and let `a` be a real zero of `G_k` with `|a| ≤ 1`. With the coordinates
`b_m` of the residual polynomial `R_n` and the backward values `H_j`, put
`F_n(a) = ∑_(j<k) b_(k-1-j) H_j(a)`. Then `R_n(a) = G_(k-1)(a) F_n(a)` and
`Q_n(a) = -a G_(k-1)(a) F_n(a)`, and the coefficient criterion gives
`F_n(a) ≥ L_n (1 - a²) + E_n a² > 0` (issue #1143, §8 and §12).

## Main statements

* `eval_transformed_eq_neg_mul`: `Q_n(a) = -a G_(k-1)(a) F_n(a)`.
* `zetaF_pos`: `F_n(a) > 0`.
-/

open Finset Polynomial

namespace RealRooted.BigDescents321

/-! ### Scalar identities over `ℚ` -/

theorem gegen_eval_one : ∀ m : ℕ, (gegen m).eval 1 = ((m : ℚ) + 1) * (m + 2) / 2
  | 0 => by simp
  | 1 => by norm_num [gegen_one]
  | m + 2 => by
    have h := congrArg (Polynomial.eval 1) (gegen_rec m)
    simp only [eval_mul, eval_add, eval_sub, eval_X, eval_natCast, eval_ofNat, mul_one] at h
    rw [gegen_eval_one (m + 1), gegen_eval_one m] at h
    have hm : ((m : ℚ) + 2) ≠ 0 := by positivity
    push_cast at h ⊢
    apply mul_left_cancel₀ hm
    rw [h]
    ring

/-- `∑_m b_(n,m) = α_n + β_n - σ_n`. -/
theorem coordSum_residCoord {k : ℕ} (hk : 2 ≤ k) :
    coordSum (residCoord (k + 2)) (k - 1) = alphaN (k + 2) + betaN (k + 2) - sigmaQ (k + 2) := by
  have hr : ∀ j, k - 1 < j → residCoord (k + 2) j = 0 := fun j hj ↦ residCoord_of_lt (by lia)
  have hxr : ∀ j, k < j → xShift (residCoord (k + 2)) j = 0 := fun j hj ↦ by
    simp only [xShift, hr (j + 1) (by lia), zero_mul, zero_div, add_zero, hr (j - 1) (by lia),
      ite_self]
  have hsum := congrArg (fun f : ℕ → ℚ ↦ ∑ i ∈ range (k + 2 + 1), f i)
    (funext (xShift_residCoord_add hk))
  simp only [sum_add_distrib, ← mul_sum, sum_ite_eq', mem_range,
    show k < k + 2 + 1 by lia, ↓reduceIte] at hsum
  have h1 : ∑ i ∈ range (k + 2 + 1), xShift (residCoord (k + 2)) i =
      coordSum (residCoord (k + 2)) (k - 1) := by
    have hx := coordSum_xShift hr
    rw [show k - 1 + 1 = k by lia] at hx
    rw [← coordSum, coordSum_eq_of_le hxr (by lia), hx, residCoord_of_le (by lia)]
    simp [residRaw]
  have h2 : ∑ i ∈ range (k + 2 + 1), sqShift k i = 1 := by
    have hs1 : ∀ j, k < j → (fun i ↦ if i = k then (1 : ℚ) else 0) j = 0 := fun j hj ↦ by
      simp only [show j ≠ k by lia, ↓reduceIte]
    have hs2 : ∀ j, k + 1 < j → xShift (fun i ↦ if i = k then (1 : ℚ) else 0) j = 0 :=
      fun j hj ↦ by
        rw [xShift_single]
        simp only [show j ≠ k + 1 by lia, show j + 1 ≠ k by lia, ↓reduceIte, add_zero]
    rw [← coordSum, sqShift, coordSum_xShift hs2, coordSum_xShift hs1, xShift_single]
    simp only [show (0 : ℕ) ≠ k + 1 by lia, show 0 + 1 ≠ k by lia, show (0 : ℕ) ≠ k by lia,
      ↓reduceIte, add_zero, mul_zero, sub_zero, coordSum, sum_ite_eq', mem_range,
      show k < k + 1 by lia]
  rw [h1, h2, ← coordSum] at hsum
  simp only [sigmaQ]
  linarith

/-- `Q_n(1) = 2^(-n) F_(n+1) > 0`. -/
theorem transformed_eval_one_pos (n : ℕ) : 0 < (transformed n).eval 1 := by
  have h := aeval_transformed (c := (1 : ℝ)) one_ne_zero n
  rw [one_pow, inv_one, sub_self, eval_zero_bigDescentPoly] at h
  have hpos : (0 : ℝ) < (1 / 2) ^ n * ((n + 1).fib : ℝ) := by
    have : (0 : ℝ) < ((n + 1).fib : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
    positivity
  rw [← h, show (1 : ℝ) = algebraMap ℚ ℝ 1 by simp,
    aeval_algebraMap_apply_eq_algebraMap_eval] at hpos
  exact (Rat.cast_pos (K := ℝ)).mp (by simpa using hpos)

/-- `R_n(1) = ∑_m b_m G_m(1)`, and `R_n(1) = (α_n + β_n) G_k(1) - Q_n(1)`. -/
private theorem residual_eval_one {k : ℕ} (hk : 2 ≤ k) :
    ∑ m ∈ range k, residCoord (k + 2) m * (((m : ℚ) + 1) * (m + 2) / 2) =
      (alphaN (k + 2) + betaN (k + 2)) * (((k : ℚ) + 1) * (k + 2) / 2) -
        (transformed (k + 2)).eval 1 := by
  have h := congrArg (Polynomial.eval 1) (X_mul_residual hk)
  simp only [eval_mul, eval_X, one_mul, eval_sub, eval_add, eval_C, eval_pow, one_pow,
    mul_one, gegen_eval_one] at h
  rw [← h, residual, gsum, show k + 2 - 3 + 1 = k by lia, eval_finsetSum]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [eval_mul, eval_C, gegen_eval_one]

/-- `E_n = ∑_j b_(k-1-j) H_j(1) = Q_n(1)/(k + 1) - (k + 2) σ_n / 2`, with
`H_j(1) = (j + 1)(2k + 2 - j)/(2k + 2)`. -/
theorem sum_residCoord_mul_backOne {k : ℕ} (hk : 2 ≤ k) :
    ∑ j ∈ range k, residCoord (k + 2) (k - 1 - j) *
        (((j : ℚ) + 1) * (2 * k + 2 - j) / (2 * k + 2)) =
      (transformed (k + 2)).eval 1 / (k + 1) - ((k : ℚ) + 2) / 2 * sigmaQ (k + 2) := by
  have e : ∑ j ∈ range k, residCoord (k + 2) (k - 1 - j) *
      (((j : ℚ) + 1) * (2 * k + 2 - j) / (2 * k + 2)) =
      ∑ m ∈ range k, residCoord (k + 2) m * (((k : ℚ) + 2) / 2 -
        ((m : ℚ) + 1) * (m + 2) / 2 / (k + 1)) := by
    rw [← sum_range_reflect (fun m ↦ residCoord (k + 2) m * (((k : ℚ) + 2) / 2 -
      ((m : ℚ) + 1) * (m + 2) / 2 / (k + 1))) k]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)]
    have : ((k : ℚ) + 1) ≠ 0 := by positivity
    have : (2 * (k : ℚ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hσ := coordSum_residCoord hk
  rw [coordSum, show k - 1 + 1 = k by lia] at hσ
  have hR := residual_eval_one hk
  rw [e]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  have hR' : ∑ m ∈ range k, residCoord (k + 2) m * (((m : ℚ) + 1) * (m + 2) / 2 / (k + 1)) =
      (∑ m ∈ range k, residCoord (k + 2) m * (((m : ℚ) + 1) * (m + 2) / 2)) / (k + 1) := by
    rw [sum_div]
    exact sum_congr rfl fun m _ ↦ by ring
  rw [hR', hR, hσ]
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem alphaN_pos {n : ℕ} (hn : 2 ≤ n) : 0 < alphaN n := by
  have h2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  rw [alphaN]
  have : (0 : ℚ) < (n : ℚ) ^ 2 - 1 := by nlinarith
  apply div_pos <;> nlinarith

/-- `L_n = α_n + β_n - σ_n - (2k - 1)/k b_(n,1) > 0` for `n = j + 10 ≥ 25`, `k = n - 2`. -/
theorem lowerCoeff_pos {j : ℕ} (hj : 15 ≤ j) :
    0 < alphaN (j + 10) + betaN (j + 10) - sigmaQ (j + 10) -
      (2 * ((j : ℚ) + 8) - 1) / ((j : ℚ) + 8) * residCoord (j + 10) (j + 5) := by
  have hz := neg_half_lt_zN (n := j + 10) (by lia)
  have hσ := sigmaQ_neg (n := j + 10) (by lia)
  have hα := alphaN_pos (n := j + 10) (by lia)
  rw [residCoord_top_b1, betaN_eq_zN_mul (by lia)]
  obtain ⟨s, rfl⟩ : ∃ s, j = s + 15 := ⟨j - 15, by lia⟩
  set z := zN (s + 15 + 10)
  set α := alphaN (s + 15 + 10)
  push_cast
  have hs : (0 : ℚ) ≤ s := s.cast_nonneg
  have hN0 : 0 < 4 * ((s : ℚ) + 23) ^ 4 - 72 * ((s : ℚ) + 23) ^ 3 + 197 * ((s : ℚ) + 23) ^ 2 -
      201 * ((s : ℚ) + 23) + 54 := by
    have : 4 * ((s : ℚ) + 23) ^ 4 - 72 * ((s : ℚ) + 23) ^ 3 + 197 * ((s : ℚ) + 23) ^ 2 -
        201 * ((s : ℚ) + 23) + 54 = 4 * (s : ℚ) ^ 4 + 296 * s ^ 3 + 7925 * s ^ 2 + 89269 * s +
          342984 := by ring
    rw [this]
    positivity
  have hS : 0 < 5 * ((s : ℚ) + 23) ^ 3 - 6 * ((s : ℚ) + 23) ^ 2 - 5 * ((s : ℚ) + 23) + 3 := by
    have : 5 * ((s : ℚ) + 23) ^ 3 - 6 * ((s : ℚ) + 23) ^ 2 - 5 * ((s : ℚ) + 23) + 3 =
        5 * (s : ℚ) ^ 3 + 339 * s ^ 2 + 7654 * s + 57549 := by ring
    rw [this]
    positivity
  have hbr : 0 < (4 * ((s : ℚ) + 23) ^ 4 - 72 * ((s : ℚ) + 23) ^ 3 + 197 * ((s : ℚ) + 23) ^ 2 -
      201 * ((s : ℚ) + 23) + 54 + (z + 1 / 2) * (8 * (2 * ((s : ℚ) + 23) + 3) *
        (5 * ((s : ℚ) + 23) ^ 3 - 6 * ((s : ℚ) + 23) ^ 2 - 5 * ((s : ℚ) + 23) + 3))) /
      (8 * ((s : ℚ) + 23) ^ 2 * ((s : ℚ) + 23 - 2) * (2 * ((s : ℚ) + 23) + 3)) := by
    have : 0 < z + 1 / 2 := by linarith
    have : (0 : ℚ) < (s : ℚ) + 23 - 2 := by linarith
    positivity
  have key : α + z * α - sigmaQ (s + 15 + 10) -
      (2 * ((s : ℚ) + 15 + 8) - 1) / ((s : ℚ) + 15 + 8) *
        (α * (-(2 * ((s : ℚ) + 15 + 8) - 3) *
          (16 * ((s : ℚ) + 15 + 8) ^ 2 * z + 7 * ((s : ℚ) + 15 + 8) ^ 2 +
            40 * ((s : ℚ) + 15 + 8) * z + ((s : ℚ) + 15 + 8) + 24 * z + 30) /
          (8 * ((s : ℚ) + 15 + 8) * ((s : ℚ) + 15 + 8 - 2) * (2 * ((s : ℚ) + 15 + 8) + 3)))) =
      α * ((4 * ((s : ℚ) + 23) ^ 4 - 72 * ((s : ℚ) + 23) ^ 3 + 197 * ((s : ℚ) + 23) ^ 2 -
        201 * ((s : ℚ) + 23) + 54 + (z + 1 / 2) * (8 * (2 * ((s : ℚ) + 23) + 3) *
          (5 * ((s : ℚ) + 23) ^ 3 - 6 * ((s : ℚ) + 23) ^ 2 - 5 * ((s : ℚ) + 23) + 3))) /
        (8 * ((s : ℚ) + 23) ^ 2 * ((s : ℚ) + 23 - 2) * (2 * ((s : ℚ) + 23) + 3))) -
        sigmaQ (s + 15 + 10) := by
    have : (s : ℚ) + 15 + 8 - 2 ≠ 0 := by intro h; linarith
    have : (s : ℚ) + 23 - 2 ≠ 0 := by intro h; linarith
    field_simp
    ring
  rw [key]
  have := mul_pos hα hbr
  linarith

/-! ### The real criterion at the zeros of `G_k` -/

/-- `F_n(x) = ∑_(j<k) b_(n, k-1-j) H_j(x)`, with `n = k + 2`. -/
noncomputable def zetaF (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range k, (residCoord (k + 2) (k - 1 - j) : ℝ) * backH k x j

/-- `R_n(a) = G_(k-1)(a) F_n(a)` at a zero `a` of `G_k`. -/
theorem aeval_residual_eq {k : ℕ} (hk : 2 ≤ k) {a : ℝ} (ha : aeval a (gegen k) = 0) :
    aeval a (residual (k + 2)) = aeval a (gegen (k - 1)) * zetaF k a := by
  rw [residual, gsum, show k + 2 - 3 + 1 = k by lia, map_sum, zetaF, mul_sum,
    ← sum_range_reflect]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  rw [map_mul, aeval_C, aeval_gegen_eq_backH ha j (by lia), eq_ratCast]
  ring

/-- `Q_n(a) = -a G_(k-1)(a) F_n(a)` at a zero `a` of `G_k`. -/
theorem aeval_transformed_eq_neg_mul {k : ℕ} (hk : 2 ≤ k) {a : ℝ} (ha : aeval a (gegen k) = 0) :
    aeval a (transformed (k + 2)) = -a * aeval a (gegen (k - 1)) * zetaF k a := by
  have h := congrArg (aeval a) (X_mul_residual hk)
  simp only [map_mul, map_sub, map_add, aeval_X, ha, mul_zero, zero_sub] at h
  rw [aeval_residual_eq hk ha] at h
  linear_combination h

/-- The tail signs over `ℚ`: `b_(n,m) ≤ 0` for `m ≤ n - 7` of parity opposite to `n`,
for `n = j + 10 ≥ 25`. -/
theorem residCoord_tail_nonpos {j m : ℕ} (hj : 15 ≤ j) (hm : m ≤ j + 3)
    (hp : (j + 10 + m) % 2 = 1) : residCoord (j + 10) m ≤ 0 := by
  have hz := zN_mem (n := j + 10) (by lia)
  have hα := alphaN_pos (n := j + 10) (by lia)
  have hjq : (15 : ℚ) ≤ j := by exact_mod_cast hj
  rcases (show m = j + 3 ∨ m = j + 1 ∨ m + 1 ≤ j by lia) with rfl | rfl | h
  · rw [residCoord_top_b2]
    have hκ : 0 < (2 * ((j : ℚ) + 10) - 11) * ((j : ℚ) + 10 - 1) * ((j : ℚ) + 10 - 3) /
        (((j : ℚ) + 10 - 2) * ((j : ℚ) + 10 - 4) * ((j : ℚ) + 10 - 6)) := by
      apply div_pos
      · apply mul_pos (mul_pos _ _) _ <;> linarith
      · apply mul_pos (mul_pos _ _) _ <;> linarith
    have hzU : zN (j + 10) - upperU (j + 10) < 0 := by linarith [hz.2]
    exact (mul_neg_of_pos_of_neg hα (mul_neg_of_pos_of_neg hκ hzU)).le
  · rw [residCoord_top_b3]
    have hκ : 0 < (2 * ((j : ℚ) + 10) - 15) * ((j : ℚ) + 10 - 1) * ((j : ℚ) + 10 - 3) *
        ((j : ℚ) + 10 - 5) / (((j : ℚ) + 10 - 2) * ((j : ℚ) + 10 - 4) * ((j : ℚ) + 10 - 6) *
          ((j : ℚ) + 10 - 8)) := by
      apply div_pos
      · apply mul_pos (mul_pos (mul_pos _ _) _) _ <;> linarith
      · apply mul_pos (mul_pos (mul_pos _ _) _) _ <;> linarith
    have hzL : 0 < zN (j + 10) - lowerL (j + 10) := by linarith [hz.1]
    have hneg : -(2 * ((j : ℚ) + 10) - 15) * ((j : ℚ) + 10 - 1) * ((j : ℚ) + 10 - 3) *
        ((j : ℚ) + 10 - 5) / (((j : ℚ) + 10 - 2) * ((j : ℚ) + 10 - 4) * ((j : ℚ) + 10 - 6) *
          ((j : ℚ) + 10 - 8)) = -((2 * ((j : ℚ) + 10) - 15) * ((j : ℚ) + 10 - 1) *
          ((j : ℚ) + 10 - 3) * ((j : ℚ) + 10 - 5) / (((j : ℚ) + 10 - 2) * ((j : ℚ) + 10 - 4) *
          ((j : ℚ) + 10 - 6) * ((j : ℚ) + 10 - 8))) := by ring
    rw [hneg]
    exact (mul_neg_of_pos_of_neg hα (mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) hzL)).le
  · rcases m with _ | m
    · rw [residCoord_of_le (by lia)]
      simp [residRaw]
    · exact (residCoord_neg_of_le (n := j + 10) (j := m) (by lia) (by lia) (by lia)).le

/-- `F_n(x) > 0` on `[-1, 1]` for `n = k + 2 ≥ 25`. -/
theorem zetaF_pos {k : ℕ} (hk : 23 ≤ k) {x : ℝ} (hx : |x| ≤ 1) : 0 < zetaF k x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by lia⟩
  set c : ℕ → ℝ := fun i ↦ (residCoord (j + 8 + 2) (j + 8 - 1 - i) : ℝ) with hc
  have hodd : ∀ i, i % 2 = 1 → c i = 0 := by
    intro i hi
    simp only [hc]
    rw [residCoord_of_le (by lia)]
    rcases le_or_gt (j + 8) i with h | h
    · rw [show j + 8 - 1 - i = 0 by lia]
      simp [residRaw]
    · rw [residRaw_of_even_add (by lia) _ (by lia)]
      simp
  have hneg : ∀ i, 4 ≤ i → i < j + 8 → c i ≤ 0 := by
    intro i h4 hi
    rcases Nat.even_or_odd' i with ⟨l, rfl | rfl⟩
    · have := residCoord_tail_nonpos (j := j) (m := j + 8 - 1 - 2 * l) (by lia) (by lia) (by lia)
      simp only [hc]
      exact_mod_cast this
    · rw [hodd _ (by lia)]
  have hcrit := backward_criterion (k := j + 8) (by lia) c hodd hneg hx
  have hsum : ∑ i ∈ range (j + 8), c i =
      ((alphaN (j + 10) + betaN (j + 10) - sigmaQ (j + 10) : ℚ) : ℝ) := by
    have h := coordSum_residCoord (k := j + 8) (by lia)
    rw [coordSum, show j + 8 - 1 + 1 = j + 8 by lia, ← sum_range_reflect] at h
    simp only [hc]
    rw [← Rat.cast_sum]
    exact_mod_cast h
  have hsplit : ∑ i ∈ range (j + 8), c i = c 0 + c 1 + c 2 + c 3 + ∑ i ∈ Ico 4 (j + 8), c i := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (show 0 ≤ 4 by norm_num) (show 4 ≤ j + 8 by lia)]
    simp [sum_Ico_eq_sum_range, sum_range_succ]
  have hc2 : c 2 = ((residCoord (j + 10) (j + 5) : ℚ) : ℝ) := by
    simp only [hc, show j + 8 - 1 - 2 = j + 5 by lia]
  have hL : c 0 - (((j + 8 : ℕ) : ℝ) - 1) / ((j + 8 : ℕ) : ℝ) * c 2 + ∑ i ∈ Ico 4 (j + 8), c i =
      ((alphaN (j + 10) + betaN (j + 10) - sigmaQ (j + 10) -
        (2 * ((j : ℚ) + 8) - 1) / ((j : ℚ) + 8) * residCoord (j + 10) (j + 5) : ℚ) : ℝ) := by
    have h1 := hodd 1 rfl
    have h3 := hodd 3 rfl
    have hI : ∑ i ∈ Ico 4 (j + 8), c i = ∑ i ∈ range (j + 8), c i - c 0 - c 2 := by
      rw [hsplit, h1, h3]; ring
    rw [hI, hsum, hc2]
    push_cast
    have : ((j : ℝ) + 8) ≠ 0 := by positivity
    field_simp
    ring
  have hLpos := lowerCoeff_pos (j := j) (by lia)
  have hE : ∑ i ∈ range (j + 8), c i * backH (j + 8) 1 i =
      (((transformed (j + 8 + 2)).eval 1 / ((j + 8 : ℕ) + 1) -
        (((j + 8 : ℕ) : ℚ) + 2) / 2 * sigmaQ (j + 8 + 2) : ℚ) : ℝ) := by
    rw [← sum_residCoord_mul_backOne (k := j + 8) (by lia), Rat.cast_sum]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [backH_eval_one i (by have := mem_range.mp hi; lia)]
    simp only [hc]
    push_cast
    ring
  have hEpos : 0 < (transformed (j + 8 + 2)).eval 1 / ((j + 8 : ℕ) + 1) -
      (((j + 8 : ℕ) : ℚ) + 2) / 2 * sigmaQ (j + 8 + 2) := by
    have h1 := transformed_eval_one_pos (j + 8 + 2)
    have h2 := sigmaQ_neg (n := j + 8 + 2) (by lia)
    have : (0 : ℚ) < ((j + 8 : ℕ) : ℚ) + 2 := by positivity
    have : 0 < (transformed (j + 8 + 2)).eval 1 / ((j + 8 : ℕ) + 1) := by positivity
    nlinarith
  rw [hL, hE] at hcrit
  have hLr : (0 : ℝ) < ((alphaN (j + 10) + betaN (j + 10) - sigmaQ (j + 10) -
      (2 * ((j : ℚ) + 8) - 1) / ((j : ℚ) + 8) * residCoord (j + 10) (j + 5) : ℚ) : ℝ) := by
    exact_mod_cast hLpos
  have hEr : (0 : ℝ) < (((transformed (j + 8 + 2)).eval 1 / ((j + 8 : ℕ) + 1) -
      (((j + 8 : ℕ) : ℚ) + 2) / 2 * sigmaQ (j + 8 + 2) : ℚ) : ℝ) := by
    exact_mod_cast hEpos
  have hx2 : x ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg x) hx
  refine lt_of_lt_of_le ?_ hcrit
  rcases le_or_gt (x ^ 2) (1 / 2) with h | h
  · have : 0 ≤ (((transformed (j + 8 + 2)).eval 1 / ((j + 8 : ℕ) + 1) -
        (((j + 8 : ℕ) : ℚ) + 2) / 2 * sigmaQ (j + 8 + 2) : ℚ) : ℝ) * x ^ 2 :=
      mul_nonneg hEr.le (sq_nonneg x)
    nlinarith
  · have : 0 ≤ ((alphaN (j + 10) + betaN (j + 10) - sigmaQ (j + 10) -
        (2 * ((j : ℚ) + 8) - 1) / ((j : ℚ) + 8) * residCoord (j + 10) (j + 5) : ℚ) : ℝ) *
          (1 - x ^ 2) := mul_nonneg hLr.le (by linarith)
    nlinarith

end RealRooted.BigDescents321
