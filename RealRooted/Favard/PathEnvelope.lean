import RealRooted.Mathlib.RingTheory.Polynomial.Chebyshev.Bounds
import RealRooted.Favard.Recurrence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The weighted-path envelope for symmetric Favard families

Let `0 ≤ η_e ≤ 1/4` for `e ≥ 1`, and let `D` satisfy `D_0 = 1`, `D_1 = x` and
`D_(n+2) = x D_(n+1) - η_(n+1) D_n`, as the evaluations of a Favard family with zero
diagonal do. For `|x| ≤ 1` we prove

* `|D_(2m+1)(x)| ≤ D_(2m+1)(1) |x|`, and
* `|D_(2m)(x)| ≤ B_m (1 - x²) + D_(2m)(1) x²`, where `B_m = ∏_(i < m) (1/2 - η_(2i+1))`.

The proof compares `D` with the normalized Chebyshev values `Û_n = 2^(-n) U_n(x)`, which
solve the recurrence with every `η_e = 1/4`. With `δ_e = 1/4 - η_e ≥ 0`, the last-edge
decomposition `D_n = Û_n + ∑_(e < n) δ_(e+1) Û_(n-2-e) D_e` has nonnegative coefficients,
and a product-of-chords estimate closes a strong induction. Zero edges are allowed.

## Main results

* `abs_le_of_odd`, `abs_le_of_even`: the two envelope bounds for sequences, which need only
  `η_e ≤ 1/4`; `envConst_le_one` uses `0 ≤ η_e` as well.
* `SatisfiesFavardRecurrence.abs_eval_le_envelope` and
  `SatisfiesFavardRecurrence.abs_eval_le_of_odd`: the same bounds for a Favard family.
-/

open Finset Polynomial

namespace RealRooted.PathEnvelope

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The normalized Chebyshev value `Û_n(x) = 2^(-n) U_n(x)`. -/
noncomputable def chebHat (n : ℕ) (x : K) : K := (Chebyshev.U K n).eval x / 2 ^ n

/-- The shifted normalized Chebyshev value: `0` at `0`, and `Û_k` at `k + 1`. -/
noncomputable def chebShift : ℕ → K → K
  | 0, _ => 0
  | k + 1, x => chebHat k x

@[simp] theorem chebHat_zero (x : K) : chebHat 0 x = 1 := by simp [chebHat]

@[simp] theorem chebHat_one (x : K) : chebHat 1 x = x := by
  simp [chebHat, Chebyshev.U_one]

theorem chebHat_add_two (n : ℕ) (x : K) :
    chebHat (n + 2) x = x * chebHat (n + 1) x - chebHat n x / 4 := by
  have h := congrArg (eval x) (Chebyshev.U_add_two K n)
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at h
  simp only [chebHat]
  push_cast at h ⊢
  rw [h]
  field_simp
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem chebShift_zero (x : K) : chebShift 0 x = 0 := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem chebShift_succ (k : ℕ) (x : K) : chebShift (k + 1) x = chebHat k x := rfl

theorem chebShift_add_two (k : ℕ) (x : K) :
    chebShift (k + 2) x = x * chebShift (k + 1) x - chebShift k x / 4 := by
  cases k with
  | zero => simp
  | succ k => simp only [chebShift_succ]; exact chebHat_add_two k x

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem chebHat_eval_one (n : ℕ) : chebHat n (1 : K) = (n + 1) / 2 ^ n := by
  simp [chebHat, Chebyshev.U_eval_one]

theorem chebHat_one_pos (n : ℕ) : 0 < chebHat n (1 : K) := by
  rw [chebHat_eval_one]; positivity

theorem chebShift_one_nonneg (k : ℕ) : 0 ≤ chebShift k (1 : K) := by
  cases k with
  | zero => simp
  | succ k => exact (chebHat_one_pos k).le

/-- The odd Chebyshev chord: `|Û_(2m+1)(x)| ≤ Û_(2m+1)(1) |x|`. -/
theorem abs_chebHat_odd_le (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |chebHat (2 * m + 1) x| ≤ chebHat (2 * m + 1) 1 * |x| := by
  have h := Chebyshev.abs_eval_U_two_mul_add_one_le (K := K) m hx
  rw [chebHat, chebHat_eval_one, abs_div, abs_of_pos (by positivity : (0 : K) < 2 ^ _)]
  push_cast at h ⊢
  rw [div_mul_eq_mul_div]
  gcongr
  linarith

/-- The even Chebyshev chord: `|Û_(2m)(x)| ≤ 4^(-m) (1 - x²) + Û_(2m)(1) x²`. -/
theorem abs_chebHat_even_le (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |chebHat (2 * m) x| ≤ (1 / 4) ^ m * (1 - x ^ 2) + chebHat (2 * m) 1 * x ^ 2 := by
  have h := Chebyshev.abs_eval_U_two_mul_le (K := K) m hx
  rw [chebHat, chebHat_eval_one, abs_div, abs_of_pos (by positivity : (0 : K) < 2 ^ _)]
  push_cast at h ⊢
  have h4 : (2 : K) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  rw [h4, div_le_iff₀ (by positivity)]
  calc |(Chebyshev.U K (2 * (m : ℤ))).eval x| ≤ 1 + 2 * m * x ^ 2 := h
    _ = ((1 / 4) ^ m * (1 - x ^ 2) + (2 * m + 1) / 4 ^ m * x ^ 2) * 4 ^ m := by
      have h1 : (1 / 4 : K) ^ m * 4 ^ m = 1 := by rw [← mul_pow]; norm_num
      have h2 : (2 * m + 1) / 4 ^ m * 4 ^ m = (2 * m + 1 : K) :=
        div_mul_cancel₀ _ (by positivity)
      linear_combination -(1 - x ^ 2) * h1 - x ^ 2 * h2

theorem quarter_pow_le_chebHat_even (m : ℕ) : (1 / 4 : K) ^ m ≤ chebHat (2 * m) 1 := by
  rw [chebHat_eval_one]
  have h4 : (2 : K) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  rw [h4, one_div_pow]
  gcongr
  push_cast
  linarith [(m.cast_nonneg : (0 : K) ≤ m)]

/-! ### The last-edge decomposition -/

section Decomposition

variable {η : ℕ → K} {x : K} {d : ℕ → K}

/-- The last-edge decomposition `D_n = Û_n + ∑_(i < n) δ_(i+1) Û_(n-2-i) D_i`, written with
`chebShift` to cover the term `i = n - 1`. -/
theorem eq_chebHat_add_sum (h0 : d 0 = 1) (h1 : d 1 = x)
    (hrec : ∀ n, d (n + 2) = x * d (n + 1) - η (n + 1) * d n) (n : ℕ) :
    d n = chebHat n x + ∑ i ∈ range n, (1 / 4 - η (i + 1)) * chebShift (n - 1 - i) x * d i := by
  induction n using Nat.twoStepInduction with
  | zero => simp [h0]
  | one => simp [h1]
  | more n ih ih1 =>
    have hsum : ∑ i ∈ range n, (1 / 4 - η (i + 1)) * chebShift (n + 1 - i) x * d i =
        x * ∑ i ∈ range n, (1 / 4 - η (i + 1)) * chebShift (n - i) x * d i -
          (∑ i ∈ range n, (1 / 4 - η (i + 1)) * chebShift (n - 1 - i) x * d i) / 4 := by
      rw [mul_sum, sum_div, ← sum_sub_distrib]
      refine sum_congr rfl fun i hi ↦ ?_
      have hi' := mem_range.mp hi
      rw [show n + 1 - i = n - 1 - i + 2 by lia, show n - i = n - 1 - i + 1 by lia,
        chebShift_add_two]
      ring
    rw [hrec, sum_range_succ, sum_range_succ, show n + 2 - 1 - n = 1 by lia,
      show n + 2 - 1 - (n + 1) = 0 by lia, show n + 2 - 1 = n + 1 by lia]
    simp only [Nat.add_sub_cancel] at ih1
    rw [sum_range_succ, Nat.sub_self] at ih1
    simp only [chebShift_succ, chebHat_zero, chebShift_zero, mul_zero, zero_mul, add_zero,
      mul_one] at ih1 ⊢
    rw [hsum, chebHat_add_two]
    linear_combination x * ih1 - (1 / 4 - η (n + 1) + η (n + 1)) * ih

end Decomposition

/-! ### Chebyshev chords for the shifted values -/

/-- `|Û_(2k-1)(x)| ≤ Û_(2k-1)(1) |x|`, including the value `0` at `k = 0`. -/
theorem abs_chebShift_even_le (k : ℕ) {x : K} (hx : |x| ≤ 1) :
    |chebShift (2 * k) x| ≤ chebShift (2 * k) 1 * |x| := by
  cases k with
  | zero => simp
  | succ k =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, chebShift_succ, chebShift_succ]
    exact abs_chebHat_odd_le k hx

theorem abs_chebShift_odd_le (k : ℕ) {x : K} (hx : |x| ≤ 1) :
    |chebShift (2 * k + 1) x| ≤ (1 / 4) ^ k * (1 - x ^ 2) + chebShift (2 * k + 1) 1 * x ^ 2 := by
  simpa using abs_chebHat_even_le k hx

/-! ### The envelope constant -/

/-- The envelope constant `B_m = ∏_(i < m) (1/2 - η_(2i+1))`. -/
def envConst (η : ℕ → K) (m : ℕ) : K := ∏ i ∈ range m, (1 / 2 - η (2 * i + 1))

theorem envConst_eq_sum (η : ℕ → K) (m : ℕ) :
    envConst η m = (1 / 4) ^ m +
      ∑ j ∈ range m, (1 / 4 - η (2 * j + 1)) * (1 / 4) ^ (m - 1 - j) * envConst η j := by
  induction m with
  | zero => simp [envConst]
  | succ m ih =>
    rw [envConst, prod_range_succ, ← envConst, sum_range_succ, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ j ∈ range m, (1 / 4 - η (2 * j + 1)) * (1 / 4) ^ (m - j) * envConst η j =
        (∑ j ∈ range m, (1 / 4 - η (2 * j + 1)) * (1 / 4) ^ (m - 1 - j) * envConst η j) / 4 := by
      rw [sum_div]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [show m - j = m - 1 - j + 1 by have := mem_range.mp hj; lia, pow_succ]
      ring
    rw [hs, ih]
    ring

theorem envConst_nonneg {η : ℕ → K} (hη1 : ∀ e, η (e + 1) ≤ 1 / 4) (m : ℕ) :
    0 ≤ envConst η m :=
  prod_nonneg fun i _ ↦ by linarith [hη1 (2 * i)]

theorem envConst_le_one {η : ℕ → K} (hη0 : ∀ e, 0 ≤ η (e + 1))
    (hη1 : ∀ e, η (e + 1) ≤ 1 / 4) (m : ℕ) : envConst η m ≤ 1 :=
  prod_le_one₀ (fun i _ ↦ by linarith [hη1 (2 * i)]) fun i _ ↦ by linarith [hη0 (2 * i)]

/-- The product-of-chords estimate: if `|s| ≤ a(1-y) + by` and `|t| ≤ c(1-y) + dy` with
`0 ≤ a ≤ b`, `c ≤ d` and `0 ≤ y ≤ 1`, then `|st| ≤ ac(1-y) + bdy`. -/
theorem abs_mul_le_chord {a b c d y s t : K} (ha : 0 ≤ a) (hab : a ≤ b) (hcd : c ≤ d)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hs : |s| ≤ a * (1 - y) + b * y)
    (ht : |t| ≤ c * (1 - y) + d * y) : |s * t| ≤ a * c * (1 - y) + b * d * y := by
  rw [abs_mul]
  calc |s| * |t| ≤ (a * (1 - y) + b * y) * (c * (1 - y) + d * y) :=
        mul_le_mul hs ht (abs_nonneg _) (by nlinarith)
    _ ≤ a * c * (1 - y) + b * d * y := by
        nlinarith [mul_nonneg (mul_nonneg hy0 (by linarith : (0 : K) ≤ 1 - y))
          (mul_nonneg (by linarith : (0 : K) ≤ b - a) (by linarith : (0 : K) ≤ d - c))]

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-! ### The envelope induction -/

section Main

variable {η : ℕ → K} {d : K → ℕ → K}

/-- The joint induction behind the envelope bounds. -/
private theorem envelope_aux (hη1 : ∀ e, η (e + 1) ≤ 1 / 4)
    (h0 : ∀ x, d x 0 = 1) (h1 : ∀ x, d x 1 = x)
    (hrec : ∀ x n, d x (n + 2) = x * d x (n + 1) - η (n + 1) * d x n) (N : ℕ) :
    0 ≤ d 1 N ∧
    (∀ m, N = 2 * m + 1 → ∀ x : K, |x| ≤ 1 → |d x N| ≤ d 1 N * |x|) ∧
    (∀ m, N = 2 * m → envConst η m ≤ d 1 N ∧
      ∀ x : K, |x| ≤ 1 → |d x N| ≤ envConst η m * (1 - x ^ 2) + d 1 N * x ^ 2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have dec := fun x ↦ eq_chebHat_add_sum (h0 x) (h1 x) (hrec x) N
  have hδ : ∀ e, 0 ≤ 1 / 4 - η (e + 1) := fun e ↦ by linarith [hη1 e]
  -- consequences of the induction hypothesis
  have hpos : ∀ i < N, 0 ≤ d 1 i := fun i hi ↦ (ih i hi).1
  have hodd : ∀ j, 2 * j + 1 < N → ∀ x : K, |x| ≤ 1 → |d x (2 * j + 1)| ≤ d 1 (2 * j + 1) * |x| :=
    fun j hj ↦ (ih _ hj).2.1 j rfl
  have heven : ∀ j, 2 * j < N → envConst η j ≤ d 1 (2 * j) ∧ ∀ x : K, |x| ≤ 1 →
      |d x (2 * j)| ≤ envConst η j * (1 - x ^ 2) + d 1 (2 * j) * x ^ 2 :=
    fun j hj ↦ (ih _ hj).2.2 j rfl
  have hunif : ∀ i < N, ∀ x : K, |x| ≤ 1 → |d x i| ≤ d 1 i := by
    intro i hi x hx
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
    rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
    · obtain ⟨hB, hb⟩ := heven j hi
      have := hb x hx
      nlinarith [sq_nonneg x]
    · have := hodd j hi x hx
      nlinarith [hpos _ hi, abs_nonneg x]
  refine ⟨?_, ?_, ?_⟩
  · -- nonnegativity at `1`
    rw [dec 1]
    exact add_nonneg (chebHat_one_pos N).le (sum_nonneg fun i hi ↦
      mul_nonneg (mul_nonneg (hδ i) (chebShift_one_nonneg _)) (hpos i (mem_range.mp hi)))
  · -- odd indices
    rintro m rfl x hx
    have e2 : ∀ j < m, 2 * m + 1 - 1 - 2 * j = 2 * (m - j) := fun j hj ↦ by lia
    have e3 : ∀ j < m, 2 * m + 1 - 1 - (2 * j + 1) = 2 * (m - 1 - j) + 1 := fun j hj ↦ by lia
    have hsplit : ∀ z : K, ∑ i ∈ range (2 * m + 1),
        (1 / 4 - η (i + 1)) * chebShift (2 * m + 1 - 1 - i) z * d z i =
        ∑ j ∈ range m, ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - j)) z * d z (2 * j) +
          (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j) + 1) z *
            d z (2 * j + 1)) := by
      intro z
      rw [sum_range_succ, show 2 * m + 1 - 1 - 2 * m = 0 by lia, chebShift_zero, mul_zero,
        zero_mul, add_zero, sum_range_two_mul]
      exact sum_congr rfl fun j hj ↦ by
        rw [e2 j (mem_range.mp hj), e3 j (mem_range.mp hj)]
    rw [dec x, dec 1, hsplit, hsplit]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
    calc |chebHat (2 * m + 1) x + ∑ j ∈ range m,
          ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - j)) x * d x (2 * j) +
            (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j) + 1) x * d x (2 * j + 1))|
        ≤ |chebHat (2 * m + 1) x| + ∑ j ∈ range m,
          (|(1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - j)) x * d x (2 * j)| +
            |(1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j) + 1) x *
              d x (2 * j + 1)|) :=
          (abs_add_le _ _).trans (add_le_add_right ((abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun j _ ↦ abs_add_le _ _)) _)
      _ ≤ chebHat (2 * m + 1) 1 * |x| + ∑ j ∈ range m,
          ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - j)) 1 * d 1 (2 * j) * |x| +
            (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j) + 1) 1 *
              d 1 (2 * j + 1) * |x|) := by
          gcongr with j hj
          · exact abs_chebHat_odd_le m hx
          · have hj' := mem_range.mp hj
            rw [abs_mul, abs_mul, abs_of_nonneg (hδ _)]
            have hw := abs_chebShift_even_le (m - j) hx
            have hd := hunif (2 * j) (by lia) x hx
            have := mul_le_mul hw hd (abs_nonneg _)
              (mul_nonneg (chebShift_one_nonneg _) (abs_nonneg x))
            nlinarith [hδ (2 * j), abs_nonneg x, chebShift_one_nonneg (K := K) (2 * (m - j))]
          · have hj' := mem_range.mp hj
            rw [abs_mul, abs_mul, abs_of_nonneg (hδ _)]
            have hw := abs_chebShift_odd_le (m - 1 - j) hx
            have hq : (1 / 4 : K) ^ (m - 1 - j) ≤ chebShift (2 * (m - 1 - j) + 1) 1 := by
              rw [chebShift_succ]; exact quarter_pow_le_chebHat_even _
            have hw' : |chebShift (2 * (m - 1 - j) + 1) x| ≤
                chebShift (2 * (m - 1 - j) + 1) 1 := by nlinarith [sq_nonneg x]
            have hd := hodd j (by lia) x hx
            have := mul_le_mul hw' hd (abs_nonneg _) (chebShift_one_nonneg _)
            nlinarith [hδ (2 * j + 1)]
      _ = (chebHat (2 * m + 1) 1 + ∑ j ∈ range m,
          ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - j)) 1 * d 1 (2 * j) +
            (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j) + 1) 1 *
              d 1 (2 * j + 1))) * |x| := by
          rw [add_mul, sum_mul]
          congr 1
          exact sum_congr rfl fun j _ ↦ by ring
  · -- even indices
    rintro m rfl
    have e2 : ∀ j < m, 2 * m - 1 - 2 * j = 2 * (m - 1 - j) + 1 := fun j hj ↦ by lia
    have e3 : ∀ j < m, 2 * m - 1 - (2 * j + 1) = 2 * (m - 1 - j) := fun j hj ↦ by lia
    have hsplit : ∀ z : K, ∑ i ∈ range (2 * m),
        (1 / 4 - η (i + 1)) * chebShift (2 * m - 1 - i) z * d z i =
        ∑ j ∈ range m, ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - 1 - j) + 1) z * d z (2 * j) +
          (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) z * d z (2 * j + 1)) := by
      intro z
      rw [sum_range_two_mul]
      exact sum_congr rfl fun j hj ↦ by
        rw [e2 j (mem_range.mp hj), e3 j (mem_range.mp hj)]
    have hq : ∀ j, (1 / 4 : K) ^ (m - 1 - j) ≤ chebShift (2 * (m - 1 - j) + 1) 1 := fun j ↦ by
      rw [chebShift_succ]; exact quarter_pow_le_chebHat_even _
    constructor
    · rw [dec 1, hsplit, envConst_eq_sum]
      gcongr with j hj
      · exact quarter_pow_le_chebHat_even m
      · have hj' := mem_range.mp hj
        have hB := (heven j (by lia)).1
        have := mul_le_mul (hq j) hB (envConst_nonneg hη1 j) (chebShift_one_nonneg _)
        have hp := mul_nonneg (mul_nonneg (hδ (2 * j + 1)) (chebShift_one_nonneg (K := K)
          (2 * (m - 1 - j)))) (hpos (2 * j + 1) (by lia))
        nlinarith [hδ (2 * j)]
    · intro x hx
      have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
      have hy1 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
      rw [dec x, dec 1, hsplit, hsplit, envConst_eq_sum]
      calc |chebHat (2 * m) x + ∑ j ∈ range m,
            ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - 1 - j) + 1) x * d x (2 * j) +
              (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) x * d x (2 * j + 1))|
          ≤ |chebHat (2 * m) x| + ∑ j ∈ range m,
            (|(1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - 1 - j) + 1) x * d x (2 * j)| +
              |(1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) x *
                d x (2 * j + 1)|) :=
            (abs_add_le _ _).trans (add_le_add_right ((abs_sum_le_sum_abs _ _).trans
              (sum_le_sum fun j _ ↦ abs_add_le _ _)) _)
        _ ≤ ((1 / 4) ^ m * (1 - x ^ 2) + chebHat (2 * m) 1 * x ^ 2) + ∑ j ∈ range m,
            ((1 / 4 - η (2 * j + 1)) * ((1 / 4) ^ (m - 1 - j) * envConst η j * (1 - x ^ 2) +
                chebShift (2 * (m - 1 - j) + 1) 1 * d 1 (2 * j) * x ^ 2) +
              (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) 1 *
                d 1 (2 * j + 1) * x ^ 2) := by
            gcongr with j hj
            · exact abs_chebHat_even_le m hx
            · have hj' := mem_range.mp hj
              rw [mul_assoc, abs_mul, abs_of_nonneg (hδ _)]
              obtain ⟨hB, hb⟩ := heven j (by lia)
              exact mul_le_mul_of_nonneg_left (abs_mul_le_chord (by positivity) (hq j) hB hy0 hy1
                (abs_chebShift_odd_le _ hx) (hb x hx)) (hδ _)
            · have hj' := mem_range.mp hj
              rw [abs_mul, abs_mul, abs_of_nonneg (hδ _)]
              have hw := abs_chebShift_even_le (m - 1 - j) hx
              have hd := hodd j (by lia) x hx
              have := mul_le_mul hw hd (abs_nonneg _)
                (mul_nonneg (chebShift_one_nonneg _) (abs_nonneg x))
              have hxx : |x| * |x| = x ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
              calc (1 / 4 - η (2 * j + 1 + 1)) * |chebShift (2 * (m - 1 - j)) x| *
                    |d x (2 * j + 1)|
                  = (1 / 4 - η (2 * j + 1 + 1)) *
                      (|chebShift (2 * (m - 1 - j)) x| * |d x (2 * j + 1)|) := by ring
                _ ≤ (1 / 4 - η (2 * j + 1 + 1)) * (chebShift (2 * (m - 1 - j)) 1 * |x| *
                      (d 1 (2 * j + 1) * |x|)) := mul_le_mul_of_nonneg_left this (hδ _)
                _ = _ := by rw [← hxx]; ring
        _ = ((1 / 4) ^ m + ∑ j ∈ range m,
              (1 / 4 - η (2 * j + 1)) * (1 / 4) ^ (m - 1 - j) * envConst η j) * (1 - x ^ 2) +
            (chebHat (2 * m) 1 + ∑ j ∈ range m,
              ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - 1 - j) + 1) 1 * d 1 (2 * j) +
                (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) 1 *
                  d 1 (2 * j + 1))) * x ^ 2 := by
            rw [add_mul, add_mul, sum_mul, sum_mul]
            rw [sum_congr rfl fun j _ ↦ (show
              (1 / 4 - η (2 * j + 1)) * ((1 / 4) ^ (m - 1 - j) * envConst η j * (1 - x ^ 2) +
                  chebShift (2 * (m - 1 - j) + 1) 1 * d 1 (2 * j) * x ^ 2) +
                (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) 1 *
                  d 1 (2 * j + 1) * x ^ 2 =
              (1 / 4 - η (2 * j + 1)) * (1 / 4) ^ (m - 1 - j) * envConst η j * (1 - x ^ 2) +
                ((1 / 4 - η (2 * j + 1)) * chebShift (2 * (m - 1 - j) + 1) 1 * d 1 (2 * j) +
                  (1 / 4 - η (2 * j + 1 + 1)) * chebShift (2 * (m - 1 - j)) 1 *
                    d 1 (2 * j + 1)) * x ^ 2 by ring), sum_add_distrib]
            ring

variable (hη1 : ∀ e, η (e + 1) ≤ 1 / 4) (h0 : ∀ x, d x 0 = 1) (h1 : ∀ x, d x 1 = x)
  (hrec : ∀ x n, d x (n + 2) = x * d x (n + 1) - η (n + 1) * d x n)
include hη1 h0 h1 hrec

theorem nonneg_one (n : ℕ) : 0 ≤ d 1 n := (envelope_aux hη1 h0 h1 hrec n).1

/-- The odd envelope: `|D_(2m+1)(x)| ≤ D_(2m+1)(1) |x|` for `|x| ≤ 1`. -/
theorem abs_le_of_odd (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |d x (2 * m + 1)| ≤ d 1 (2 * m + 1) * |x| :=
  (envelope_aux hη1 h0 h1 hrec _).2.1 m rfl x hx

/-- The even envelope: `|D_(2m)(x)| ≤ B_m (1 - x²) + D_(2m)(1) x²` for `|x| ≤ 1`. -/
theorem abs_le_of_even (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |d x (2 * m)| ≤ envConst η m * (1 - x ^ 2) + d 1 (2 * m) * x ^ 2 :=
  ((envelope_aux hη1 h0 h1 hrec _).2.2 m rfl).2 x hx

theorem envConst_le_eval_one (m : ℕ) : envConst η m ≤ d 1 (2 * m) :=
  ((envelope_aux hη1 h0 h1 hrec _).2.2 m rfl).1

end Main

end RealRooted.PathEnvelope

namespace RealRooted.SatisfiesFavardRecurrence

open RealRooted.PathEnvelope

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : ℕ → K[X]} {η : ℕ → K}

/-- For a Favard family with zero diagonal and `η_e ≤ 1/4`, the even members satisfy the
envelope `|P_(2m)(x)| ≤ B_m (1 - x²) + P_(2m)(1) x²` on `[-1, 1]`, with
`B_m = ∏_(i < m) (1/2 - η_(2i+1))`. -/
theorem abs_eval_le_envelope (hrec : SatisfiesFavardRecurrence P (fun _ ↦ 0) η)
    (hη : ∀ e, η (e + 1) ≤ 1 / 4) (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |(P (2 * m)).eval x| ≤ envConst η m * (1 - x ^ 2) + (P (2 * m)).eval 1 * x ^ 2 :=
  abs_le_of_even (d := fun x n ↦ (P n).eval x) hη (fun x ↦ by simp [hrec.1])
    (fun x ↦ by simp [hrec.2.1]) (fun x n ↦ by simp [hrec.2.2 n]) m hx

/-- The odd members satisfy `|P_(2m+1)(x)| ≤ P_(2m+1)(1) |x|` on `[-1, 1]`. -/
theorem abs_eval_le_of_odd (hrec : SatisfiesFavardRecurrence P (fun _ ↦ 0) η)
    (hη : ∀ e, η (e + 1) ≤ 1 / 4) (m : ℕ) {x : K} (hx : |x| ≤ 1) :
    |(P (2 * m + 1)).eval x| ≤ (P (2 * m + 1)).eval 1 * |x| :=
  abs_le_of_odd (d := fun x n ↦ (P n).eval x) hη (fun x ↦ by simp [hrec.1])
    (fun x ↦ by simp [hrec.2.1]) (fun x n ↦ by simp [hrec.2.2 n]) m hx

end RealRooted.SatisfiesFavardRecurrence
