import RealRooted.CombinatorialExamples.BigDescents321.Neighbor

/-!
# The residual polynomial `R_n`

With `k = n - 2` and `α_n = (2n - 1)/(n(n² - 1))` there is a unique `β_n` for which

`R_n = ((α_n c² + β_n) G_k - Q_n) / c`

is a polynomial of degree at most `k - 1` whose `G_0`-coordinate vanishes (issue #1143, §8).
We define its Gegenbauer coordinates `b` directly by the upward recurrence that
`c R_n = (α_n c² + β_n) G_k - Q_n` forces on them, and choose `β_n` so that the recurrence
stops at degree `k - 1`.

## Main statements

* `X_mul_residual`: `c R_n = (α_n c² + β_n) G_k - Q_n`.
* `residCoord_eq_altSum`: below the top, `b_(j+1) = -(2j + 5)/((j + 3) w_j) S_j`, where
  `S_j = w_j q_(n,j) - w_(j-2) q_(n,j-2) + ⋯` is an alternating sum of rescaled coordinates.
-/

open Polynomial

namespace RealRooted.BigDescents321

/-- `α_n = (2n - 1)/(n(n² - 1))`. -/
def alphaN (n : ℕ) : ℚ := (2 * n - 1) / (n * ((n : ℚ) ^ 2 - 1))

/-- The Gegenbauer coordinates of `c² G_k`. -/
def sqShift (k : ℕ) : ℕ → ℚ := xShift (xShift fun i ↦ if i = k then 1 else 0)

/-- The coordinates of `α_n c² G_(n-2) - Q_n`. -/
noncomputable def topCoord (n i : ℕ) : ℚ := alphaN n * sqShift (n - 2) i - transformedCoord n i

/-- The upward recurrence for the coordinates of `R_n`, from `b_0 = 0`. -/
noncomputable def residRaw (n : ℕ) : ℕ → ℚ
  | 0 => 0
  | 1 => 5 / 3 * topCoord n 0
  | i + 2 => (topCoord n (i + 1) - residRaw n i * (i + 1) / (2 * i + 3)) * (2 * i + 7) / (i + 4)

/-- The Gegenbauer coordinates of `R_n`. -/
noncomputable def residCoord (n i : ℕ) : ℚ := if i + 3 ≤ n then residRaw n i else 0

/-- `β_n`, chosen so that the coordinates of `R_n` stop at degree `n - 3`. -/
noncomputable def betaN (n : ℕ) : ℚ :=
  residRaw n (n - 3) * ((n : ℚ) - 2) / (2 * n - 3) - topCoord n (n - 2)

/-- The residual polynomial `R_n`. -/
noncomputable def residual (n : ℕ) : ℚ[X] := gsum (residCoord n) (n - 3)

/-! ### Coordinates of `c² G_k` -/

theorem xShift_single (k : ℕ) (a : ℚ) (i : ℕ) :
    xShift (fun j ↦ if j = k then a else 0) i =
      (if i = k + 1 then a * (k + 1) / (2 * k + 3) else 0) +
        (if i + 1 = k then a * (i + 3) / (2 * i + 5) else 0) := by
  unfold xShift
  rcases i with _ | i
  · simp only [↓reduceIte, zero_add]
    split_ifs <;> simp_all
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs <;> subst_vars <;> push_cast <;> ring_nf

theorem sqShift_eq_zero {k i : ℕ} (h1 : i ≠ k + 2) (h2 : i ≠ k) (h3 : i + 2 ≠ k) :
    sqShift k i = 0 := by
  rw [sqShift, xShift, xShift_single, xShift_single]
  split_ifs <;> first | lia | simp

theorem sqShift_top (k : ℕ) :
    sqShift k (k + 2) = (k + 1) * (k + 2) / ((2 * k + 3) * (2 * k + 5)) := by
  rw [sqShift, xShift, xShift_single, xShift_single]
  split_ifs <;> first | lia | (push_cast; field_simp; ring)

/-! ### Parity -/

theorem transformedCoord_of_odd_add {n j : ℕ} (h : (n + j) % 2 = 1) : transformedCoord n j = 0 := by
  unfold transformedCoord
  split_ifs with h'
  · obtain ⟨hj, he⟩ := h'
    rw [Nat.even_iff] at he
    lia
  · rfl

theorem sqShift_of_odd_add {k i : ℕ} (h : (k + i) % 2 = 1) : sqShift k i = 0 :=
  sqShift_eq_zero (by lia) (by lia) (by lia)

theorem topCoord_of_odd_add {n i : ℕ} (hn : 2 ≤ n) (h : (n + i) % 2 = 1) : topCoord n i = 0 := by
  rw [topCoord, sqShift_of_odd_add (by lia), transformedCoord_of_odd_add h, mul_zero, sub_zero]

theorem residRaw_of_even_add {n : ℕ} (hn : 2 ≤ n) : ∀ i, (n + i) % 2 = 0 → residRaw n i = 0
  | 0, _ => rfl
  | 1, h => by rw [residRaw, topCoord_of_odd_add hn (by lia), mul_zero]
  | i + 2, h => by
    rw [residRaw, residRaw_of_even_add hn i (by lia), topCoord_of_odd_add hn (by lia)]
    ring

/-! ### The recurrence -/

theorem residCoord_of_le {n i : ℕ} (h : i + 3 ≤ n) : residCoord n i = residRaw n i := by
  simp only [residCoord, h, ↓reduceIte]

theorem residCoord_of_lt {n i : ℕ} (h : n < i + 3) : residCoord n i = 0 := by
  simp only [residCoord, show ¬ (i + 3 ≤ n) by lia, ↓reduceIte]

/-- The coordinates `residRaw n` solve `c R = α_n c² G_k - Q_n` in every degree. -/
theorem xShift_residRaw (n i : ℕ) : xShift (residRaw n) i = topCoord n i := by
  rcases i with _ | i
  · simp only [xShift, ↓reduceIte, zero_add, residRaw]
    push_cast
    ring
  · simp only [xShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      residRaw]
    push_cast
    field_simp
    ring

theorem transformedCoord_self (n : ℕ) : transformedCoord n n = 1 / ((2 * n + 1) * (n + 1)) := by
  rw [transformedCoord_eq (r := 0) (by ring), kernelCoord_eq, corrCoordZ, kernelMoment_zero,
    kernelMoment_of_neg (by norm_num)]
  simp only [lt_self_iff_false, ↓reduceIte, Int.toNat_zero, corrCoord]
  field_simp
  ring

/-- `c R_n = (α_n c² + β_n) G_(n-2) - Q_n`. -/
theorem X_mul_residual {k : ℕ} (hk : 2 ≤ k) :
    X * residual (k + 2) =
      (C (alphaN (k + 2)) * X ^ 2 + C (betaN (k + 2))) * gegen k - transformed (k + 2) := by
  have hr : ∀ j, k - 1 < j → residCoord (k + 2) j = 0 := fun j hj ↦ by
    simp only [residCoord, show ¬ (j + 3 ≤ k + 2) by lia, ↓reduceIte]
  have hsingle : ∀ j, k < j → (fun i ↦ if i = k then (1 : ℚ) else 0) j = 0 := fun j hj ↦ by
    simp only [show j ≠ k by lia, ↓reduceIte]
  have hXG : X * gegen k = gsum (xShift fun i ↦ if i = k then (1 : ℚ) else 0) (k + 1) := by
    rw [← X_mul_gsum hsingle, gsum_single k k le_rfl, map_one, one_mul]
  have hXXG : X ^ 2 * gegen k = gsum (sqShift k) (k + 2) := by
    rw [pow_two, mul_assoc, hXG, sqShift, X_mul_gsum]
    intro j hj
    rw [xShift_single]
    simp only [show j ≠ k + 1 by lia, show j + 1 ≠ k by lia, ↓reduceIte, add_zero]
  have hxr : ∀ j, k < j → xShift (residCoord (k + 2)) j = 0 := fun j hj ↦ by
    simp only [xShift, hr (j + 1) (by lia), zero_mul, zero_div, add_zero,
      hr (j - 1) (by lia), ite_self]
  rw [residual, show k + 2 - 3 = k - 1 by lia, X_mul_gsum hr, show k - 1 + 1 = k by lia,
    ← gsum_eq_of_le hxr (show k ≤ k + 2 by lia), transformed_eq_gsum, add_mul, mul_assoc, hXXG,
    ← gsum_single (k + 2) k (by lia), ← gsum_smul, ← gsum_add]
  rw [show gsum (xShift (residCoord (k + 2))) (k + 2) =
      gsum (alphaN (k + 2) • sqShift k + fun i ↦ if i = k then betaN (k + 2) else 0) (k + 2) -
        gsum (transformedCoord (k + 2)) (k + 2) from ?_]
  rw [eq_sub_iff_add_eq, ← gsum_add]
  refine gsum_congr fun i hi ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hk2 : 2 ≤ k + 2 := by lia
  rcases (show i + 2 ≤ k ∨ i = k - 1 ∨ i = k ∨ i = k + 1 ∨ i = k + 2 by lia) with h | h | h | h | h
  · have e : xShift (residCoord (k + 2)) i = xShift (residRaw (k + 2)) i := by
      simp only [xShift, residCoord_of_le (show i + 1 + 3 ≤ k + 2 by lia),
        residCoord_of_le (show i - 1 + 3 ≤ k + 2 by lia)]
    rw [e, xShift_residRaw, topCoord, show k + 2 - 2 = k by lia]
    simp only [show i ≠ k by lia, ↓reduceIte]
    ring
  · subst h
    simp only [xShift, show k - 1 ≠ 0 by lia, ↓reduceIte, show k - 1 - 1 = k - 2 by lia,
      show k - 1 + 1 = k by lia, residCoord_of_lt (show k + 2 < k + 3 by lia),
      residCoord_of_le (show k - 2 + 3 ≤ k + 2 by lia),
      residRaw_of_even_add hk2 (k - 2) (by lia),
      transformedCoord_of_odd_add (show (k + 2 + (k - 1)) % 2 = 1 by lia),
      sqShift_of_odd_add (show (k + (k - 1)) % 2 = 1 by lia), show k - 1 ≠ k by lia]
    ring
  · subst i
    simp only [xShift, show k ≠ 0 by lia, ↓reduceIte,
      residCoord_of_lt (show k + 2 < k + 1 + 3 by lia),
      residCoord_of_le (show k - 1 + 3 ≤ k + 2 by lia), betaN, topCoord,
      show k + 2 - 3 = k - 1 by lia, show k + 2 - 2 = k by lia]
    have : 2 * ((k : ℚ) + 2) - 3 ≠ 0 := by have := (k.cast_nonneg : (0 : ℚ) ≤ k); intro h; linarith
    push_cast
    field_simp
    ring
  · subst h
    simp only [xShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      residCoord_of_lt (show k + 2 < k + 3 by lia),
      residCoord_of_lt (show k + 2 < k + 1 + 1 + 3 by lia),
      transformedCoord_of_odd_add (show (k + 2 + (k + 1)) % 2 = 1 by lia),
      sqShift_of_odd_add (show (k + (k + 1)) % 2 = 1 by lia), show k + 1 ≠ k by lia]
    ring
  · subst h
    simp only [xShift, show k + 2 ≠ 0 by lia, ↓reduceIte, show k + 2 - 1 = k + 1 by lia,
      residCoord_of_lt (show k + 2 < k + 1 + 3 by lia),
      residCoord_of_lt (show k + 2 < k + 2 + 1 + 3 by lia), transformedCoord_self, sqShift_top,
      show k + 2 ≠ k by lia, alphaN]
    have : ((k : ℚ) + 2) ^ 2 - 1 ≠ 0 := by have := (k.cast_nonneg : (0 : ℚ) ≤ k); nlinarith
    push_cast
    field_simp
    ring

/-! ### The tail -/

/-- The weights `w_0 = 1`, `w_1 = 2`, `w_(j+2) = (j + 3)/(j + 2) w_j`. -/
def weightW : ℕ → ℚ
  | 0 => 1
  | 1 => 2
  | j + 2 => (j + 3) / (j + 2) * weightW j

theorem weightW_pos : ∀ j, 0 < weightW j
  | 0 => by norm_num [weightW]
  | 1 => by norm_num [weightW]
  | j + 2 => by
    rw [weightW]
    have := weightW_pos j
    positivity

/-- The alternating sums `S_j = w_j q_(n,j) - w_(j-2) q_(n,j-2) + ⋯`. -/
noncomputable def altSum (n : ℕ) : ℕ → ℚ
  | 0 => transformedCoord n 0
  | 1 => 2 * transformedCoord n 1
  | j + 2 => weightW (j + 2) * transformedCoord n (j + 2) - altSum n j

theorem topCoord_of_lt {n i : ℕ} (h : i + 4 < n) : topCoord n i = -transformedCoord n i := by
  rw [topCoord, sqShift_eq_zero (by lia) (by lia) (by lia)]
  ring

/-- Identity (A): below the top, `b_(j+1) = -(2j + 5)/((j + 3) w_j) S_j`. -/
theorem residRaw_succ_eq {n : ℕ} :
    ∀ j, j + 6 ≤ n → residRaw n (j + 1) = -(2 * j + 5) / ((j + 3) * weightW j) * altSum n j
  | 0, h => by
    simp only [residRaw, topCoord_of_lt (show 0 + 4 < n by lia), altSum, weightW]
    push_cast
    ring
  | 1, h => by
    simp only [residRaw, topCoord_of_lt (show 1 + 4 < n by lia), altSum, weightW]
    push_cast
    ring
  | j + 2, h => by
    have ih := residRaw_succ_eq (n := n) j (by lia)
    rw [show j + 2 + 1 = (j + 1) + 2 from rfl, residRaw, ih,
      topCoord_of_lt (n := n) (i := j + 1 + 1) (by lia), altSum, weightW]
    have := weightW_pos j
    push_cast
    field_simp
    ring

/-- The neighbour inequality in rescaled form: `w_j q_(n,j) < w_(j+2) q_(n,j+2)`. -/
theorem weightW_mul_lt {n j : ℕ} (h : j + 14 ≤ n) (hp : j % 2 = n % 2) :
    weightW j * transformedCoord n j < weightW (j + 2) * transformedCoord n (j + 2) := by
  obtain ⟨r, hr⟩ : ∃ r, n = j + 2 + 2 * r := ⟨(n - j - 2) / 2, by lia⟩
  have hpos := kernelCoord_neighbor_pos (r := r) (J := j + 2) (by lia) (by lia)
  rw [← transformedCoord_eq (n := n) (by push_cast; lia),
    ← transformedCoord_eq (n := n) (j := j + 2 - 2) (by push_cast; lia),
    Nat.add_sub_cancel] at hpos
  have hw := weightW_pos j
  rw [weightW]
  push_cast at hpos ⊢
  have key : (j + 3 : ℚ) / (j + 2) * weightW j * transformedCoord n (j + 2) -
      weightW j * transformedCoord n j = weightW j / (j + 2) *
        ((j + 2 + 1) * transformedCoord n (j + 2) - (j + 2) * transformedCoord n j) := by
    field_simp
    ring
  have : 0 < weightW j / (j + 2) *
      ((j + 2 + 1) * transformedCoord n (j + 2) - (j + 2) * transformedCoord n j) := by
    positivity
  linarith

/-- `0 < S_j ≤ w_j q_(n,j)` along the parity of `n`, up to `n - 12`, given the bottom sign. -/
theorem altSum_pos {n : ℕ} (hbot : 0 < transformedCoord n (n % 2)) :
    ∀ j, j + 12 ≤ n → j % 2 = n % 2 →
      0 < altSum n j ∧ altSum n j ≤ weightW j * transformedCoord n j
  | 0, _, hp => by
    rw [← hp] at hbot
    simp only [altSum, weightW, one_mul, le_refl, and_true]
    exact hbot
  | 1, _, hp => by
    rw [← hp] at hbot
    simp only [altSum, weightW, le_refl, and_true]
    linarith
  | j + 2, h, hp => by
    obtain ⟨ih1, ih2⟩ := altSum_pos hbot j (by lia) (by lia)
    have hlt := weightW_mul_lt (n := n) (j := j) (by lia) (by lia)
    rw [altSum]
    constructor <;> linarith

/-- The tail signs: `b_(n, j+1) < 0` for `j ≤ n - 12` of the parity of `n`. -/
theorem residCoord_neg {n j : ℕ} (hbot : 0 < transformedCoord n (n % 2)) (h : j + 12 ≤ n)
    (hp : j % 2 = n % 2) : residCoord n (j + 1) < 0 := by
  rw [residCoord_of_le (by lia), residRaw_succ_eq j (by lia)]
  have hS := (altSum_pos hbot j h hp).1
  have hw := weightW_pos j
  have : 0 < (2 * (j : ℚ) + 5) / ((j + 3) * weightW j) * altSum n j := by positivity
  rw [neg_div, neg_mul]
  linarith

end RealRooted.BigDescents321
