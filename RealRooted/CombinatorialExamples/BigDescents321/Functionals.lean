import RealRooted.CombinatorialExamples.BigDescents321.Residual
import Mathlib.Algebra.BigOperators.Field

/-!
# Linear functionals on Gegenbauer coordinates

Two linear functionals on the Gegenbauer coordinates turn the coordinate recurrence (1.9) of
`Q_n` into scalar recurrences driven by the bottom coordinate `q_(n,0)`:

* the plain sum `σ(φ) = ∑_j φ_j`, with `σ(c φ) = σ(φ) - (2/3) φ_0`;
* the weighted sum `ψ(φ) = ∑_j ψ_j φ_j` with `ψ_1 = 4`, `ψ_(j+2) = -(j + 3)/(j + 2) ψ_j` on odd
  `j` and `ψ_j = 0` on even `j`, so that `ψ(c φ) = (4/3) φ_0`. On odd polynomials it is
  `p ↦ Λ((1 - c²) p / c)`.

Here `c φ` denotes the coordinates `xShift φ` of `c · ∑_j φ_j G_j`.
-/

open Finset

namespace RealRooted.BigDescents321

/-- The sum `∑_(j ≤ N) φ_j` of the Gegenbauer coordinates. -/
def coordSum (φ : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ range (N + 1), φ i

/-- The weights `ψ_j` of the functional `p ↦ Λ((1 - c²) p / c)` on odd polynomials. -/
def psiW : ℕ → ℚ
  | 0 => 0
  | 1 => 4
  | j + 2 => -((j : ℚ) + 3) / (j + 2) * psiW j

/-- The weighted sum `∑_(j ≤ N) ψ_j φ_j`. -/
def psiSum (φ : ℕ → ℚ) (N : ℕ) : ℚ := ∑ i ∈ range (N + 1), φ i * psiW i

theorem coordSum_eq_of_le {φ : ℕ → ℚ} {N : ℕ} (hφ : ∀ j, N < j → φ j = 0) {M : ℕ}
    (h : N ≤ M) : coordSum φ M = coordSum φ N := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hNM ih => rw [coordSum, sum_range_succ, ← coordSum, ih, hφ _ (by lia), add_zero]

theorem psiSum_eq_of_le {φ : ℕ → ℚ} {N : ℕ} (hφ : ∀ j, N < j → φ j = 0) {M : ℕ}
    (h : N ≤ M) : psiSum φ M = psiSum φ N := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hNM ih => rw [psiSum, sum_range_succ, ← psiSum, ih, hφ _ (by lia), zero_mul, add_zero]

/-- `∑_(i ≤ N) (c φ)_i w_i` split into the two neighbours of each coordinate of `φ`. -/
theorem sum_xShift_mul (φ w : ℕ → ℚ) (N : ℕ) :
    ∑ i ∈ range (N + 1), xShift φ i * w i =
      ∑ j ∈ range N, φ j * (((j : ℚ) + 1) / (2 * j + 3)) * w (j + 1) +
        ∑ j ∈ range (N + 1), φ (j + 1) * (((j : ℚ) + 3) / (2 * j + 5)) * w j := by
  induction N with
  | zero =>
    simp only [zero_add, sum_range_one, sum_range_zero, xShift, ↓reduceIte, Nat.cast_zero]
    ring
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j ↦ φ j * _ * w (j + 1)) N,
      sum_range_succ (fun j ↦ φ (j + 1) * _ * w j) (N + 1)]
    simp only [xShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    push_cast
    ring

/-- `σ(c φ) = σ(φ) - (2/3) φ_0`. -/
theorem coordSum_xShift {φ : ℕ → ℚ} {N : ℕ} (hφ : ∀ j, N < j → φ j = 0) :
    coordSum (xShift φ) (N + 1) = coordSum φ N - 2 / 3 * φ 0 := by
  have h := sum_xShift_mul φ (fun _ ↦ 1) (N + 1)
  simp only [mul_one] at h
  rw [coordSum, h, sum_range_succ (fun j ↦ φ (j + 1) * _) (N + 1), hφ (N + 1 + 1) (by lia),
    zero_mul, add_zero]
  have hg := sum_range_succ' (fun j ↦ φ j * (((j : ℚ) + 2) / (2 * j + 3))) (N + 1)
  rw [sum_range_succ, hφ (N + 1) (by lia), zero_mul, add_zero] at hg
  have e : ∀ j ∈ range (N + 1), φ (j + 1) * (((j : ℚ) + 3) / (2 * j + 5)) =
      φ (j + 1) * ((((j + 1 : ℕ) : ℚ) + 2) / (2 * ((j + 1 : ℕ) : ℚ) + 3)) := fun j _ ↦ by
    push_cast; ring_nf
  rw [sum_congr rfl e, coordSum]
  have hs : ∀ j ∈ range (N + 1), φ j * (((j : ℚ) + 1) / (2 * j + 3)) +
      φ j * (((j : ℚ) + 2) / (2 * j + 3)) = φ j := fun j _ ↦ by
    have : (2 * (j : ℚ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  rw [← sum_congr rfl hs, sum_add_distrib]
  simp only [Nat.cast_zero] at hg
  linarith

/-- `(j + 2) ψ_(j+2) + (j + 3) ψ_j = 0`. -/
theorem psiW_rec (j : ℕ) : ((j : ℚ) + 2) * psiW (j + 2) + (j + 3) * psiW j = 0 := by
  rw [psiW]
  have : (j : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `ψ(c φ) = (4/3) φ_0`. -/
theorem psiSum_xShift {φ : ℕ → ℚ} {N : ℕ} (hφ : ∀ j, N < j → φ j = 0) :
    psiSum (xShift φ) (N + 1) = 4 / 3 * φ 0 := by
  rw [psiSum, sum_xShift_mul, sum_range_succ (fun j ↦ φ (j + 1) * _ * psiW j) (N + 1),
    sum_range_succ (fun j ↦ φ (j + 1) * _ * psiW j) N, hφ (N + 1 + 1) (by lia),
    hφ (N + 1) (by lia), sum_range_succ' (fun j ↦ φ j * _ * psiW (j + 1)) N]
  simp only [zero_mul, add_zero, Nat.cast_zero]
  have hz : ∀ j ∈ range N, φ (j + 1) * ((((j + 1 : ℕ) : ℚ) + 1) / (2 * ((j + 1 : ℕ) : ℚ) + 3)) *
      psiW (j + 1 + 1) + φ (j + 1) * (((j : ℚ) + 3) / (2 * j + 5)) * psiW j = 0 := fun j _ ↦ by
    have h := psiW_rec j
    have : (2 * (j : ℚ) + 5) ≠ 0 := by positivity
    rw [show j + 1 + 1 = j + 2 from rfl]
    push_cast
    field_simp
    linear_combination (2 * (j : ℚ) + 5) * φ (j + 1) * h
  have hsum := sum_add_distrib.symm.trans (sum_eq_zero hz)
  simp only [zero_add, show psiW 1 = 4 from rfl] at hsum ⊢
  linear_combination hsum

/-! ### Recurrences for `σ(q_n)` and `ψ(q_n)` -/

/-- `σ_n = ∑_j q_(n,j)`; `J*_n = 2 σ_n`. -/
noncomputable def sigmaQ (n : ℕ) : ℚ := coordSum (transformedCoord n) n

/-- `T_n = ∑_j ψ_j q_(n,j) = Λ((1 - c²) Q_n / c)` for odd `n`. -/
noncomputable def psiQ (n : ℕ) : ℚ := psiSum (transformedCoord n) n

/-- Weighted sums of the correction coordinates of (1.9). -/
theorem sum_extraCoord_mul (m : ℕ) (w : ℕ → ℚ) :
    ∑ i ∈ range (m + 4 + 1), extraCoord (m + 3) i * w i =
      extraCoord (m + 3) (m + 4) * w (m + 4) + extraCoord (m + 3) (m + 2) * w (m + 2) +
        extraCoord (m + 3) m * w m := by
  have hz : ∑ i ∈ range m, extraCoord (m + 3) i * w i = 0 := sum_eq_zero fun i hi ↦ by
    have := mem_range.mp hi
    simp only [extraCoord, show i ≠ m + 3 + 1 by lia, show i + 1 ≠ m + 3 by lia,
      show i + 3 ≠ m + 3 by lia, ↓reduceIte, zero_mul]
  rw [show m + 4 + 1 = m + 5 from rfl]
  simp only [sum_range_succ, hz]
  simp only [extraCoord, show m + 1 ≠ m + 3 + 1 by lia, show m + 1 + 1 ≠ m + 3 by lia,
    show m + 1 + 3 ≠ m + 3 by lia, show m + 3 ≠ m + 3 + 1 by lia,
    show m + 3 + 3 ≠ m + 3 by lia, ↓reduceIte]
  ring

private theorem extraCoord_values (m : ℕ) :
    extraCoord (m + 3) (m + 4) = 1 / ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) + 3)) ∧
    extraCoord (m + 3) (m + 2) = ((((m : ℚ) + 3 + 1) * ((m : ℚ) + 3 - 1)) /
        ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) - 1)) + ((m : ℚ) + 3) * ((m : ℚ) + 3 + 2) /
        ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) + 3)) - 1) /
        (((m : ℚ) + 3) * ((m : ℚ) + 3 + 1)) ∧
    extraCoord (m + 3) m = 1 / ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [extraCoord, show m + 4 = m + 3 + 1 from rfl, ↓reduceIte]
    push_cast
    ring
  · simp only [extraCoord, show m + 2 ≠ m + 3 + 1 by lia, show m + 2 + 1 = m + 3 from rfl,
      ↓reduceIte]
    push_cast
    ring
  · simp only [extraCoord, show m ≠ m + 3 + 1 by lia, show m + 1 ≠ m + 3 by lia, ↓reduceIte]
    push_cast
    ring

/-- `σ(q_(m+3)) - (2/3) q_(m+3,0) = σ(q_(m+2)) - σ(q_m)/8`. -/
theorem sigmaQ_rec (m : ℕ) :
    sigmaQ (m + 3) - 2 / 3 * transformedCoord (m + 3) 0 = sigmaQ (m + 2) - sigmaQ m / 8 := by
  have hv : ∀ n j, n < j → transformedCoord n j = 0 := fun n j h ↦ transformedCoord_of_lt h
  have hL : coordSum (xShift (transformedCoord (m + 3))) (m + 4) =
      coordSum (transformedCoord (m + 3)) (m + 3) - 2 / 3 * transformedCoord (m + 3) 0 :=
    coordSum_xShift (hv (m + 3))
  have hR : coordSum (xShift (transformedCoord (m + 3))) (m + 4) =
      coordSum (transformedCoord (m + 2)) (m + 4) - coordSum (transformedCoord m) (m + 4) / 8 +
        coordSum (extraCoord (m + 3)) (m + 4) := by
    simp only [coordSum, xShift_transformedCoord, sum_add_distrib, sum_sub_distrib, sum_div]
  have he := sum_extraCoord_mul m (fun _ ↦ 1)
  obtain ⟨e1, e2, e3⟩ := extraCoord_values m
  simp only [mul_one, e1, e2, e3] at he
  rw [coordSum_eq_of_le (hv (m + 2)) (by lia), coordSum_eq_of_le (hv m) (by lia),
    show coordSum (extraCoord (m + 3)) (m + 4) = _ from he] at hR
  have hm : (2 * ((m : ℚ) + 3) - 1) ≠ 0 := by
    have := (m.cast_nonneg : (0 : ℚ) ≤ m); intro h; linarith
  simp only [sigmaQ]
  rw [← hL, hR]
  field_simp
  ring

/-- `(4/3) q_(m+3,0) = ψ(q_(m+2)) - ψ(q_m)/8 - ψ_(m+2) / ((m + 3)(m + 4))`. -/
theorem psiQ_rec (m : ℕ) :
    4 / 3 * transformedCoord (m + 3) 0 =
      psiQ (m + 2) - psiQ m / 8 - psiW (m + 2) / (((m : ℚ) + 3) * (m + 4)) := by
  have hv : ∀ n j, n < j → transformedCoord n j = 0 := fun n j h ↦ transformedCoord_of_lt h
  have hL : psiSum (xShift (transformedCoord (m + 3))) (m + 4) =
      4 / 3 * transformedCoord (m + 3) 0 := psiSum_xShift (hv (m + 3))
  have hR : psiSum (xShift (transformedCoord (m + 3))) (m + 4) =
      psiSum (transformedCoord (m + 2)) (m + 4) - psiSum (transformedCoord m) (m + 4) / 8 +
        ∑ i ∈ range (m + 4 + 1), extraCoord (m + 3) i * psiW i := by
    simp only [psiSum, xShift_transformedCoord, add_mul, sub_mul, div_mul_eq_mul_div,
      sum_add_distrib, sum_sub_distrib, sum_div]
  rw [psiSum_eq_of_le (hv (m + 2)) (by lia), psiSum_eq_of_le (hv m) (by lia),
    sum_extraCoord_mul] at hR
  obtain ⟨e1, e2, e3⟩ := extraCoord_values m
  have r1 := psiW_rec m
  have r2 := psiW_rec (m + 2)
  rw [e1, e2, e3, hL] at hR
  simp only [psiQ]
  rw [hR]
  have hm : (2 * ((m : ℚ) + 3) - 1) ≠ 0 := by
    have := (m.cast_nonneg : (0 : ℚ) ≤ m); intro h; linarith
  push_cast at r1 r2
  have h4 : psiW (m + 2 + 2) = -((m : ℚ) + 2 + 3) / (m + 2 + 2) * psiW (m + 2) := by
    have : ((m : ℚ) + 2 + 2) ≠ 0 := by positivity
    field_simp
    linear_combination r2
  have h0 : psiW m = -((m : ℚ) + 2) / (m + 3) * psiW (m + 2) := by
    have : ((m : ℚ) + 3) ≠ 0 := by positivity
    field_simp
    linear_combination r1
  rw [show m + 4 = m + 2 + 2 from rfl, h4, h0]
  field_simp
  ring

/-! ### `β_n` through the functionals -/

/-- `β_n ψ_(n-2) = ψ(q_n)`, from `ψ(c R_n) = (4/3) b_(n,0) = 0`. -/
theorem betaN_mul_psiW {k : ℕ} (hk : 2 ≤ k) : betaN (k + 2) * psiW k = psiQ (k + 2) := by
  have hr : ∀ j, k - 1 < j → residCoord (k + 2) j = 0 := fun j hj ↦
    residCoord_of_lt (by lia)
  have hxr : ∀ j, k < j → xShift (residCoord (k + 2)) j = 0 := fun j hj ↦ by
    simp only [xShift, hr (j + 1) (by lia), zero_mul, zero_div, add_zero, hr (j - 1) (by lia),
      ite_self]
  have hsum := congrArg (fun f : ℕ → ℚ ↦ ∑ i ∈ range (k + 2 + 1), f i * psiW i)
    (funext (xShift_residCoord_add hk))
  simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum, ite_mul, zero_mul,
    sum_ite_eq', mem_range, show k < k + 2 + 1 by lia, ↓reduceIte] at hsum
  have h1 : ∑ i ∈ range (k + 2 + 1), xShift (residCoord (k + 2)) i * psiW i = 0 := by
    have hx := psiSum_xShift hr
    rw [show k - 1 + 1 = k by lia] at hx
    rw [← psiSum, psiSum_eq_of_le hxr (by lia), hx, residCoord_of_le (by lia)]
    simp [residRaw]
  have h2 : ∑ i ∈ range (k + 2 + 1), sqShift k i * psiW i = 0 := by
    have hs1 : ∀ j, k < j → (fun i ↦ if i = k then (1 : ℚ) else 0) j = 0 := fun j hj ↦ by
      simp only [show j ≠ k by lia, ↓reduceIte]
    have hs2 : ∀ j, k + 1 < j → xShift (fun i ↦ if i = k then (1 : ℚ) else 0) j = 0 :=
      fun j hj ↦ by
        rw [xShift_single]
        simp only [show j ≠ k + 1 by lia, show j + 1 ≠ k by lia, ↓reduceIte, add_zero]
    rw [← psiSum, sqShift, psiSum_xShift hs2, xShift_single]
    simp only [show (0 : ℕ) ≠ k + 1 by lia, show 0 + 1 ≠ k by lia, ↓reduceIte, add_zero,
      mul_zero]
  rw [h1, h2, ← psiSum] at hsum
  simp only [psiQ]
  linarith

/-- `β_n G_(n-2)(0) = Q_n(0)`, from `c R_n = (α_n c² + β_n) G_(n-2) - Q_n` at `c = 0`. -/
theorem betaN_mul_eval_zero {k : ℕ} (hk : 2 ≤ k) :
    betaN (k + 2) * (gegen k).eval 0 = (transformed (k + 2)).eval 0 := by
  have h := congrArg (Polynomial.eval 0) (X_mul_residual hk)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow] at h
  linarith

/-! ### The recurrence of `β_n` -/

theorem gegen_eval_zero_rec (j : ℕ) :
    ((j : ℚ) + 2) * (gegen (j + 2)).eval 0 = -((j : ℚ) + 3) * (gegen j).eval 0 := by
  have h := congrArg (Polynomial.eval 0) (gegen_rec j)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, mul_zero, zero_mul, zero_sub] at h
  linear_combination h

theorem gegen_eval_zero_ne_zero (i : ℕ) : (gegen (2 * i)).eval 0 ≠ 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := gegen_eval_zero_rec (2 * i)
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    intro h0
    rw [h0, mul_zero] at h
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · have : (0 : ℚ) ≤ ((2 * i : ℕ) : ℚ) := Nat.cast_nonneg _
      linarith
    · exact ih h1

theorem psiW_ne_zero (i : ℕ) : psiW (2 * i + 1) ≠ 0 := by
  induction i with
  | zero => norm_num [psiW]
  | succ i ih =>
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, psiW]
    have h3 : -(((2 * i + 1 : ℕ) : ℚ) + 3) ≠ 0 := by
      have : (0 : ℚ) ≤ ((2 * i + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
      intro h; linarith
    have h2 : ((2 * i + 1 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
    exact mul_ne_zero (div_ne_zero h3 h2) ih

/-- `Q_(m+2)(0) = Q_m(0)/8 + G_(m+2)(0) / ((m + 3)(m + 4))`. -/
theorem transformed_eval_zero_rec (m : ℕ) :
    (transformed (m + 2)).eval 0 =
      (transformed m).eval 0 / 8 + (gegen (m + 2)).eval 0 / (((m : ℚ) + 3) * (m + 4)) := by
  have h := congrArg (Polynomial.eval 0) (X_mul_transformed_add_three m)
  rw [refHom_eq_C_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one, zero_mul] at h
  push_cast at h
  have : ((m : ℚ) + 2 + 1) * (m + 2 + 2) ≠ 0 := by positivity
  field_simp at h ⊢
  linear_combination -h

/-- The error term `ε_n` of the `β` recurrence: `0` for even `n`, and
`(4/3) q_(n+1,0) / ψ_(n-2)` for odd `n`. -/
noncomputable def epsN (n : ℕ) : ℚ :=
  if n % 2 = 0 then 0 else 4 / 3 * transformedCoord (n + 1) 0 / psiW (n - 2)

/-- `β_n = -(n - 2)/(8(n - 1)) β_(n-2) - 1/(n(n + 2)) + ε_n` for `n ≥ 6`. -/
theorem betaN_rec {k : ℕ} (hk : 2 ≤ k) :
    betaN (k + 4) = -((k : ℚ) + 2) / (8 * (k + 3)) * betaN (k + 2) -
      1 / (((k : ℚ) + 4) * (k + 6)) + epsN (k + 4) := by
  have h3 : ((k : ℚ) + 3) ≠ 0 := by positivity
  have h4 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have h5 : ((k : ℚ) + 5) ≠ 0 := by positivity
  have h6 : ((k : ℚ) + 6) ≠ 0 := by positivity
  rcases Nat.even_or_odd' k with ⟨i, rfl | rfl⟩
  · have hb1 := betaN_mul_eval_zero (k := 2 * i + 2) (by lia)
    have hb0 := betaN_mul_eval_zero hk
    have hq := transformed_eval_zero_rec (2 * i + 2)
    have hg1 := gegen_eval_zero_rec (2 * i)
    have hg2 := gegen_eval_zero_rec (2 * i + 2)
    have hg : (gegen (2 * i + 2)).eval 0 ≠ 0 := by
      rw [show 2 * i + 2 = 2 * (i + 1) by ring]; exact gegen_eval_zero_ne_zero _
    simp only [epsN, show (2 * i + 4) % 2 = 0 by lia, ↓reduceIte, add_zero]
    rw [show 2 * i + 2 + 2 = 2 * i + 4 by ring] at hb1 hq hg2
    push_cast at hg1 hg2 hq ⊢
    apply mul_right_cancel₀ hg
    rw [hb1, hq, ← hb0]
    field_simp
    linear_combination
      8 * ((i : ℚ) + 2) * ((i : ℚ) + 3) ^ 2 * (2 * i + 5) * betaN (2 * i + 2) * hg1 +
        16 * ((i : ℚ) + 3) * (2 * i + 3) * hg2
  · have hb1 := betaN_mul_psiW (k := 2 * i + 1 + 2) (by lia)
    have hb0 := betaN_mul_psiW hk
    have hT := psiQ_rec (2 * i + 1 + 2)
    have r1 := psiW_rec (2 * i + 1)
    have r2 := psiW_rec (2 * i + 1 + 2)
    have hp : psiW (2 * i + 1 + 2) ≠ 0 := by
      rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring]; exact psiW_ne_zero _
    simp only [epsN, show ¬ ((2 * i + 1 + 4) % 2 = 0) by lia, ↓reduceIte,
      show 2 * i + 1 + 4 - 2 = 2 * i + 1 + 2 by lia]
    rw [show 2 * i + 1 + 2 + 2 = 2 * i + 1 + 4 by ring] at hb1 r2
    rw [show 2 * i + 1 + 2 + 3 = 2 * i + 1 + 4 + 1 by ring,
      show 2 * i + 1 + 2 + 2 = 2 * i + 1 + 4 by ring] at hT
    push_cast at r1 r2 hT ⊢
    have e1 : psiW (2 * i + 1) =
        -(2 * (i : ℚ) + 1 + 2) / (2 * (i : ℚ) + 1 + 3) * psiW (2 * i + 1 + 2) := by
      have : (2 * (i : ℚ) + 1 + 3) ≠ 0 := by positivity
      field_simp
      linear_combination r1
    have e2 : psiW (2 * i + 1 + 4) =
        -(2 * (i : ℚ) + 1 + 2 + 3) / (2 * (i : ℚ) + 1 + 2 + 2) * psiW (2 * i + 1 + 2) := by
      have : (2 * (i : ℚ) + 1 + 2 + 2) ≠ 0 := by positivity
      field_simp
      linear_combination r2
    have eT : psiQ (2 * i + 1 + 4) = 4 / 3 * transformedCoord (2 * i + 1 + 4 + 1) 0 +
        psiQ (2 * i + 1 + 2) / 8 +
          psiW (2 * i + 1 + 4) / ((2 * (i : ℚ) + 1 + 2 + 3) * (2 * (i : ℚ) + 1 + 2 + 4)) := by
      linear_combination -hT
    apply mul_right_cancel₀ hp
    rw [hb1, eT, ← hb0, e1, e2]
    field_simp
    ring

/-! ### The scalar recurrence `z_n = -C(n) - D(n) z_(n-2) + e_n` -/

/-- `z_n = β_n / α_n`. -/
noncomputable def zN (n : ℕ) : ℚ := betaN n / alphaN n

/-- `C(n) = (n² - 1)/((n + 2)(2n - 1))`. -/
def recC (n : ℕ) : ℚ := ((n : ℚ) ^ 2 - 1) / ((n + 2) * (2 * n - 1))

/-- `D(n) = n(n + 1)(2n - 5)/(8(n - 3)(n - 1)(2n - 1))`. -/
def recD (n : ℕ) : ℚ := n * ((n : ℚ) + 1) * (2 * n - 5) / (8 * (n - 3) * (n - 1) * (2 * n - 1))

/-- The error term `e_n = ε_n / α_n`, zero in even parity. -/
noncomputable def eN (n : ℕ) : ℚ := epsN n / alphaN n

theorem zN_rec {k : ℕ} (hk : 2 ≤ k) :
    zN (k + 4) = -recD (k + 4) * zN (k + 2) - recC (k + 4) + eN (k + 4) := by
  simp only [zN, eN, recC, recD, alphaN, betaN_rec hk]
  have h1 : ((k : ℚ) + 2) ^ 2 - 1 ≠ 0 := by nlinarith [(k.cast_nonneg : (0 : ℚ) ≤ k)]
  have h2 : ((k : ℚ) + 4) ^ 2 - 1 ≠ 0 := by nlinarith [(k.cast_nonneg : (0 : ℚ) ≤ k)]
  have h3 : 2 * ((k : ℚ) + 2) - 1 ≠ 0 := by have := (k.cast_nonneg : (0 : ℚ) ≤ k); intro h; linarith
  have h4 : 2 * ((k : ℚ) + 4) - 1 ≠ 0 := by have := (k.cast_nonneg : (0 : ℚ) ≤ k); intro h; linarith
  have h5 : ((k : ℚ) + 4) - 3 ≠ 0 := by have := (k.cast_nonneg : (0 : ℚ) ≤ k); intro h; linarith
  have h6 : ((k : ℚ) + 4) - 1 ≠ 0 := by have := (k.cast_nonneg : (0 : ℚ) ≤ k); intro h; linarith
  push_cast
  field_simp
  ring

end RealRooted.BigDescents321
