module

public import RealRooted.TuranHurwitz.Recurrence
import RealRooted.DerivativeRecurrence.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The recurrence in Theorem 1.1(ii)

Here `b₁ = tau = 0` and `rho = a₁`. We define every family by its recurrence.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The five remaining parameters of Theorem 1.1(ii). -/
structure LaguerreParameters where
  /-- The positive derivative coefficient, also equal to `rho`. -/
  a₁ : ℝ
  /-- The constant coefficient in the multiplier. -/
  a₂ : ℝ
  /-- The positive coefficient of the shifted variable. -/
  b₂ : ℝ
  /-- The nonnegative shift of the excluded half-plane. -/
  lam : ℝ
  /-- The positive coefficient in the row normalization. -/
  sigma : ℝ

/-- The parameter conditions after imposing `b₁ = tau = 0` and `rho = a₁`. -/
structure LaguerreParameters.Admissible (c : LaguerreParameters) : Prop where
  /-- The common derivative and row-index coefficient is positive. -/
  a₁_pos : 0 < c.a₁
  /-- The constant multiplier is nonnegative. -/
  a₂_nonneg : 0 ≤ c.a₂
  /-- The shifted-variable multiplier is positive. -/
  b₂_pos : 0 < c.b₂
  /-- The half-plane shift is nonnegative. -/
  lam_nonneg : 0 ≤ c.lam
  /-- The row-normalization parameter is positive. -/
  sigma_pos : 0 < c.sigma
  /-- The difference of normalized parameters is a nonnegative integer. -/
  integer_shift : ∃ N : ℕ, c.a₂ / c.a₁ - 1 / c.sigma = (N : ℝ)

/-- The shifted polynomial variable for part (ii). -/
@[expose] noncomputable def laguerreShift (c : LaguerreParameters) : ℝ[X] := X + C c.lam

/-- The recurrence family with the normalization factor `1 + sigma*j`. -/
@[expose] noncomputable def laguerreFamily (c : LaguerreParameters) : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => C ((1 + c.sigma * j)⁻¹) *
      ((C (c.a₂ + c.a₁ * j) + C c.b₂ * laguerreShift c) * laguerreFamily c j +
        C c.a₁ * laguerreShift c * (laguerreFamily c j).derivative)

/-- The zeroth row is one. -/
@[simp] theorem laguerreFamily_zero (c : LaguerreParameters) : laguerreFamily c 0 = 1 := rfl

/-- Every row normalization is positive on the admissible range. -/
theorem laguerre_normalization_pos {c : LaguerreParameters} (hc : c.Admissible) (j : ℕ) :
    0 < 1 + c.sigma * j :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc.sigma_pos.le (Nat.cast_nonneg j))

/-- The defining recurrence with its scalar denominator cleared. -/
theorem laguerreFamily_succ (c : LaguerreParameters) {j : ℕ} (hj : 1 + c.sigma * j ≠ 0) :
    C (1 + c.sigma * j) * laguerreFamily c (j + 1) =
      (C (c.a₂ + c.a₁ * j) + C c.b₂ * laguerreShift c) * laguerreFamily c j +
        C c.a₁ * laguerreShift c * (laguerreFamily c j).derivative := by
  rw [laguerreFamily, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hj, map_one, one_mul]

/-- The integer-shift hypothesis forces the normalized Laguerre parameter to be positive. -/
theorem LaguerreParameters.Admissible.ratio_pos {c : LaguerreParameters} (hc : c.Admissible) :
    0 < c.a₂ / c.a₁ := by
  obtain ⟨N, hN⟩ := hc.integer_shift
  have hsig := one_div_pos.mpr hc.sigma_pos
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The first row is independent of `sigma`. -/
@[simp] theorem laguerreFamily_one (c : LaguerreParameters) :
    laguerreFamily c 1 = C c.a₂ + C c.b₂ * laguerreShift c := by
  simp [laguerreFamily]

private theorem laguerreFamily_derivative_recurrence (c : LaguerreParameters) (j : ℕ) :
    laguerreFamily c (j + 1) =
      (C ((1 + c.sigma * j)⁻¹) * C c.a₁ * laguerreShift c) *
          (laguerreFamily c j).derivative +
        (C ((1 + c.sigma * j)⁻¹) *
          (C (c.a₂ + c.a₁ * j) + C c.b₂ * laguerreShift c)) * laguerreFamily c j := by
  rw [laguerreFamily]
  ring

/-- Every row has its index as degree and a positive leading coefficient. -/
theorem laguerreFamily_natDegree_and_leadingCoeff_pos {c : LaguerreParameters}
    (hc : c.Admissible) (j : ℕ) :
    (laguerreFamily c j).natDegree = j ∧ 0 < (laguerreFamily c j).leadingCoeff := by
  have hA (n : ℕ) :
      (C ((1 + c.sigma * n)⁻¹) * C c.a₁ * laguerreShift c).natDegree ≤ 1 + 1 := by
    dsimp [laguerreShift]
    compute_degree
    norm_num
  have hB (n : ℕ) :
      (C ((1 + c.sigma * n)⁻¹) *
        (C (c.a₂ + c.a₁ * n) + C c.b₂ * laguerreShift c)).natDegree ≤ 1 := by
    dsimp [laguerreShift]
    compute_degree
  have h := RealRooted.derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos
    (P := laguerreFamily c) (d := 1) (D₀ := 0) (laguerreFamily_derivative_recurrence c)
    hA hB (by simp) (by simp) (by simp)
    (fun n => by
      norm_num [laguerreShift, mul_assoc, coeff_C_mul, coeff_add, coeff_X, coeff_C]
      exact mul_pos (inv_pos.mpr (laguerre_normalization_pos hc n)) hc.b₂_pos) j
  simpa using h

/-- No admissible recurrence row is zero. -/
theorem laguerreFamily_ne_zero {c : LaguerreParameters} (hc : c.Admissible) (j : ℕ) :
    laguerreFamily c j ≠ 0 :=
  leadingCoeff_ne_zero.mp (laguerreFamily_natDegree_and_leadingCoeff_pos hc j).2.ne'

/-- The reflected generalized Laguerre recurrence from Table 1, with integer parameter `N`. -/
@[expose] noncomputable def reflectedLaguerre (N : ℕ) (lam : ℝ) : ℕ → ℝ[X] :=
  laguerreFamily ⟨1, (N : ℝ) + 1, 1, lam, 1⟩

/-- The reflected ordinary Laguerre recurrence. -/
@[expose] noncomputable def reflectedOrdinaryLaguerre : ℕ → ℝ[X] := reflectedLaguerre 0 0

/-- The Table 1 reflected Laguerre parameters satisfy every condition of part (ii). -/
theorem reflectedLaguerre_admissible (N : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    (LaguerreParameters.mk 1 ((N : ℝ) + 1) 1 lam 1).Admissible := by
  refine ⟨by norm_num, by positivity, by norm_num, hlam, by norm_num, N, ?_⟩
  simp

end RealRooted.TuranHurwitz
