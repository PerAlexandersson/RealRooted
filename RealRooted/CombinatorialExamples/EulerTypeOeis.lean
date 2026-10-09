import RealRooted.EulerBidiagonal.GeneralRows
import RealRooted.EulerBidiagonal.DepRows

/-!
# Euler-type OEIS rows strictly interlace

A156289, A166960, A166961, A166962 and A166972 are rows of the general Euler step
`κ(θ+a)(θ+b) + X(u + vθ)` (with an `n`-dependent `u` for the A1669xx families), so consecutive
rows strictly interlace (#1074, group A).

## A156289

Scratch port: `A156289` is defined exactly as in
`ProofsOeis/A156289.lean`; the bridge `A156289_eq_generalRows` identifies its rows with
`generalRows 1 1 1 3 2`.
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- The rows of A156289 (copy of the downstream definition). -/
def A156289 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ((X) ^ (2)) * ((A156289 n).derivative).derivative +
      (((2 * (X) ^ (2)) + (3 * X))) * (A156289 n).derivative + ((1 + (3 * X))) * A156289 n

/-- One step of A156289 is `generalStep 1 1 1 3 2`. -/
theorem generalStep_one_one_one_three_two (p : ℝ[X]) :
    generalStep 1 1 1 3 2 p =
      X ^ 2 * p.derivative.derivative + (2 * X ^ 2 + 3 * X) * p.derivative +
        (1 + 3 * X) * p := by
  rw [generalStep_eq_second_derivative]
  simp only [map_one, one_mul, map_ofNat, mul_one]
  have h3 : (C (1 + 1 + 1 : ℝ) : ℝ[X]) = 3 := by
    norm_num [map_ofNat]
  rw [h3]
  ring

/-- The rows of A156289 are the rows of the general Euler recurrence. -/
theorem A156289_eq_generalRows (n : ℕ) : A156289 n = generalRows 1 1 1 3 2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [A156289, generalRows, generalStep_one_one_one_three_two, ih]

/-- The A156289 rows are negative-simple of degree `n`. -/
theorem isNegativeSimple_A156289 (n : ℕ) :
    IsNegativeSimple (A156289 n) ∧ (A156289 n).natDegree = n := by
  rw [A156289_eq_generalRows]
  refine isNegativeSimple_generalRows 1 1 1 3 2 one_pos one_pos one_pos
    (fun k => by positivity) ?_ n
  exact comparisonDefect_neg_of_two_mul_u_ge 1 1 1 3 2 one_pos one_pos one_pos (by norm_num)

/-- Consecutive rows of A156289 strictly interlace and have no common root. -/
theorem strictInterl_A156289 (n : ℕ) :
    StrictInterl (A156289 n) (A156289 (n + 1)) ∧
      ∀ r, ¬ ((A156289 n).IsRoot r ∧ (A156289 (n + 1)).IsRoot r) := by
  rw [A156289_eq_generalRows, A156289_eq_generalRows]
  refine strictInterl_generalRows 1 1 1 3 2 one_pos one_pos one_pos
    (fun k => by positivity) ?_ n
  exact comparisonDefect_neg_of_two_mul_u_ge 1 1 1 3 2 one_pos one_pos one_pos (by norm_num)

end RealRooted.EulerBidiagonal

/-!
## A166960, A166961, A166962, A166972 rows strictly interlace

The rows satisfy `P (n + 1) = generalStep κ a b (1 + m n) (-m) (P n)` with
`(κ, a, b, m) = (1, 1, 1, 1), (2, 1, 1/2, 2), (3, 1, 1/3, 3), (3, 1, 1/3, 1)`.
The definitions below are copies of those in `ProofsOeis/A16696x.lean` and `A166972.lean`.
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- Rows with multiplier `1 + m n` and `v = -m`: negative-simple of degree `n`, consecutive rows
strictly interlace without common roots. -/
theorem generalRowsDep_spec_one_add_mul (κ a b m : ℝ) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (n : ℕ) :
    IsNegativeSimple (generalRowsDep κ a b (fun n : ℕ => 1 + m * n) (-m) n) ∧
      (generalRowsDep κ a b (fun n : ℕ => 1 + m * n) (-m) n).natDegree = n ∧
      StrictInterl (generalRowsDep κ a b (fun n : ℕ => 1 + m * n) (-m) n)
        (generalRowsDep κ a b (fun n : ℕ => 1 + m * n) (-m) (n + 1)) ∧
      ∀ r, ¬ ((generalRowsDep κ a b (fun n : ℕ => 1 + m * n) (-m) n).IsRoot r ∧
        (generalRowsDep κ a b (fun n : ℕ => 1 + m * n) (-m) (n + 1)).IsRoot r) := by
  refine generalRowsDep_spec κ a b (fun n : ℕ => 1 + m * n) (-m) m hκ ha hb ?_ ?_ ?_ n
  · intro n
    push_cast
    ring
  · intro n k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith
  · intro n
    apply comparisonDefect_neg_of_two_mul_u_ge κ a b _ _ hκ ha hb
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

/-- The general step with `κ (a + b + 1) = B` and `κ a b = 1` in the downstream shape. -/
theorem generalStep_eq_of_params (κ a b u v B : ℝ) (hB : κ * (a + b + 1) = B)
    (hab : κ * (a * b) = 1) (p : ℝ[X]) :
    generalStep κ a b u v p =
      (C κ * X ^ 2) * p.derivative.derivative + (C B * X + C v * X ^ 2) * p.derivative +
        (C 1 + C u * X) * p := by
  rw [generalStep_eq_second_derivative, hB, hab]
  ring

/-- Rows of A166960 (copy of the downstream definition). -/
def A166960 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C (1) * X ^ 2) * ((A166960 n).derivative).derivative +
      ((C (3) * X + C (-1) * X ^ 2)) * (A166960 n).derivative +
        ((C (1) + C ((1 + (n : ℝ))) * X)) * A166960 n

/-- Rows of A166961 (copy of the downstream definition). -/
def A166961 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C (2) * X ^ 2) * ((A166961 n).derivative).derivative +
      ((C (5) * X + C (-2) * X ^ 2)) * (A166961 n).derivative +
        ((C (1) + C ((1 + (2 * (n : ℝ)))) * X)) * A166961 n

/-- Rows of A166962 (copy of the downstream definition). -/
def A166962 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C (3) * X ^ 2) * ((A166962 n).derivative).derivative +
      ((C (7) * X + C (-3) * X ^ 2)) * (A166962 n).derivative +
        ((C (1) + C ((1 + (3 * (n : ℝ)))) * X)) * A166962 n

/-- Rows of A166972 (copy of the downstream definition). -/
def A166972 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C (3) * X ^ 2) * ((A166972 n).derivative).derivative +
      ((C (7) * X + C (-1) * X ^ 2)) * (A166972 n).derivative +
        ((C (1) + C ((1 + (n : ℝ))) * X)) * A166972 n

/-- A166960 rows are rows of the general step. -/
theorem A166960_eq_generalRowsDep (n : ℕ) :
    A166960 n = generalRowsDep 1 1 1 (fun n : ℕ => 1 + 1 * n) (-1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [A166960, generalRowsDep, generalStep_eq_of_params 1 1 1 _ _ 3 (by norm_num)
        (by norm_num), ih]
      simp only [one_mul]

/-- A166961 rows are rows of the general step. -/
theorem A166961_eq_generalRowsDep (n : ℕ) :
    A166961 n = generalRowsDep 2 1 (1 / 2) (fun n : ℕ => 1 + 2 * n) (-2) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [A166961, generalRowsDep, generalStep_eq_of_params 2 1 (1 / 2) _ _ 5 (by norm_num)
        (by norm_num), ih]

/-- A166962 rows are rows of the general step. -/
theorem A166962_eq_generalRowsDep (n : ℕ) :
    A166962 n = generalRowsDep 3 1 (1 / 3) (fun n : ℕ => 1 + 3 * n) (-3) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [A166962, generalRowsDep, generalStep_eq_of_params 3 1 (1 / 3) _ _ 7 (by norm_num)
        (by norm_num), ih]

/-- A166972 rows are rows of the general step. -/
theorem A166972_eq_generalRowsDep (n : ℕ) :
    A166972 n = generalRowsDep 3 1 (1 / 3) (fun n : ℕ => 1 + 1 * n) (-1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [A166972, generalRowsDep, generalStep_eq_of_params 3 1 (1 / 3) _ _ 7 (by norm_num)
        (by norm_num), ih]
      simp only [one_mul]

/-- A166960: rows strictly interlace, no common roots; rows are negative-simple of degree `n`. -/
theorem A166960_spec (n : ℕ) :
    IsNegativeSimple (A166960 n) ∧ (A166960 n).natDegree = n ∧
      StrictInterl (A166960 n) (A166960 (n + 1)) ∧
      ∀ r, ¬ ((A166960 n).IsRoot r ∧ (A166960 (n + 1)).IsRoot r) := by
  rw [A166960_eq_generalRowsDep, A166960_eq_generalRowsDep]
  exact generalRowsDep_spec_one_add_mul 1 1 1 1 one_pos one_pos one_pos one_pos n

/-- A166961: rows strictly interlace, no common roots; rows are negative-simple of degree `n`. -/
theorem A166961_spec (n : ℕ) :
    IsNegativeSimple (A166961 n) ∧ (A166961 n).natDegree = n ∧
      StrictInterl (A166961 n) (A166961 (n + 1)) ∧
      ∀ r, ¬ ((A166961 n).IsRoot r ∧ (A166961 (n + 1)).IsRoot r) := by
  rw [A166961_eq_generalRowsDep, A166961_eq_generalRowsDep]
  exact generalRowsDep_spec_one_add_mul 2 1 (1 / 2) 2 (by norm_num) one_pos (by norm_num)
    (by norm_num) n

/-- A166962: rows strictly interlace, no common roots; rows are negative-simple of degree `n`. -/
theorem A166962_spec (n : ℕ) :
    IsNegativeSimple (A166962 n) ∧ (A166962 n).natDegree = n ∧
      StrictInterl (A166962 n) (A166962 (n + 1)) ∧
      ∀ r, ¬ ((A166962 n).IsRoot r ∧ (A166962 (n + 1)).IsRoot r) := by
  rw [A166962_eq_generalRowsDep, A166962_eq_generalRowsDep]
  exact generalRowsDep_spec_one_add_mul 3 1 (1 / 3) 3 (by norm_num) one_pos (by norm_num)
    (by norm_num) n

/-- A166972: rows strictly interlace, no common roots; rows are negative-simple of degree `n`. -/
theorem A166972_spec (n : ℕ) :
    IsNegativeSimple (A166972 n) ∧ (A166972 n).natDegree = n ∧
      StrictInterl (A166972 n) (A166972 (n + 1)) ∧
      ∀ r, ¬ ((A166972 n).IsRoot r ∧ (A166972 (n + 1)).IsRoot r) := by
  rw [A166972_eq_generalRowsDep, A166972_eq_generalRowsDep]
  exact generalRowsDep_spec_one_add_mul 3 1 (1 / 3) 1 (by norm_num) one_pos (by norm_num)
    one_pos n

end RealRooted.EulerBidiagonal
