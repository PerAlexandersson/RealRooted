import RealRooted.CombinatorialExamples.BigDescents321.Basic
import RealRooted.CombinatorialExamples.BigDescents321.Gegenbauer
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The transformed big-descent polynomials and their generating function

With `t = 1 - c⁻²` and `x = cz/2`, the big-descent series becomes
`𝒬(c, z) = ∑ Q_n(c) zⁿ = 2 / (1 - z²/2 + √(1 - 2cz + z²))`, where
`Q_n(c) = (c/2)ⁿ A_n(1 - c⁻²)`. We define the transformed families over `ℚ[c]` by the
homogenized recurrences, so no division by `c` occurs:

* `refHom k = μ_k`, the transform `(c/2)^k M_k(1 - c⁻²)` of the reference polynomials;
* `transformed n = Q_n`.

## Main results

* `refHom_eq`: `(k + 1)(k + 2) μ_k = 2 G_k`, so `μ_k` is a Gegenbauer polynomial. The proof
  identifies `1 - cz - ((c² - 1)/2) z² ∑ μ_k z^k` with `√b` (`sqrt_disc_eq`).
* `transformedSeries_mul_add_sqrt`: `𝒬 (1 - z²/2 + √b) = 2`, with `b = 1 - 2cz + z²`.
* `X_mul_transformed_add_three`: the recurrence
  `c Q_(m+3) = Q_(m+2) - Q_m / 8 + ((c² - 1)/2) μ_(m+2)`.
* `aeval_refHom`, `aeval_transformed`: `μ_k(c) = (c/2)^k M_k(1 - c⁻²)` and
  `Q_n(c) = (c/2)ⁿ A_n(1 - c⁻²)` for real `c ≠ 0`.
-/

open Polynomial

noncomputable section

namespace RealRooted.BigDescents321

/-- `μ_0 = 1`, `μ_1 = c`, `μ_(k+2) = c μ_(k+1) + (c² - 1)/4 ∑_(i ≤ k) μ_i μ_(k-i)`. -/
private def refHomAux : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | k + 2 => X * refHomAux (k + 1) +
      C (1 / 4) * (X ^ 2 - 1) * ∑ i : Fin (k + 1), refHomAux i.1 * refHomAux (k - i.1)

/-- The homogenized reference polynomials `μ_k(c) = (c/2)^k M_k(1 - c⁻²)`. -/
irreducible_def refHom (k : ℕ) : ℚ[X] := refHomAux k

@[simp] theorem refHom_zero : refHom 0 = 1 := by rw [refHom_def, refHomAux]

@[simp] theorem refHom_one : refHom 1 = X := by rw [refHom_def, refHomAux]

theorem refHom_add_two (k : ℕ) :
    refHom (k + 2) = X * refHom (k + 1) +
      C (1 / 4) * (X ^ 2 - 1) * ∑ i ∈ Finset.range (k + 1), refHom i * refHom (k - i) := by
  simp only [refHom_def]
  rw [refHomAux, Fin.sum_univ_eq_sum_range (fun i ↦ refHomAux i * refHomAux (k - i))]

/-- The series `𝓜 = ∑ μ_k z^k`. -/
def refHomSeries : PowerSeries ℚ[X] := PowerSeries.mk refHom

/-- `𝓜 = 1 + cz𝓜 + ((c² - 1)/4) z² 𝓜²`. -/
theorem refHomSeries_eq :
    refHomSeries = 1 + PowerSeries.C X * PowerSeries.X * refHomSeries +
      PowerSeries.C (C (1 / 4) * (X ^ 2 - 1)) * PowerSeries.X ^ 2 * refHomSeries ^ 2 := by
  refine PowerSeries.ext fun n ↦ ?_
  rw [map_add, map_add, mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  match n with
  | 0 => simp [refHomSeries]
  | 1 => simp [refHomSeries]
  | k + 2 =>
    simp only [show k + 2 ≠ 0 by lia, show 2 ≤ k + 2 by lia, ↓reduceIte, Nat.add_sub_cancel,
      zero_add, PowerSeries.coeff_succ_X_mul]
    rw [show refHomSeries ^ 2 = refHomSeries * refHomSeries from sq _, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [refHomSeries, PowerSeries.coeff_mk, refHom_add_two]

/-- `√(1 - 2cz + z²) = 1 - cz - ((c² - 1)/2) z² 𝓜`. -/
theorem sqrt_disc_eq :
    PowerSeries.sqrt disc = 1 - PowerSeries.C X * PowerSeries.X -
      2 * PowerSeries.C (C (1 / 4) * (X ^ 2 - 1)) * PowerSeries.X ^ 2 * refHomSeries := by
  set q : PowerSeries ℚ[X] := PowerSeries.C (C (1 / 4) * (X ^ 2 - 1)) with hq_def
  have hq : 4 * q = PowerSeries.C X ^ 2 - 1 := by
    rw [hq_def, show (4 : PowerSeries ℚ[X]) = PowerSeries.C (C 4) by
      rw [map_ofNat C, map_ofNat], ← map_mul, ← mul_assoc, ← C_mul]
    norm_num
  have hM := refHomSeries_eq
  rw [← hq_def] at hM
  symm
  refine PowerSeries.eq_sqrt_of_sq_eq constantCoeff_disc (by simp) ?_
  simp only [disc, map_mul, map_ofNat]
  linear_combination (-4 * q * PowerSeries.X ^ 2) * hM - PowerSeries.X ^ 2 * hq

theorem sqrtDiscCoeff_add_two_eq_refHom (k : ℕ) :
    sqrtDiscCoeff (k + 2) = -(C (1 / 2) * (X ^ 2 - 1)) * refHom k := by
  rw [sqrtDiscCoeff, sqrt_disc_eq, map_sub, map_sub, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X, mul_assoc,
    mul_assoc, show (2 : PowerSeries ℚ[X]) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [show k + 2 ≠ 0 by lia, show k + 2 ≠ 1 by lia, show 2 ≤ k + 2 by lia, ↓reduceIte,
    Nat.add_sub_cancel, refHomSeries, PowerSeries.coeff_mk]
  have h2 : (2 : ℚ[X]) * C (1 / 4) = C (1 / 2) := by
    rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  linear_combination (-(X ^ 2 - 1) * refHom k) * h2

/-- `(k + 1)(k + 2) μ_k = 2 G_k`: the homogenized reference polynomials are Gegenbauer. -/
theorem refHom_eq (k : ℕ) : ((k + 1) * (k + 2) : ℚ[X]) * refHom k = 2 * gegen k := by
  have h := sqrtDiscCoeff_add_two k
  rw [sqrtDiscCoeff_add_two_eq_refHom] at h
  have hne : (1 - X ^ 2 : ℚ[X]) ≠ 0 := by
    intro h0
    have := congrArg (eval 0) h0
    simp at this
  have h2 : (2 : ℚ[X]) * C (1 / 2) = 1 := by
    rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  apply mul_left_cancel₀ hne
  linear_combination 2 * h - ((k + 1) * (k + 2) * (1 - X ^ 2) * refHom k) * h2

/-! ### The transformed polynomials -/

/-- The transformed first-return terms: `ι_1 = c/2`, `ι_2 = c²/4` and
`ι_(j+3) = ((c² - 1)/4) μ_(j+1)`. -/
def firstReturnHom : ℕ → ℚ[X]
  | 0 => 0
  | 1 => C (1 / 2) * X
  | 2 => C (1 / 4) * X ^ 2
  | j + 3 => C (1 / 4) * (X ^ 2 - 1) * refHom (j + 1)

/-- `Q_0 = 1`, `Q_(n+1) = ∑_(j ≤ n) ι_(j+1) Q_(n-j)`. -/
private def transformedAux : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1), firstReturnHom (j.1 + 1) * transformedAux (n - j.1)

/-- The transformed big-descent polynomials `Q_n(c) = (c/2)ⁿ A_n(1 - c⁻²)`. -/
irreducible_def transformed (n : ℕ) : ℚ[X] := transformedAux n

@[simp] theorem transformed_zero : transformed 0 = 1 := by
  rw [transformed_def, transformedAux]

theorem transformed_succ (n : ℕ) :
    transformed (n + 1) =
      ∑ j ∈ Finset.range (n + 1), firstReturnHom (j + 1) * transformed (n - j) := by
  simp only [transformed_def]
  rw [transformedAux, Fin.sum_univ_eq_sum_range
    (fun j ↦ firstReturnHom (j + 1) * transformedAux (n - j))]

/-- The series `𝒬 = ∑ Q_n zⁿ`. -/
def transformedSeries : PowerSeries ℚ[X] := PowerSeries.mk transformed

/-- `a = 1 - z²/2`. -/
def halfSeries : PowerSeries ℚ[X] := 1 - PowerSeries.C (C (1 / 2)) * PowerSeries.X ^ 2

theorem transformedSeries_eq :
    transformedSeries = 1 + PowerSeries.mk firstReturnHom * transformedSeries := by
  refine PowerSeries.ext fun n ↦ ?_
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_mul]
  match n with
  | 0 => simp [transformedSeries, firstReturnHom]
  | n + 1 =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [transformedSeries, PowerSeries.coeff_mk, transformed_succ, firstReturnHom,
      zero_mul, show n + 1 ≠ 0 by lia, ↓reduceIte, zero_add]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- `ι = (1 - √b)/2 + z²/4`. -/
private theorem C_half_mul_C_half : (C (1 / 2) : ℚ[X]) * C (1 / 2) = C (1 / 4) := by
  rw [← C_mul]; norm_num

theorem mk_firstReturnHom :
    PowerSeries.mk firstReturnHom = PowerSeries.C (C (1 / 2)) * (1 - PowerSeries.sqrt disc) +
      PowerSeries.C (C (1 / 4)) * PowerSeries.X ^ 2 := by
  refine PowerSeries.ext fun n ↦ ?_
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, ← sqrtDiscCoeff]
  match n with
  | 0 => simp [firstReturnHom, sqrtDiscCoeff_zero]
  | 1 => simp [firstReturnHom, sqrtDiscCoeff_one]
  | 2 =>
    simp only [firstReturnHom, sqrtDiscCoeff_add_two_eq_refHom 0, refHom_zero]
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, zero_sub, mul_one]
    linear_combination (-(X ^ 2 - 1)) * C_half_mul_C_half
  | j + 3 =>
    simp only [firstReturnHom, show j + 3 ≠ 0 by lia, show j + 3 ≠ 2 by lia, ↓reduceIte,
      zero_sub, mul_zero, add_zero]
    rw [show j + 3 = (j + 1) + 2 by ring, sqrtDiscCoeff_add_two_eq_refHom]
    linear_combination (-(X ^ 2 - 1) * refHom (j + 1)) * C_half_mul_C_half

private theorem two_mul_C_half :
    (2 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 2)) = 1 := by
  rw [show (2 : PowerSeries ℚ[X]) = PowerSeries.C (C 2) by rw [map_ofNat C, map_ofNat],
    ← map_mul, ← C_mul]
  norm_num

private theorem two_mul_C_quarter :
    (2 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 4)) = PowerSeries.C (C (1 / 2)) := by
  rw [show (2 : PowerSeries ℚ[X]) = PowerSeries.C (C 2) by rw [map_ofNat C, map_ofNat],
    ← map_mul, ← C_mul]
  norm_num

/-- The generating function: `𝒬 (1 - z²/2 + √(1 - 2cz + z²)) = 2`. -/
theorem transformedSeries_mul_add_sqrt :
    transformedSeries * (halfSeries + PowerSeries.sqrt disc) = 2 := by
  have hQ := transformedSeries_eq
  have hι := mk_firstReturnHom
  simp only [halfSeries]
  linear_combination 2 * hQ + (2 * transformedSeries) * hι +
    (transformedSeries * (1 - PowerSeries.sqrt disc)) * two_mul_C_half +
    (transformedSeries * PowerSeries.X ^ 2) * two_mul_C_quarter

/-- The rationalized form `𝒬 (a² - b) = 2 (a - √b)`. -/
theorem transformedSeries_mul_sq_sub_disc :
    transformedSeries * (halfSeries ^ 2 - disc) = 2 * (halfSeries - PowerSeries.sqrt disc) := by
  linear_combination (halfSeries - PowerSeries.sqrt disc) * transformedSeries_mul_add_sqrt +
    transformedSeries * PowerSeries.sqrt_sq constantCoeff_disc

private theorem coeff_transformedSeries_mul_sq_sub_disc (n : ℕ) :
    PowerSeries.coeff (n + 1) (transformedSeries * (halfSeries ^ 2 - disc)) =
      2 * X * transformed n - (if 1 ≤ n then 2 * transformed (n - 1) else 0) +
        (if 3 ≤ n then C (1 / 4) * transformed (n - 3) else 0) := by
  have h : transformedSeries * (halfSeries ^ 2 - disc) =
      PowerSeries.C (2 * X) * (PowerSeries.X * transformedSeries) -
        PowerSeries.C 2 * (PowerSeries.X ^ 2 * transformedSeries) +
        PowerSeries.C (C (1 / 4)) * (PowerSeries.X ^ 4 * transformedSeries) := by
    have hq : PowerSeries.C (C (1 / 2)) * PowerSeries.C (C (1 / 2)) =
        (PowerSeries.C (C (1 / 4)) : PowerSeries ℚ[X]) := by
      rw [← map_mul, C_half_mul_C_half]
    simp only [halfSeries, disc, map_mul, map_ofNat]
    linear_combination (transformedSeries * PowerSeries.X ^ 4) * hq -
      (transformedSeries * PowerSeries.X ^ 2) * two_mul_C_half
  rw [h, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul']
  simp only [transformedSeries, PowerSeries.coeff_mk, show (2 ≤ n + 1) ↔ (1 ≤ n) by lia,
    show (4 ≤ n + 1) ↔ (3 ≤ n) by lia, show n + 1 - 2 = n - 1 by lia,
    show n + 1 - 4 = n - 3 by lia]
  split_ifs <;> ring

/-- The recurrence `c Q_(m+3) = Q_(m+2) - Q_m / 8 + ((c² - 1)/2) μ_(m+2)`, that is (1.9) with
`μ_(m+2) = 2 G_(m+2) / ((m + 3)(m + 4))`. -/
theorem X_mul_transformed_add_three (m : ℕ) :
    X * transformed (m + 3) = transformed (m + 2) - C (1 / 8) * transformed m +
      C (1 / 2) * (X ^ 2 - 1) * refHom (m + 2) := by
  have h := congrArg (PowerSeries.coeff (m + 3 + 1)) transformedSeries_mul_sq_sub_disc
  rw [coeff_transformedSeries_mul_sq_sub_disc] at h
  simp only [show 1 ≤ m + 3 by lia, show 3 ≤ m + 3 by lia, ↓reduceIte,
    show m + 3 - 1 = m + 2 by lia, Nat.add_sub_cancel] at h
  rw [show (2 : PowerSeries ℚ[X]) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
    PowerSeries.coeff_C_mul, map_sub, halfSeries, map_sub, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, ← sqrtDiscCoeff,
    show m + 3 + 1 = (m + 2) + 2 by ring, sqrtDiscCoeff_add_two_eq_refHom] at h
  simp only [show m + 2 + 2 ≠ 0 by lia, show m + 2 + 2 ≠ 2 by lia, ↓reduceIte, mul_zero,
    sub_zero, zero_sub] at h
  have h8 : (C (1 / 4) : ℚ[X]) = 2 * C (1 / 8) := by
    rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  have h2 : (2 : ℚ[X]) * C (1 / 2) = 1 := by
    rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  linear_combination C (1 / 2) * h - (X * transformed (m + 3) - transformed (m + 2) +
    C (1 / 8) * transformed m - C (1 / 2) * (X ^ 2 - 1) * refHom (m + 2)) * h2 -
    (C (1 / 2) * transformed m) * h8

/-! ### Evaluation: the transforms of `M_k` and `A_n` -/

section Eval

variable {c : ℝ}

theorem aeval_refHom (hc : c ≠ 0) (k : ℕ) :
    aeval c (refHom k) = (c / 2) ^ k * (motzkinRef k : ℝ[X]).eval (1 - (c ^ 2)⁻¹) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [refHom_add_two, motzkinRef_add_two]
      simp only [map_add, map_mul, map_sum, aeval_X, aeval_C, map_sub, map_pow, map_one,
        eval_add, eval_mul, eval_X, eval_finsetSum, eval_ofNat, ih (k + 1) (by lia)]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      have hs : ∀ i ∈ Finset.range (k + 1),
          (c / 2) ^ (k + 2) * ((1 - (c ^ 2)⁻¹) *
            ((motzkinRef i : ℝ[X]).eval (1 - (c ^ 2)⁻¹) *
              (motzkinRef (k - i) : ℝ[X]).eval (1 - (c ^ 2)⁻¹))) =
          algebraMap ℚ ℝ (1 / 4) * (c ^ 2 - 1) *
            (aeval c (refHom i) * aeval c (refHom (k - i))) := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [ih i (by lia), ih (k - i) (by lia)]
        have hk : (c / 2) ^ (k + 2) = (c / 2) ^ 2 * ((c / 2) ^ i * (c / 2) ^ (k - i)) := by
          rw [← pow_add, ← pow_add]; congr 1; lia
        rw [hk, map_div₀, map_one, map_ofNat]
        field_simp
        ring
      rw [Finset.sum_congr rfl hs]
      ring

theorem aeval_firstReturnHom (hc : c ≠ 0) (j : ℕ) :
    aeval c (firstReturnHom j) = (c / 2) ^ j * (firstReturn j : ℝ[X]).eval (1 - (c ^ 2)⁻¹) := by
  match j with
  | 0 => simp [firstReturnHom]
  | 1 => simp [firstReturnHom]; ring
  | 2 => simp [firstReturnHom]; ring
  | j + 3 =>
    rw [firstReturnHom, firstReturn_add_three, map_mul, map_mul, aeval_refHom hc, aeval_C,
      map_sub, map_pow, aeval_X, map_one, eval_mul, eval_X, map_div₀, map_one, map_ofNat]
    field_simp
    ring

/-- `Q_n(c) = (c/2)ⁿ A_n(1 - c⁻²)` for `c ≠ 0`. -/
theorem aeval_transformed (hc : c ≠ 0) (n : ℕ) :
    aeval c (transformed n) =
      (c / 2) ^ n * (bigDescentPoly n : ℝ[X]).eval (1 - (c ^ 2)⁻¹) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [transformed_succ, bigDescentPoly_succ, map_sum, eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj' := Finset.mem_range.mp hj
      rw [map_mul, aeval_firstReturnHom hc, ih _ (by lia), eval_mul,
        show (c / 2) ^ (n + 1) = (c / 2) ^ (j + 1) * (c / 2) ^ (n - j) by
          rw [← pow_add]; congr 1; lia]
      ring

end Eval

end RealRooted.BigDescents321
