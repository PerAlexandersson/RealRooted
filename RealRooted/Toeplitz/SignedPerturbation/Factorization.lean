module

public import RealRooted.Toeplitz.SignedPerturbation.Chebyshev
public import RealRooted.Toeplitz.SignedPerturbation.Rows
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Factorization of the rescaled denominator

At a point `(ρ, x, λ)` satisfying the two real conditions below, the rescaled denominator
`1 - λ ρ z + ρ ^ 2 z ^ 2 + ∑ c_j ρ ^ (j + 1) z ^ (j + 1)` equals
`(1 - 2 x z + z ^ 2)` times a cofactor polynomial.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.ToeplitzPerturbation

section Factorization

variable (s : ℕ) (c : ℕ → ℝ) (ρ x : ℝ)

/-- The cofactor of `X ^ 2 - 2 x X + 1` in the rescaled denominator. -/
def cofactor : ℝ[X] :=
  C (ρ ^ 2) + ∑ j ∈ Finset.Icc 2 s, C (c j * ρ ^ (j + 1)) * qPoly x j

theorem factorization (lam : ℝ)
    (h1 : ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j = 0)
    (h2 : lam * ρ = 2 * x * ρ ^ 2 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU x j) :
    (X ^ 2 - C (2 * x) * X + 1) * cofactor s c ρ x =
      1 - C (lam * ρ) * X + C (ρ ^ 2) * X ^ 2 +
        ∑ j ∈ Finset.Icc 2 s, C (c j * ρ ^ (j + 1)) * X ^ (j + 1) := by
  have hq : ∀ j, (X ^ 2 - C (2 * x) * X + 1) * qPoly x j =
      X ^ (j + 1) - C (chebU x j) * X + C (chebUPred x j) := fun j => by
    rw [← X_pow_succ_eq x j]; ring
  have hsum : (X ^ 2 - C (2 * x) * X + 1) * cofactor s c ρ x =
      C (ρ ^ 2) * (X ^ 2 - C (2 * x) * X + 1) +
        (∑ j ∈ Finset.Icc 2 s, C (c j * ρ ^ (j + 1)) * X ^ (j + 1)
          - C (∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU x j) * X
          + C (∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j)) := by
    rw [cofactor, mul_add, Finset.mul_sum, map_sum, map_sum, Finset.sum_mul]
    have : ∀ j ∈ Finset.Icc 2 s, (X ^ 2 - C (2 * x) * X + 1) * (C (c j * ρ ^ (j + 1)) * qPoly x j)
        = C (c j * ρ ^ (j + 1)) * X ^ (j + 1) - C (c j * ρ ^ (j + 1) * chebU x j) * X
          + C (c j * ρ ^ (j + 1) * chebUPred x j) := by
      intro j _
      rw [mul_left_comm, hq j]; simp only [map_mul]; ring
    rw [mul_comm _ (C (ρ ^ 2)), Finset.sum_congr rfl this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsum]
  have e1 : C (∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j) = C (1 - ρ ^ 2) := by
    congr 1; linarith
  have e2 : C (∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU x j) =
      C (lam * ρ) - C (2 * x) * C (ρ ^ 2) := by
    rw [← map_mul, ← map_sub]; congr 1; linarith
  rw [e1, e2]
  simp only [map_sub, map_mul, map_one, map_pow]
  ring




theorem scaledDenominator_eq_mul_cofactor (lam : ℝ)
    (h1 : ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j = 0)
    (h2 : lam * ρ = 2 * x * ρ ^ 2 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU x j) :
    scaledDenominator s c lam ρ =
      (1 - PowerSeries.C (2 * x) * PowerSeries.X + PowerSeries.X ^ 2) *
        (cofactor s c ρ x : PowerSeries ℝ) := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℝ))
    (factorization s c ρ x lam h1 h2)
  simp only [map_mul, map_sub, map_add, map_sum, map_pow, map_one, coeToPowerSeries.ringHom_apply,
    coe_X, coe_C] at h
  simp only [scaledDenominator, map_mul, map_pow]
  linear_combination -h

/-- The generating series `∑ U_n(x) z ^ n` of the Chebyshev polynomials. -/
def chebSeries (x : ℝ) : PowerSeries ℝ := PowerSeries.mk (chebU x)

theorem chebQuad_mul_chebSeries (x : ℝ) :
    (1 - PowerSeries.C (2 * x) * PowerSeries.X + PowerSeries.X ^ 2) * chebSeries x = 1 := by
  ext n
  rcases n with _ | _ | n
  · simp [chebSeries]
  · simp [chebSeries, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul']
  · simp [chebSeries, sub_mul, add_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', chebU_add_two]

theorem coeff_zero_cofactor
    (h1 : ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j = 0) :
    (cofactor s c ρ x).coeff 0 = 1 := by
  have : ∀ j ∈ Finset.Icc 2 s, (C (c j * ρ ^ (j + 1)) * qPoly x j).coeff 0 =
      c j * ρ ^ (j + 1) * chebUPred x j := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; lia⟩
    rw [coeff_C_mul, coeff_qPoly]
    simp [chebUPred]
  rw [cofactor, coeff_add, finsetSum_coeff, Finset.sum_congr rfl this, coeff_C_zero]
  linarith

/-- The rescaled evaluated row series is `U(z) / cofactor(z)`. -/
theorem scaledRowSeries_eq (lam : ℝ)
    (h1 : ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j = 0)
    (h2 : lam * ρ = 2 * x * ρ ^ 2 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU x j) :
    scaledRowSeries s c lam ρ = (cofactor s c ρ x : PowerSeries ℝ)⁻¹ * chebSeries x := by
  have hCf : (cofactor s c ρ x : PowerSeries ℝ) * (cofactor s c ρ x : PowerSeries ℝ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        coeff_zero_cofactor s c ρ x h1]
      exact one_ne_zero)
  have hD := scaledDenominator_mul_scaledRowSeries s c lam ρ
  rw [scaledDenominator_eq_mul_cofactor s c ρ x lam h1 h2] at hD
  have hQ := chebQuad_mul_chebSeries x
  calc scaledRowSeries s c lam ρ
      = (scaledRowSeries s c lam ρ) * ((1 - PowerSeries.C (2 * x) * PowerSeries.X +
          PowerSeries.X ^ 2) * chebSeries x) *
        ((cofactor s c ρ x : PowerSeries ℝ) * (cofactor s c ρ x : PowerSeries ℝ)⁻¹) := by
        rw [hQ, hCf]; ring
    _ = _ := by
        linear_combination ((cofactor s c ρ x : PowerSeries ℝ)⁻¹ * chebSeries x) * hD

/-- The `k`th coefficient of the inverse of the cofactor. -/
def cofactorInvCoeff (k : ℕ) : ℝ := PowerSeries.coeff k (cofactor s c ρ x : PowerSeries ℝ)⁻¹

theorem row_eval_eq_sum (lam : ℝ)
    (h1 : ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred x j = 0)
    (h2 : lam * ρ = 2 * x * ρ ^ 2 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU x j) (n : ℕ) :
    ρ ^ n * (row s c n).eval lam =
      ∑ k ∈ Finset.range (n + 1), cofactorInvCoeff s c ρ x k * chebU x (n - k) := by
  have h := congrArg (PowerSeries.coeff n) (scaledRowSeries_eq s c ρ x lam h1 h2)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (cofactor s c ρ x : PowerSeries ℝ)⁻¹ *
      PowerSeries.coeff j (chebSeries x))] at h
  simpa [scaledRowSeries, chebSeries, cofactorInvCoeff] using h

end Factorization

end RealRooted.ToeplitzPerturbation
