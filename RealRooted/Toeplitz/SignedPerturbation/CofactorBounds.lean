module

public import RealRooted.Toeplitz.SignedPerturbation.Chebyshev
public import RealRooted.Toeplitz.SignedPerturbation.Factorization
import Mathlib.Algebra.BigOperators.Field

/-!
# Bounds for the cofactor and its reciprocal

If the nonconstant coefficients of a power series `C` with constant term `1` have `ℓ¹` norm at
most `1/2`, then the first `n + 1` coefficients of `C⁻¹` have `ℓ¹` norm at most `2 - 2⁻ⁿ`.  We
bound the `ℓ¹` norm of the nonconstant part of the cofactor of the rescaled denominator by
`B(ρ) / 2`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.ToeplitzPerturbation


theorem coeff_succ_inv_eq {C : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff C = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1) C⁻¹ =
      -∑ ℓ ∈ Finset.range (n + 1),
        PowerSeries.coeff (ℓ + 1) C * PowerSeries.coeff (n - ℓ) C⁻¹ := by
  have h := congrArg (PowerSeries.coeff (n + 1))
    (PowerSeries.mul_inv_cancel C (by rw [h0]; exact one_ne_zero))
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i C * PowerSeries.coeff j C⁻¹), Finset.sum_range_succ'] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0] at h
  simp only [PowerSeries.coeff_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    Nat.sub_zero, one_mul] at h
  have : ∀ ℓ ∈ Finset.range (n + 1), n + 1 - (ℓ + 1) = n - ℓ := fun ℓ _ => by lia
  rw [Finset.sum_congr rfl fun ℓ hℓ => by rw [this ℓ hℓ]] at h
  linarith

theorem sum_abs_coeff_inv_le {C : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff C = 1)
    (hH : ∀ N, ∑ ℓ ∈ Finset.range N, |PowerSeries.coeff (ℓ + 1) C| ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), |PowerSeries.coeff k C⁻¹| ≤ 2 - (1 / 2) ^ n := by
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, ∀ k, b k = PowerSeries.coeff k C⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ k, a k = PowerSeries.coeff k C := ⟨_, fun _ => rfl⟩
  simp only [← hb]
  have hb0 : b 0 = 1 := by
    simp [hb, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  have hrec : ∀ n, b (n + 1) = -∑ ℓ ∈ Finset.range (n + 1), a (ℓ + 1) * b (n - ℓ) := by
    intro n; simp only [hb, ha]; exact coeff_succ_inv_eq h0 n
  simp only [← ha] at hH
  have hmono : ∀ m n, m ≤ n →
      ∑ k ∈ Finset.range (m + 1), |b k| ≤ ∑ k ∈ Finset.range (n + 1), |b k| :=
    fun m n h => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by lia)) fun _ _ _ => abs_nonneg _
  induction n with
  | zero => norm_num [hb0]
  | succ n ih =>
    have hstep : ∀ k, |b (k + 1)| ≤ ∑ ℓ ∈ Finset.range (k + 1), |a (ℓ + 1)| * |b (k - ℓ)| := by
      intro k
      rw [hrec, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun ℓ _ => abs_mul _ _
    have hflip := Finset.sum_range_diag_flip (n + 1) (fun ℓ m => |a (ℓ + 1)| * |b m|)
    have h1 : ∑ k ∈ Finset.range (n + 1), |b (k + 1)| ≤
        ∑ ℓ ∈ Finset.range (n + 1), |a (ℓ + 1)| * ∑ k ∈ Finset.range (n + 1), |b k| := by
      calc _ ≤ ∑ k ∈ Finset.range (n + 1), ∑ ℓ ∈ Finset.range (k + 1), |a (ℓ + 1)| * |b (k - ℓ)| :=
            Finset.sum_le_sum fun k _ => hstep k
        _ = ∑ ℓ ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1 - ℓ), |a (ℓ + 1)| * |b k| := hflip
        _ ≤ _ := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := hmono (n - ℓ) n (by lia)
          have e : n + 1 - ℓ = n - ℓ + 1 := by have := Finset.mem_range.mp hℓ; lia
          rw [e]; exact this
    rw [← Finset.sum_mul] at h1
    have h2 := hH (n + 1)
    have h3 : ∑ k ∈ Finset.range (n + 1), |b (k + 1)| ≤
        (1 / 2) * ∑ k ∈ Finset.range (n + 1), |b k| :=
      h1.trans (mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    rw [Finset.sum_range_succ', hb0, abs_one]
    have : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) ^ n / 2 := by ring
    rw [this]
    linarith


theorem sum_range_succ_id (m : ℕ) : ∑ i ∈ Finset.range m, ((i : ℝ) + 1) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The `ℓ`-weight of `qPoly`: bound for the `(ℓ+1)`st coefficient. -/
theorem sum_abs_coeff_qPoly_le (x : ℝ) (hU : ∀ m : ℕ, |chebU x m| ≤ m + 1) (j N : ℕ)
    (hj : 2 ≤ j) :
    ∑ ℓ ∈ Finset.range N, |(qPoly x j).coeff (ℓ + 1)| ≤ j * (j - 1) / 2 := by
  have hterm : ∀ ℓ, |(qPoly x j).coeff (ℓ + 1)| ≤
      if ℓ + 1 < j then (((j - 2 - ℓ : ℕ) : ℝ) + 1) else 0 := by
    intro ℓ
    rw [coeff_qPoly]
    split_ifs with h
    · have := hU (j - 1 - (ℓ + 1))
      rw [show j - 1 - (ℓ + 1) = j - 2 - ℓ by lia] at this ⊢
      exact this
    · simp
  calc ∑ ℓ ∈ Finset.range N, |(qPoly x j).coeff (ℓ + 1)|
      ≤ ∑ ℓ ∈ Finset.range N, (if ℓ + 1 < j then (((j - 2 - ℓ : ℕ) : ℝ) + 1) else 0) :=
        Finset.sum_le_sum fun ℓ _ => hterm ℓ
    _ ≤ ∑ ℓ ∈ Finset.range (N + j), (if ℓ + 1 < j then (((j - 2 - ℓ : ℕ) : ℝ) + 1) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by lia))
          fun ℓ _ _ => ?_
        split_ifs <;> positivity
    _ = ∑ ℓ ∈ Finset.range (j - 1), (if ℓ + 1 < j then (((j - 2 - ℓ : ℕ) : ℝ) + 1) else 0) := by
        symm
        refine Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) fun ℓ hℓ hnot => ?_
        have := Finset.mem_range.mp hℓ
        have : ¬ ℓ < j - 1 := fun h => hnot (Finset.mem_range.mpr h)
        simp [show ¬ ℓ + 1 < j by lia]
    _ = ∑ ℓ ∈ Finset.range (j - 1), (((j - 2 - ℓ : ℕ) : ℝ) + 1) := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        simp [show ℓ + 1 < j by have := Finset.mem_range.mp hℓ; lia]
    _ = ∑ i ∈ Finset.range (j - 1), ((i : ℝ) + 1) := by
        rw [← Finset.sum_range_reflect (fun i => ((i : ℝ) + 1)) (j - 1)]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        congr 2
    _ = j * (j - 1) / 2 := by
        rw [sum_range_succ_id]
        have : ((j - 1 : ℕ) : ℝ) = j - 1 := by rw [Nat.cast_sub (by lia)]; simp
        rw [this]; ring

/-- Bound on the `ℓ¹` norm of the nonconstant part of the cofactor. -/
theorem sum_abs_coeff_cofactor_le (s : ℕ) (c : ℕ → ℝ) (ρ x : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ m : ℕ, |chebU x m| ≤ m + 1) (hB : perturbationB s c ρ ≤ 1) (N : ℕ) :
    ∑ ℓ ∈ Finset.range N, |(cofactor s c ρ x).coeff (ℓ + 1)| ≤ 1 / 2 := by
  have hco : ∀ ℓ, (cofactor s c ρ x).coeff (ℓ + 1) =
      ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * (qPoly x j).coeff (ℓ + 1) := by
    intro ℓ
    rw [cofactor, coeff_add, finsetSum_coeff, coeff_C]
    simp only [Nat.add_one_ne_zero, ite_false, zero_add]
    exact Finset.sum_congr rfl fun j _ => coeff_C_mul _
  calc ∑ ℓ ∈ Finset.range N, |(cofactor s c ρ x).coeff (ℓ + 1)|
      ≤ ∑ ℓ ∈ Finset.range N, ∑ j ∈ Finset.Icc 2 s,
          |c j| * ρ ^ (j + 1) * |(qPoly x j).coeff (ℓ + 1)| := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        rw [hco]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hρ _)]
    _ = ∑ j ∈ Finset.Icc 2 s, |c j| * ρ ^ (j + 1) *
          ∑ ℓ ∈ Finset.range N, |(qPoly x j).coeff (ℓ + 1)| := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.Icc 2 s, |c j| * ρ ^ (j + 1) * (j * (j - 1) / 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_left
          (sum_abs_coeff_qPoly_le x hU j N (Finset.mem_Icc.mp hj).1) (by positivity)
    _ = perturbationB s c ρ / 2 := by
        rw [perturbationB, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 1 / 2 := by linarith

end RealRooted.ToeplitzPerturbation
