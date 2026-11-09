module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Rows of the signed Toeplitz perturbation

For real `c₂, …, c_s` the rows `P_n` are the coefficients of the reciprocal
`∑ P_n z ^ n = 1 / (1 - t z + z ^ 2 + ∑_{j=2}^s c_j z ^ (j + 1))` in `ℝ[t]⟦z⟧`.  This file
defines the rows, derives their recurrence and shows that `P_n` is monic of degree `n`.
-/

@[expose] public section

open Polynomial


noncomputable section

namespace RealRooted.ToeplitzPerturbation

variable (s : ℕ) (c : ℕ → ℝ)

/-- `A(R) = ∑_{j=2}^s j |c_j| R ^ (j + 1)`. -/
def perturbationA (R : ℝ) : ℝ := ∑ j ∈ Finset.Icc 2 s, j * |c j| * R ^ (j + 1)

/-- `B(R) = ∑_{j=2}^s j (j - 1) |c_j| R ^ (j + 1)`. -/
def perturbationB (R : ℝ) : ℝ := ∑ j ∈ Finset.Icc 2 s, j * (j - 1) * |c j| * R ^ (j + 1)

/-- The denominator `1 - X z + z² + ∑_{j=2}^s c_j z^{j+1}`, as a power series in `z` with
polynomial coefficients. -/
def denominator : PowerSeries ℝ[X] :=
  1 - PowerSeries.C X * PowerSeries.X + PowerSeries.X ^ 2 +
    ∑ j ∈ Finset.Icc 2 s, PowerSeries.C (Polynomial.C (c j)) * PowerSeries.X ^ (j + 1)

theorem constantCoeff_denominator : PowerSeries.constantCoeff (denominator s c) = 1 := by
  simp [denominator, Finset.sum_eq_zero]

/-- The generating series `1 / (1 - X z + z² + ∑ c_j z^{j+1})` of the rows. -/
def rowSeries : PowerSeries ℝ[X] := PowerSeries.invOfUnit (denominator s c) 1

/-- The `n`th row. -/
def row (n : ℕ) : ℝ[X] := PowerSeries.coeff n (rowSeries s c)

theorem denominator_mul_rowSeries : denominator s c * rowSeries s c = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_denominator s c)

/-- `row (n - k)` if `k ≤ n` and `0` otherwise. -/
def rowLag (n k : ℕ) : ℝ[X] := if k ≤ n then row s c (n - k) else 0

theorem row_zero : row s c 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0) (denominator_mul_rowSeries s c)
  simpa [row, denominator, PowerSeries.coeff_zero_eq_constantCoeff_apply] using h

theorem row_succ (n : ℕ) : row s c (n + 1) =
    X * row s c n - rowLag s c n 1 - ∑ j ∈ Finset.Icc 2 s, C (c j) * rowLag s c n j := by
  have h := congrArg (PowerSeries.coeff (n + 1)) (denominator_mul_rowSeries s c)
  simp only [denominator, add_mul, sub_mul, one_mul, Finset.sum_mul, map_add, map_sub,
    map_sum, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_X_pow_mul'] at h
  simp at h
  simp only [row, rowLag, mul_ite, mul_zero]
  linear_combination h

theorem isMonicOfDegree_row (n : ℕ) : (row s c n).IsMonicOfDegree n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [row_zero, isMonicOfDegree_zero_iff]
    · have hlag : ∀ k, (rowLag s c n k).natDegree ≤ n := by
        intro k
        unfold rowLag
        split_ifs with hk
        · rw [(ih (n - k) (by lia)).natDegree_eq]; lia
        · simp
      have hmain : (X * row s c n).IsMonicOfDegree (n + 1) := by
        simpa [add_comm] using (isMonicOfDegree_X (R := ℝ)).mul (ih n (by lia))
      rw [row_succ, sub_sub]
      refine hmain.sub ?_
      refine lt_of_le_of_lt ((natDegree_add_le _ _).trans (max_le (hlag 1) ?_)) (by lia)
      exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
        (natDegree_C_mul_le _ _).trans (hlag j)

/-- The real denominator after evaluating at `lam` and rescaling `z ↦ ρ z`. -/
def scaledDenominator (lam ρ : ℝ) : PowerSeries ℝ :=
  1 - PowerSeries.C (lam * ρ) * PowerSeries.X + PowerSeries.C (ρ ^ 2) * PowerSeries.X ^ 2 +
    ∑ j ∈ Finset.Icc 2 s, PowerSeries.C (c j * ρ ^ (j + 1)) * PowerSeries.X ^ (j + 1)

/-- The rescaled evaluated generating series: `n ↦ ρ ^ n * P_n(lam)`. -/
def scaledRowSeries (lam ρ : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => ρ ^ n * (row s c n).eval lam

theorem scaledDenominator_mul_scaledRowSeries (lam ρ : ℝ) :
    scaledDenominator s c lam ρ * scaledRowSeries s c lam ρ = 1 := by
  have h := congrArg (fun f => PowerSeries.rescale ρ (PowerSeries.map (evalRingHom lam) f))
    (denominator_mul_rowSeries s c)
  have hS : PowerSeries.rescale ρ (PowerSeries.map (evalRingHom lam) (rowSeries s c)) =
      scaledRowSeries s c lam ρ := by
    ext n; simp [scaledRowSeries, row]
  have hD : PowerSeries.rescale ρ (PowerSeries.map (evalRingHom lam) (denominator s c)) =
      scaledDenominator s c lam ρ := by
    have hC : ∀ a : ℝ, PowerSeries.rescale ρ (PowerSeries.C a) = PowerSeries.C a := by
      intro a; ext n
      simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs <;> simp_all
    simp [denominator, scaledDenominator, map_sum, hC, mul_pow]
    simp only [mul_assoc]
  simpa [map_mul, hS, hD] using h

end RealRooted.ToeplitzPerturbation
