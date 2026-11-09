module

public import RealRooted.EvenDerivative.Symbol
public import RealRooted.PFPolynomial
import RealRooted.EvenDerivative.Interlacing
import RealRooted.EvenDerivative.Preserver
import RealRooted.Linear
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Examples for even-derivative preservers

Two coefficient sequences illustrate the finite-degree criterion.

* `c = (1, 1, 1, 0, 0, …)` (`evenDerivativeCapTwo`): `T_c(u⁴) = x²(x² + 12x + 24)` is real-rooted
  but `T_c(u⁵) = x³(x² + 20x + 120)` is not, so `T_c` preserves PF polynomials through degree
  four and fails in degree five.
* `c = (1, 2, 1, 0, 0, …)` (`evenDerivativeSquare`, `C(t) = (1 + t)²`): the signed symbol is
  `(1 - w²)²`, so `T_c` preserves PF polynomials and directed interlacing in every degree.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The coefficient sequence `(1, 1, 1, 0, 0, …)`. -/
def evenDerivativeCapTwo (k : ℕ) : ℝ := if k ≤ 2 then 1 else 0

/-- The coefficient sequence `(1, 2, 1, 0, 0, …)` of `(1 + t)²`. -/
def evenDerivativeSquare (k : ℕ) : ℝ := if k = 0 ∨ k = 2 then 1 else if k = 1 then 2 else 0

theorem evenDerivativeOperator_capTwo_X_pow_four :
    evenDerivativeOperator evenDerivativeCapTwo (X ^ 4) = X ^ 2 * (X ^ 2 + 12 * X + 24) := by
  rw [evenDerivativeOperator_X_pow]
  simp [Finset.sum_range_succ, evenDerivativeCapTwo, Nat.descFactorial, map_ofNat]
  ring

theorem evenDerivativeOperator_capTwo_X_pow_five :
    evenDerivativeOperator evenDerivativeCapTwo (X ^ 5) = X ^ 3 * (X ^ 2 + 20 * X + 120) := by
  rw [evenDerivativeOperator_X_pow]
  simp [Finset.sum_range_succ, evenDerivativeCapTwo, Nat.descFactorial, map_ofNat]
  ring

private theorem splits_quadratic_twelve_twentyfour :
    ((X : ℝ[X]) ^ 2 + 12 * X + 24).Splits := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : (X : ℝ[X]) ^ 2 + 12 * X + 24 =
      (X - C (-6 + 2 * Real.sqrt 3)) * (X - C (-6 - 2 * Real.sqrt 3)) := by
    have hC : (C (-6 + 2 * Real.sqrt 3) * C (-6 - 2 * Real.sqrt 3) : ℝ[X]) = 24 := by
      rw [← C_mul]
      have : (-6 + 2 * Real.sqrt 3) * (-6 - 2 * Real.sqrt 3) = 24 := by nlinarith
      rw [this, map_ofNat]
    have hS : (C (-6 + 2 * Real.sqrt 3) + C (-6 - 2 * Real.sqrt 3) : ℝ[X]) = -12 := by
      rw [← C_add]
      have : (-6 + 2 * Real.sqrt 3) + (-6 - 2 * Real.sqrt 3) = -12 := by ring
      rw [this, C_neg, map_ofNat]
    linear_combination (-1 : ℝ[X]) * hC + (X : ℝ[X]) * hS
  rw [this]
  exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)

/-- For `c = (1, 1, 1, 0, …)` the operator preserves PF polynomials through degree four. -/
theorem isPFPolynomial_evenDerivativeOperator_capTwo_of_natDegree_le_four {f : ℝ[X]}
    (hf : IsPFPolynomial f) (hdeg : f.natDegree ≤ 4) :
    IsPFPolynomial (evenDerivativeOperator evenDerivativeCapTwo f) := by
  have hc0 : evenDerivativeCapTwo 0 = 1 := by simp [evenDerivativeCapTwo]
  have hc : ∀ k, 0 ≤ evenDerivativeCapTwo k := fun k => by
    unfold evenDerivativeCapTwo; split_ifs <;> norm_num
  refine isPFPolynomial_evenDerivativeOperator_of_splits_X_pow hc0 hc (N := 4) ?_ hf hdeg
  rw [evenDerivativeOperator_capTwo_X_pow_four]
  exact (Splits.X_pow 2).mul splits_quadratic_twelve_twentyfour

/-- For `c = (1, 1, 1, 0, …)` the image of `u⁵` is not real-rooted. -/
theorem not_splits_evenDerivativeOperator_capTwo_X_pow_five :
    ¬ (evenDerivativeOperator evenDerivativeCapTwo (X ^ 5)).Splits := by
  rw [evenDerivativeOperator_capTwo_X_pow_five]
  intro h
  have hq := (splits_mul_iff_right (pow_ne_zero 3 X_ne_zero) (Splits.X_pow 3)).1 h
  have hnat : ((X : ℝ[X]) ^ 2 + 20 * X + 120).natDegree = 2 := by compute_degree!
  obtain ⟨a, ha⟩ := hq.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by rw [hnat]; norm_num))
  simp at ha
  nlinarith [sq_nonneg (a + 10)]

theorem evenDerivativeSymbol_square :
    evenDerivativeSymbol evenDerivativeSquare 2 = (X ^ 2 - 1) ^ 2 := by
  simp [evenDerivativeSymbol, Finset.sum_range_succ, evenDerivativeSquare, map_ofNat, C_neg]
  ring

/-- For `c = (1, 2, 1, 0, …)` every test polynomial `p_N` is real-rooted. -/
theorem splits_evenDerivativeTest_square (N : ℕ) :
    (evenDerivativeTest evenDerivativeSquare N).Splits := by
  refine splits_evenDerivativeTest_of_splits_symbol (M := 2) (by simp [evenDerivativeSquare])
    (fun k hk => by simp [evenDerivativeSquare]; lia) ?_ N
  rw [evenDerivativeSymbol_square, show (X ^ 2 - 1 : ℝ[X]) = (X - C 1) * (X - C (-1)) by
    simp; ring]
  exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).pow 2

/-- For `c = (1, 2, 1, 0, …)`, that is `T f = f + 2x f'' + x² f^(4)`, the operator preserves PF
polynomials in every degree. -/
theorem isPFPolynomial_evenDerivativeOperator_square {f : ℝ[X]} (hf : IsPFPolynomial f) :
    IsPFPolynomial (evenDerivativeOperator evenDerivativeSquare f) :=
  isPFPolynomial_evenDerivativeOperator (by simp [evenDerivativeSquare])
    (fun k => by unfold evenDerivativeSquare; split_ifs <;> norm_num)
    (splits_evenDerivativeTest_square f.natDegree) hf le_rfl

theorem evenDerivativeOperator_square_X_add_one_pow_three :
    evenDerivativeOperator evenDerivativeSquare ((X + 1) ^ 3) =
      X ^ 3 + 15 * X ^ 2 + 15 * X + 1 := by
  have h1 : ((X : ℝ[X]) + 1) ^ 3 = (X + C 1) ^ 3 := by simp
  have hdeg : (((X : ℝ[X]) + 1) ^ 3).natDegree = 3 := by compute_degree!
  rw [evenDerivativeOperator_eq_sum_range (m := 3) (by rw [hdeg]; norm_num), h1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iterate_derivative_X_add_pow]
  simp [evenDerivativeSquare, Nat.descFactorial, map_ofNat]
  ring

theorem evenDerivativeOperator_square_X_add_one_pow_four :
    evenDerivativeOperator evenDerivativeSquare ((X + 1) ^ 4) =
      X ^ 4 + 28 * X ^ 3 + 78 * X ^ 2 + 28 * X + 1 := by
  have h1 : ((X : ℝ[X]) + 1) ^ 4 = (X + C 1) ^ 4 := by simp
  have hdeg : (((X : ℝ[X]) + 1) ^ 4).natDegree = 4 := by compute_degree!
  rw [evenDerivativeOperator_eq_sum_range (m := 3) (by rw [hdeg]; norm_num), h1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iterate_derivative_X_add_pow]
  simp [evenDerivativeSquare, Nat.descFactorial, map_ofNat]
  ring

/-- For `c = (1, 2, 1, 0, …)` the images of `(u + 1)³` and `(u + 1)⁴` interlace. -/
theorem strictInterl_evenDerivativeOperator_square_X_add_one_pow :
    StrictInterl (X ^ 3 + 15 * X ^ 2 + 15 * X + 1)
      (X ^ 4 + 28 * X ^ 3 + 78 * X ^ 2 + 28 * X + 1) := by
  rw [← evenDerivativeOperator_square_X_add_one_pow_three,
    ← evenDerivativeOperator_square_X_add_one_pow_four]
  have hpow : StrictInterl ((X : ℝ[X]) ^ 3) (X ^ 4) := by
    simpa [pow_succ'] using strictInterl_self_X_mul_of_nonneg (pow_ne_zero 3 X_ne_zero)
      (Splits.X_pow 3) (hasNonnegCoeffs_X.pow 3)
  have hshift := (StrictInterl.comp_X_add_C_iff (f := (X : ℝ[X]) ^ 3) (g := X ^ 4) 1).2 hpow
  simp only [pow_comp, X_comp] at hshift
  have hc0 : evenDerivativeSquare 0 = 1 := by simp [evenDerivativeSquare]
  have hc : ∀ k, 0 ≤ evenDerivativeSquare k := fun k => by
    unfold evenDerivativeSquare; split_ifs <;> norm_num
  have hnn : ∀ n : ℕ, HasNonnegCoeffs ((X + 1 : ℝ[X]) ^ n) := fun n =>
    (hasNonnegCoeffs_X.add hasNonnegCoeffs_one).pow n
  simpa using strictInterl_evenDerivativeOperator hc0 hc (splits_evenDerivativeTest_square 4)
    hshift (hnn 3) (hnn 4) (by simp)

end RealRooted
