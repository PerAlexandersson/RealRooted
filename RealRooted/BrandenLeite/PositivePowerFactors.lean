module

public import RealRooted.BrandenLeite.PositivePowerRegularization
public import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import Mathlib.Tactic

/-! The positive real-power Brändén–Leite theorem for factored data. -/

public section

open Polynomial

namespace RealRooted.BrandenLeite

/-- For a nonempty positive product denominator and a PF product numerator
vanishing to order `r`, every positive real power gives nonzero, split
coefficient rows with strictly negative roots, exact degree `n/r`, positive
coefficients through that degree, and oriented consecutive interlacing. -/
theorem affineNegativePowerCoeff_factor_properties
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (r : ℕ) (hr : 0 < r) (n : ℕ) :
    let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    let q := fun m => PowerSeries.affineNegativePowerCoeff κ
      (Q : PowerSeries ℝ) (B : PowerSeries ℝ) m
    q n ≠ 0 ∧ (q n).Splits ∧ (∀ x ∈ (q n).roots, x < 0) ∧
      (q n).natDegree = n / r ∧ (∀ k ≤ n / r, 0 < (q n).coeff k) ∧
      Interl (q n) (q (n + 1)) := by
  let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
  let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
  have hQcoe : (Q : PowerSeries ℝ) =
      ∏ i ∈ s, (1 - PowerSeries.C (α i) * PowerSeries.X : PowerSeries ℝ) :=
    Polynomial.coe_prod_one_sub_C_mul_X s α
  have hBcoe : (B : PowerSeries ℝ) = PowerSeries.C c * PowerSeries.X ^ r *
      ∏ j ∈ t, (1 + PowerSeries.C (β j) * PowerSeries.X : PowerSeries ℝ) :=
    Polynomial.coe_C_mul_X_pow_prod_one_add_C_mul_X c r t β
  obtain ⟨hBnonneg, hBzero, hBpositive⟩ :=
    PowerSeries.coeff_C_mul_X_pow_prod_linear t β hβ hc r
  have hBnn : HasNonnegCoeffs B := by
    intro k
    rw [← Polynomial.coeff_coe, hBcoe]
    exact hBnonneg k
  have hB0 : B.coeff 0 = 0 := by
    rw [← Polynomial.coeff_coe, hBcoe]
    exact hBzero 0 hr
  have hBpos : 0 < B.coeff r := by
    rw [← Polynomial.coeff_coe, hBcoe]
    exact hBpositive
  have hBne : B ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.coeff_zero, lt_self_iff_false] at hBpos
  have hBs : B.Splits := by
    exact (Polynomial.Splits.C_mul_X_pow c r).mul
      (Polynomial.splits_prod_one_add_C_mul_X t β)
  obtain ⟨hne, hsplit, hneg⟩ :=
    affineNegativePowerCoeff_prod_linear_splits_and_roots_neg
      s hs α hα hκ B hB0 hBs hBnn n
  have hdegree := PowerSeries.affineNegativePowerCoeff_factor_degree_and_pos
    s hs α hα t β hβ hc hκ r hr n
  dsimp only at hdegree
  rw [← hQcoe, ← hBcoe] at hdegree
  exact ⟨hne, hsplit, hneg, hdegree.1, hdegree.2,
    interl_affineNegativePowerCoeff_prod_linear_succ
      s hs α hα hκ B hBne hB0 hBs hBnn n⟩

end RealRooted.BrandenLeite
