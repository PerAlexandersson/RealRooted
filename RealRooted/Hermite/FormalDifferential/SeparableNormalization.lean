module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Hermite.FormalDifferential.SeparableIteration
import RealRooted.Hermite.FormalDifferential.Composition

/-!
# Eventual separability without a symbol normalization
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- A nonzero constant term may be normalized away: every nonzero input
of degree congruent to zero or one modulo the first exponential discrepancy
order eventually has simple complex roots under the literal operator iterates. -/
theorem eventually_separable_iterate_of_scaled_exponential_jet
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ ≠ 0)
    (a : ℝ) {p : ℕ} (hp : 2 ≤ p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ =
      PowerSeries.constantCoeff φ * a ^ k / (k.factorial : ℝ))
    (hβ : PowerSeries.coeff p φ -
      PowerSeries.constantCoeff φ * a ^ p / (p.factorial : ℝ) ≠ 0)
    {P : ℝ[X]} (hP : P ≠ 0) (hrem : P.natDegree % p ≤ 1) :
    ∀ᶠ m : ℕ in atTop, ((formalDifferentialOperator φ)^[m] P).Separable := by
  let c := PowerSeries.constantCoeff φ
  let ψ : PowerSeries ℝ := PowerSeries.C c⁻¹ * φ
  have hc : c ≠ 0 := h0
  have hcoeff (k : ℕ) : PowerSeries.coeff k ψ = c⁻¹ * PowerSeries.coeff k φ := by
    simp [ψ]
  have hψjet (k : ℕ) (hk : k < p) :
      PowerSeries.coeff k ψ = a ^ k / (k.factorial : ℝ) := by
    rw [hcoeff, hjet k hk]
    change c⁻¹ * (c * a ^ k / (k.factorial : ℝ)) = a ^ k / (k.factorial : ℝ)
    simp only [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hψβ : PowerSeries.coeff p ψ - a ^ p / (p.factorial : ℝ) ≠ 0 := by
    intro heq
    apply hβ
    rw [hcoeff] at heq
    have h := congrArg (fun x : ℝ ↦ c * x) (sub_eq_zero.mp heq)
    apply sub_eq_zero.mpr
    simpa only [← mul_assoc, mul_inv_cancel₀ hc, one_mul, mul_div_assoc] using h
  filter_upwards [eventually_separable_iterate_of_exponential_jet
    a hp hψjet hψβ hP hrem] with m hm
  have hpower : ψ ^ m = PowerSeries.C (c⁻¹ ^ m) * φ ^ m := by
    simp only [ψ, mul_pow, map_pow]
  rw [← formalDifferentialOperator_pow, hpower, formalDifferentialOperator_C_mul,
    formalDifferentialOperator_pow] at hm
  exact hm.of_mul_right

end RealRooted.HermitePoulain
