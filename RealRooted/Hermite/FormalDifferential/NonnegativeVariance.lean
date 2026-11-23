module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Hermite.FormalDifferential.NonrealIterates
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.RingTheory.PowerSeries.FirstDiscrepancy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The nonnegative-variance complement for polynomial iterates

Kim--Kim (2015), Theorem 1.2: a nonexponential formal symbol with nonzero
constant term and nonnegative second cumulant eventually produces nonreal
roots on every polynomial above a finite degree threshold.
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- The first normalized exponential discrepancy supplies a common degree
threshold; the iteration threshold may still depend on the input polynomial. -/
private theorem exists_eventually_not_splits_normalized {φ : PowerSeries ℝ}
    (h0 : PowerSeries.constantCoeff φ = 1)
    (hv : 0 ≤ 2 * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2)
    (hne : φ ≠ PowerSeries.rescale (PowerSeries.coeff 1 φ) (PowerSeries.exp ℝ)) :
    ∃ p : ℕ, 2 ≤ p ∧ ∀ P : ℝ[X], p ≤ P.natDegree →
      ∀ᶠ m : ℕ in atTop, ¬ ((formalDifferentialOperator φ)^[m] P).Splits := by
  obtain ⟨p, hp, hjet, hdiff⟩ := PowerSeries.exists_first_exponential_discrepancy h0 hne
  have hbad : (p = 2 ∧ 0 < PowerSeries.coeff p φ -
      PowerSeries.coeff 1 φ ^ p / (p.factorial : ℝ)) ∨
      (3 ≤ p ∧ PowerSeries.coeff p φ -
        PowerSeries.coeff 1 φ ^ p / (p.factorial : ℝ) ≠ 0) := by
    by_cases hp2 : p = 2
    · left
      refine ⟨hp2, ?_⟩
      rw [hp2] at hdiff ⊢
      norm_num at hdiff ⊢
      have hn : 0 ≤ PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2 / 2 := by
        linarith
      exact lt_of_le_of_ne (sub_nonneg.mp hn) (Ne.symm hdiff)
    · exact Or.inr ⟨by lia, sub_ne_zero.mpr hdiff⟩
  refine ⟨p, hp, fun P hP ↦ ?_⟩
  apply eventually_not_splits_iterate_of_exponential_jet (PowerSeries.coeff 1 φ)
    (by lia) hjet hbad _ hP
  intro hz
  rw [hz, natDegree_zero] at hP
  lia

/-- Above a finite degree threshold, every real polynomial has nonreal roots
after all sufficiently many iterates of a nonexponential formal symbol with
nonnegative second cumulant. The formal symbol need not converge anywhere. -/
theorem exists_eventually_not_splits_iterate
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ ≠ 0)
    (hv : 0 ≤ 2 * PowerSeries.constantCoeff φ * PowerSeries.coeff 2 φ -
      PowerSeries.coeff 1 φ ^ 2)
    (hne : φ ≠ PowerSeries.C (PowerSeries.constantCoeff φ) *
      PowerSeries.rescale (PowerSeries.coeff 1 φ / PowerSeries.constantCoeff φ)
        (PowerSeries.exp ℝ)) :
    ∃ p : ℕ, 2 ≤ p ∧ ∀ P : ℝ[X], p ≤ P.natDegree →
      ∀ᶠ m : ℕ in atTop, ¬ ((formalDifferentialOperator φ)^[m] P).Splits := by
  let a := PowerSeries.constantCoeff φ
  let ψ : PowerSeries ℝ := PowerSeries.C a⁻¹ * φ
  have ha : a ≠ 0 := h0
  have hψ0 : PowerSeries.constantCoeff ψ = 1 := by simp [ψ, a, h0]
  have hcoeff (k : ℕ) : PowerSeries.coeff k ψ = a⁻¹ * PowerSeries.coeff k φ := by
    simp [ψ]
  have hψv : 0 ≤ 2 * PowerSeries.coeff 2 ψ - PowerSeries.coeff 1 ψ ^ 2 := by
    rw [hcoeff, hcoeff]
    have heq : 2 * (a⁻¹ * PowerSeries.coeff 2 φ) -
        (a⁻¹ * PowerSeries.coeff 1 φ) ^ 2 =
        (2 * a * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2) / a ^ 2 := by
      field_simp [ha]
    rw [heq]
    exact div_nonneg hv (sq_nonneg a)
  have hψne : ψ ≠ PowerSeries.rescale (PowerSeries.coeff 1 ψ) (PowerSeries.exp ℝ) := by
    intro heq
    apply hne
    have hrestore : PowerSeries.C a * ψ = φ := by
      simp only [ψ, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
    calc
      φ = PowerSeries.C a * ψ := hrestore.symm
      _ = PowerSeries.C a * PowerSeries.rescale (PowerSeries.coeff 1 ψ)
          (PowerSeries.exp ℝ) :=
        congrArg (fun χ : PowerSeries ℝ ↦ PowerSeries.C a * χ) heq
      _ = PowerSeries.C (PowerSeries.constantCoeff φ) *
          PowerSeries.rescale (PowerSeries.coeff 1 φ / PowerSeries.constantCoeff φ)
            (PowerSeries.exp ℝ) := by
        rw [hcoeff]
        simp only [a, div_eq_mul_inv, mul_comm]
  obtain ⟨p, hp, hbad⟩ := exists_eventually_not_splits_normalized hψ0 hψv hψne
  refine ⟨p, hp, fun P hP ↦ ?_⟩
  filter_upwards [hbad P hP] with m hm hsplit
  apply hm
  have hpower : ψ ^ m = PowerSeries.C (a⁻¹ ^ m) * φ ^ m := by
    simp only [ψ, mul_pow, map_pow]
  rw [← formalDifferentialOperator_pow, hpower, formalDifferentialOperator_C_mul]
  rw [← formalDifferentialOperator_pow] at hsplit
  exact hsplit.C_mul _

end RealRooted.HermitePoulain
