module

public import RealRooted.Hermite.Poulain
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Formal differential symbols on real polynomials

Only finitely many coefficients of a formal symbol act on any polynomial.
This interface includes symbols with zero radius of convergence, as in
Kim--Kim (2015), without using totalized analytic derivative series.
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- The finite action of a real formal power series on a polynomial. -/
@[expose] noncomputable def formalDifferentialOperator
    (φ : PowerSeries ℝ) (P : ℝ[X]) : ℝ[X] :=
  applyAsDifferentialOperator (φ.trunc (P.natDegree + 1)) P

/-- The action is the finite sum of ordinary symbol coefficients times derivatives. -/
theorem formalDifferentialOperator_eq_sum (φ : PowerSeries ℝ) (P : ℝ[X]) :
    formalDifferentialOperator φ P =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        C (PowerSeries.coeff k φ) * (derivative^[k]) P := by
  rw [formalDifferentialOperator, applyAsDifferentialOperator_eq_sum_range_right]
  apply Finset.sum_congr rfl
  intro k hk
  rw [PowerSeries.coeff_trunc, ite_eq_left (Finset.mem_range.mp hk)]

/-- Any polynomial symbol with the required initial coefficients gives the same action. -/
theorem formalDifferentialOperator_eq_applyAsDifferentialOperator
    (φ : PowerSeries ℝ) (f P : ℝ[X])
    (h : ∀ k ≤ P.natDegree, PowerSeries.coeff k φ = f.coeff k) :
    formalDifferentialOperator φ P = applyAsDifferentialOperator f P := by
  rw [formalDifferentialOperator_eq_sum, applyAsDifferentialOperator_eq_sum_range_right]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

/-- A formal symbol coming from a polynomial agrees with the finite operator. -/
theorem formalDifferentialOperator_coe (f P : ℝ[X]) :
    formalDifferentialOperator (f : PowerSeries ℝ) P = applyAsDifferentialOperator f P := by
  apply formalDifferentialOperator_eq_applyAsDifferentialOperator
  intro k _
  exact Polynomial.coeff_coe f k

/-- Truncating beyond the input degree does not change the formal differential action. -/
theorem formalDifferentialOperator_eq_trunc (φ : PowerSeries ℝ) (P : ℝ[X])
    {N : ℕ} (hN : P.natDegree < N) :
    formalDifferentialOperator φ P = applyAsDifferentialOperator (φ.trunc N) P := by
  apply formalDifferentialOperator_eq_applyAsDifferentialOperator
  intro k hk
  rw [PowerSeries.coeff_trunc, ite_eq_left (hk.trans_lt hN)]

/-- A formal differential symbol never raises polynomial degree. -/
theorem natDegree_formalDifferentialOperator_le (φ : PowerSeries ℝ) (P : ℝ[X]) :
    (formalDifferentialOperator φ P).natDegree ≤ P.natDegree :=
  natDegree_applyAsDifferentialOperator_le _ _

/-- A scalar factor in the formal symbol multiplies its output by that scalar. -/
theorem formalDifferentialOperator_C_mul (a : ℝ) (φ : PowerSeries ℝ) (P : ℝ[X]) :
    formalDifferentialOperator (PowerSeries.C a * φ) P =
      C a * formalDifferentialOperator φ P := by
  rw [formalDifferentialOperator, PowerSeries.trunc_C_mul,
    applyAsDifferentialOperator_C_mul]
  rfl

/-- The constant formal symbol one is the identity operator. -/
@[simp] theorem formalDifferentialOperator_one (P : ℝ[X]) :
    formalDifferentialOperator 1 P = P := by
  simpa using formalDifferentialOperator_coe 1 P

end RealRooted.HermitePoulain
