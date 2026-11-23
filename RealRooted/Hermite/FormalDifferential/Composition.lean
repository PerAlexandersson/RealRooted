module

public import RealRooted.Hermite.FormalDifferential.Basic

/-!
# Composition and iteration of formal differential symbols

Finite input degree permits exact multiplication of formal symbols. In
particular a zero constant coefficient annihilates every polynomial after
more iterations than its degree, including symbols with no analytic sum.
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- Formal differential symbols compose by multiplication on polynomial inputs. -/
theorem formalDifferentialOperator_mul (φ ψ : PowerSeries ℝ) (P : ℝ[X]) :
    formalDifferentialOperator (φ * ψ) P =
      formalDifferentialOperator φ (formalDifferentialOperator ψ P) := by
  let N := P.natDegree + 1
  have hN : P.natDegree < N := Nat.lt_succ_self _
  have hD : (formalDifferentialOperator ψ P).natDegree < N :=
    (natDegree_formalDifferentialOperator_le ψ P).trans_lt hN
  calc
    formalDifferentialOperator (φ * ψ) P =
        applyAsDifferentialOperator (φ.trunc N * ψ.trunc N) P := by
      apply formalDifferentialOperator_eq_applyAsDifferentialOperator
      intro k hk
      have h := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc φ ψ (hk.trans_lt hN)
      simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using h
    _ = applyAsDifferentialOperator (φ.trunc N)
        (applyAsDifferentialOperator (ψ.trunc N) P) :=
      applyAsDifferentialOperator_mul _ _ _
    _ = formalDifferentialOperator φ (formalDifferentialOperator ψ P) := by
      rw [formalDifferentialOperator_eq_trunc φ _ hD,
        formalDifferentialOperator_eq_trunc ψ P hN]

/-- Powers of a formal symbol are the corresponding iterated operators. -/
theorem formalDifferentialOperator_pow (φ : PowerSeries ℝ) (m : ℕ) (P : ℝ[X]) :
    formalDifferentialOperator (φ ^ m) P = (formalDifferentialOperator φ)^[m] P := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', formalDifferentialOperator_mul, ih, Function.iterate_succ_apply']

/-- A zero constant symbol annihilates every polynomial after more than its degree
many iterates. This includes the identically zero symbol and input. -/
theorem iterate_formalDifferentialOperator_eq_zero
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ = 0)
    (P : ℝ[X]) {m : ℕ} (hm : P.natDegree < m) :
    (formalDifferentialOperator φ)^[m] P = 0 := by
  have hdiv : (PowerSeries.X : PowerSeries ℝ) ^ m ∣ φ ^ m :=
    pow_dvd_pow_of_dvd ((PowerSeries.X_dvd_iff).mpr h0) m
  have hcoeff := PowerSeries.X_pow_dvd_iff.mp hdiv
  rw [← formalDifferentialOperator_pow]
  calc
    formalDifferentialOperator (φ ^ m) P = applyAsDifferentialOperator 0 P := by
      apply formalDifferentialOperator_eq_applyAsDifferentialOperator
      intro k hk
      simpa using hcoeff k (hk.trans_lt hm)
    _ = 0 := by simp [applyAsDifferentialOperator]

end RealRooted.HermitePoulain
