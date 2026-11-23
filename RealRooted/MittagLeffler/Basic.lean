module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.Veronese
import RealRooted.MultiplierSequence.PolyaSchur.Growth
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Mittag--Leffler functions with natural stride and residue

`mittagLefflerNat r s` is the classical `E_{r,s+1}`. Positive stride is
needed for entire convergence. The positive Type-I results use `s < r`;
no such assertion is made at stride zero or at arbitrary later residues.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- The integer-parameter Mittag--Leffler series `sum z^k / (s+r*k)!`,
expressed in exponential Taylor normalization. At stride zero its series
need not converge globally; the following entire statements require `s < r`. -/
@[expose] noncomputable def mittagLefflerNat (r s : ℕ) : ℂ → ℂ :=
  complexExpGeneratingFunction (fun k ↦ (k.factorial : ℝ) / (s + r * k).factorial)

/-- The defining exponential normalization cancels to the ordinary series. -/
theorem mittagLefflerNat_eq_tsum (r s : ℕ) (z : ℂ) :
    mittagLefflerNat r s z = ∑' k : ℕ, z ^ k / ((s + r * k).factorial : ℂ) := by
  rw [mittagLefflerNat, complexExpGeneratingFunction_eq_tsum]
  apply tsum_congr
  intro k
  push_cast
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hd : ((s + r * k).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (s + r * k).factorial_ne_zero
  field_simp [hk, hd]

/-- Every residue below a positive integer stride gives a positive Type-I
Mittag--Leffler entire function. -/
theorem isLaguerrePolyaTypeI_mittagLefflerNat {r s : ℕ} (hs : s < r) :
    IsLaguerrePolyaTypeI (mittagLefflerNat r s) :=
  isLaguerrePolyaTypeI_factorial_veronese hs

/-- Exact Taylor derivatives at the origin, with no Gamma values at poles. -/
theorem iteratedDeriv_mittagLefflerNat_zero {r s : ℕ} (hs : s < r) (k : ℕ) :
    iteratedDeriv k (mittagLefflerNat r s) 0 =
      (((k.factorial : ℝ) / (s + r * k).factorial : ℝ) : ℂ) := by
  have hsum := IsPFMultiplierSequence.summable_expGenerating_majorant
    (isPFMultiplierSequence_factorial_veronese hs) 1 (zero_le_one : (0 : ℝ) ≤ 1)
  simpa only [mittagLefflerNat, iteratedDeriv_eq_iterate] using
    iteratedDeriv_complexExpGeneratingFunction_zero
      (fun j ↦ (j.factorial : ℝ) / (s + r * j).factorial)
      (R := 1) (by norm_num) (by simpa using hsum) k

/-- These Mittag--Leffler functions do not vanish at the origin. -/
theorem mittagLefflerNat_zero_ne_zero {r s : ℕ} (hs : s < r) :
    mittagLefflerNat r s 0 ≠ 0 := by
  have h := iteratedDeriv_mittagLefflerNat_zero hs 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
    Nat.mul_zero, Nat.add_zero] at h
  rw [h]
  exact ofReal_ne_zero.mpr (by positivity)

/-- Every admissible residue function is nonpolynomial. -/
theorem mittagLefflerNat_ne_polynomial {r s : ℕ} (hs : s < r) (P : ℂ[X]) :
    mittagLefflerNat r s ≠ fun z ↦ P.eval z := by
  intro heq
  have h := iteratedDeriv_mittagLefflerNat_zero hs (P.natDegree + 1)
  rw [heq, iteratedDeriv_fun_eval,
    iterate_derivative_eq_zero (Nat.lt_succ_self P.natDegree)] at h
  simp only [Polynomial.eval_zero] at h
  have hn : (((P.natDegree + 1).factorial : ℝ) /
      (s + r * (P.natDegree + 1)).factorial : ℝ) ≠ 0 := by positivity
  exact ofReal_ne_zero.mpr hn h.symm

end RealRooted
