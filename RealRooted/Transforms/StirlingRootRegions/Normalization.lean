module

public import RealRooted.NarayanaTransformation.Basis
import Mathlib.Basic.Complex.Basic
import RealRooted.Transforms.StirlingRootRegions.Parabolic
import RealRooted.Transforms.StirlingRootRegions

/-!
# Stirling root regions without monicity

We extend the monic parabolic criterion to polynomials with nonnegative leading
coefficient, including zero and constants. This is the sign-normalized PF formulation of
Brenti--Royle--Wagner's root criterion already proved in `StirlingRootRegions.Parabolic`.
The normalization step and requested interface follow the unpublished manuscript
*Long OEIS proofs and grouped factors under the Stirling transform* (2026), issue #2134.
-/

public section

open Polynomial

namespace RealRooted.StirlingRootRegion

noncomputable section

/-- The closed parabolic criterion for arbitrary nonnegative leading coefficient.
The zero polynomial is allowed, as are constants and repeated boundary roots. -/
theorem isPFPolynomial_comp_of_leadingCoeff_nonneg {m : ℝ} {p : ℝ[X]}
    (hp : 0 ≤ p.leadingCoeff)
    (hr : p ≠ 0 → ∀ r : ℝ, p.IsRoot r → r ≤ m)
    (hz : p ≠ 0 → ∀ z : ℂ, aeval z p = 0 → z.im ≠ 0 →
      4 * z.im ^ 2 ≤ 1 + 4 * m - 4 * z.re) :
    IsPFPolynomial (basisTransform touchard (p.comp (X + C m))) := by
  by_cases hp0 : p = 0
  · simp [hp0, IsPFPolynomial.zero]
  let q := p * C p.leadingCoeff⁻¹
  have hq : q.Monic := monic_mul_leadingCoeff_inv hp0
  have hqpf := isPFPolynomial_comp hq
    (fun r hroot ↦ hr hp0 r (by
      have hc : p.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
      have heval : p.eval r * p.leadingCoeff⁻¹ = 0 := by
        simpa only [q, IsRoot.def, eval_mul, eval_C] using hroot
      exact (mul_eq_zero.mp heval).resolve_right hc))
    (fun z hroot hi ↦ hz hp0 z (by
      have hc : aeval z (C p.leadingCoeff⁻¹ : ℝ[X]) ≠ 0 := by
        simp [leadingCoeff_ne_zero.mpr hp0]
      exact (mul_eq_zero.mp (by simpa only [q, map_mul] using hroot)).resolve_right hc) hi)
  have heq : p = C p.leadingCoeff * q := by
    dsimp [q]
    calc
      p = C (p.leadingCoeff * p.leadingCoeff⁻¹) * p := by
        rw [mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hp0), map_one, one_mul]
      _ = C p.leadingCoeff * (p * C p.leadingCoeff⁻¹) := by rw [map_mul]; ring
  rw [heq, mul_comp, C_comp, ← Polynomial.smul_eq_C_mul,
    Polynomial.basisTransform_smul]
  exact (IsPFPolynomial.of_C_nonneg hp).mul hqpf

/-- The falling-factorial root criterion with nonnegative leading coefficient.
Zero, constants, and all weak root-region boundaries are included. -/
theorem isPFPolynomial_fallingFactorial_mul_of_leadingCoeff_nonneg
    (m : ℕ) {p : ℝ[X]} (hp : 0 ≤ p.leadingCoeff)
    (hr : p ≠ 0 → ∀ r : ℝ, p.IsRoot r → r ≤ (m : ℝ))
    (hz : p ≠ 0 → ∀ z : ℂ, aeval z p = 0 → z.im ≠ 0 →
      4 * z.im ^ 2 ≤ 1 + 4 * (m : ℝ) - 4 * z.re) :
    IsPFPolynomial (basisTransform touchard (fallingFactorialPolynomial m * p)) := by
  exact isPFPolynomial_basisTransform_touchard_fallingFactorial_mul m
    (isPFPolynomial_comp_of_leadingCoeff_nonneg hp hr hz)

end

end RealRooted.StirlingRootRegion
