module

public import RealRooted.Wronskian.PolarLaguerre
import RealRooted.LaguerreInequalities.Forms

/-!
# Cubic and second iterated Turán inequalities

The raw derivative inequalities of Craven and Csordas, *Iterated Laguerre
and Turán inequalities*, Proposition 3.4 and Corollary 3.6 of the author
manuscript, https://math.hawaii.edu/~tom/mathfiles/iteratedLT.pdf.
Division-free factor recurrences include roots and constant polynomials.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- The numerator of the second derivative of the logarithmic derivative. -/
noncomputable def cubicDerivativeForm (p : ℝ[X]) : ℝ[X] :=
  2 * p.derivative ^ 3 - 3 * p * p.derivative * p.derivative.derivative +
    p ^ 2 * p.derivative.derivative.derivative

/-- The second Turán iterate of the raw polynomial derivative sequence at index two. -/
noncomputable def secondTuranForm (p : ℝ[X]) : ℝ[X] :=
  laguerreForm p.derivative ^ 2 -
    laguerreForm p * laguerreForm p.derivative.derivative

/-- The negative third Hankel determinant of five successive derivatives. -/
private noncomputable def turanQuotient (p : ℝ[X]) : ℝ[X] :=
  p.derivative.derivative ^ 3 -
    2 * p.derivative * p.derivative.derivative * p.derivative.derivative.derivative +
    p * p.derivative.derivative.derivative ^ 2 +
    p.derivative ^ 2 * p.derivative.derivative.derivative.derivative -
    p * p.derivative.derivative * p.derivative.derivative.derivative.derivative

/-- Adjoining a linear factor gives a positive recurrence for the cubic form. -/
theorem cubicDerivativeForm_X_sub_C_mul (r : ℝ) (p : ℝ[X]) :
    cubicDerivativeForm ((X - C r) * p) =
      (X - C r) ^ 3 * cubicDerivativeForm p + 2 * p ^ 3 := by
  simp only [cubicDerivativeForm, map_add, map_sub, derivative_mul, derivative_X,
    derivative_C, map_zero, derivative_one]
  ring

/-- The quotient recurrence involves only the cubic and second Laguerre forms. -/
private theorem turanQuotient_X_sub_C_mul (r : ℝ) (p : ℝ[X]) :
    turanQuotient ((X - C r) * p) = (X - C r) ^ 3 * turanQuotient p +
      12 * (X - C r) * p * secondLaguerreForm p + 4 * cubicDerivativeForm p := by
  simp only [turanQuotient, cubicDerivativeForm, secondLaguerreForm, map_add, map_sub,
    derivative_mul, derivative_X, derivative_C, map_zero, derivative_one]
  have h12 : (C (1 / 12 : ℝ)) * 12 = 1 := by
    rw [← C_ofNat, ← C_mul]
    simp
  linear_combination -(X - C r) * p *
    (3 * p.derivative.derivative ^ 2 -
      4 * p.derivative * p.derivative.derivative.derivative +
      p * p.derivative.derivative.derivative.derivative) * h12

/-- The second Turán iterate factors without division, including when `p''` vanishes. -/
private theorem secondTuranForm_eq_mul (p : ℝ[X]) :
    secondTuranForm p = p.derivative.derivative * turanQuotient p := by
  simp only [secondTuranForm, laguerreForm, turanQuotient]
  ring

/-- Simultaneous positivity of the cubic form and the third Hankel expression. -/
private theorem forms_nonneg {p : ℝ[X]} (hp : IsPFPolynomial p) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (cubicDerivativeForm p).eval x ∧ 0 ≤ (turanQuotient p).eval x := by
  induction hdegree : p.natDegree using Nat.strong_induction_on generalizing p with
  | ind degree ih =>
      by_cases hz : degree = 0
      · have hC : p = C (p.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero (by simpa [hdegree] using hz)
        rw [hC]
        simp [cubicDerivativeForm, turanQuotient]
      · have hd : 0 < p.natDegree := by rw [hdegree]; exact Nat.pos_of_ne_zero hz
        obtain ⟨r, q, hr, hpq, hq, hqd⟩ := hp.exists_X_sub_C_factor_of_pos_natDegree hd
        obtain ⟨hc, ht⟩ := ih q.natDegree (by simpa [hdegree] using hqd) hq rfl
        have hval := hq.hasNonnegCoeffs.eval_nonneg hx
        have hshift : 0 ≤ x - r := sub_nonneg.mpr (hr.trans hx)
        have hL := secondLaguerreForm_eval_nonneg hq.splits x
        rw [hpq, cubicDerivativeForm_X_sub_C_mul, turanQuotient_X_sub_C_mul]
        simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_ofNat]
        constructor <;> positivity

/-- The cubic derivative form of a PF polynomial is nonnegative on the nonnegative axis. -/
theorem IsPFPolynomial.cubicDerivativeForm_eval_nonneg {p : ℝ[X]}
    (hp : IsPFPolynomial p) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (cubicDerivativeForm p).eval x := (forms_nonneg hp hx).1

/-- Every PF polynomial satisfies the second raw derivative Turán inequality. -/
theorem IsPFPolynomial.secondTuranForm_eval_nonneg {p : ℝ[X]}
    (hp : IsPFPolynomial p) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (secondTuranForm p).eval x := by
  rw [secondTuranForm_eq_mul, eval_mul]
  exact mul_nonneg (hp.derivative.derivative.hasNonnegCoeffs.eval_nonneg hx)
    (forms_nonneg hp hx).2

end RealRooted
