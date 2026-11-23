module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.LaguerreInequalities.Turan
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Raw derivative Turán inequalities for positive Type-I functions

The cubic and second iterated inequalities pass from PF polynomials to their
locally uniform entire limits. These are the raw derivatives of the function,
without factorial division. See Craven and Csordas, *Iterated Laguerre and
Turán inequalities*, Theorem 3.5 and Corollary 3.6 of the author manuscript,
https://math.hawaii.edu/~tom/mathfiles/iteratedLT.pdf.
-/

public section

open Polynomial Filter Topology

namespace RealRooted

/-- The cubic derivative inequality holds on the nonnegative axis for every
positive Type-I function, including zeros and constants. -/
theorem IsLaguerrePolyaTypeI.cubic_derivative_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 2 * (iteratedDeriv 1 f x).re ^ 3 -
      3 * (f x).re * (iteratedDeriv 1 f x).re * (iteratedDeriv 2 f x).re +
      (f x).re ^ 2 * (iteratedDeriv 3 f x).re := by
  obtain ⟨p, hp, hlim⟩ := hf
  have h := Polynomial.tendsto_eval_iterate_derivative_of_tendstoLocallyUniformly hlim
  have hc := (((h 1 x).pow 3).const_mul 2).sub
    ((((h 0 x).mul (h 1 x)).mul (h 2 x)).const_mul 3)
  have ht := hc.add (((h 0 x).pow 2).mul (h 3 x))
  apply ge_of_tendsto (by simpa only [iteratedDeriv_zero, mul_assoc] using ht)
  filter_upwards [] with n
  simpa only [cubicDerivativeForm, eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    Function.iterate_succ_apply', Function.iterate_zero_apply, mul_assoc] using
    (hp n).cubicDerivativeForm_eval_nonneg hx

/-- The second Turán iterate of the raw derivative sequence is nonnegative
on the nonnegative axis for every positive Type-I function. -/
theorem IsLaguerrePolyaTypeI.second_turan_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ((iteratedDeriv 2 f x).re ^ 2 -
        (iteratedDeriv 1 f x).re * (iteratedDeriv 3 f x).re) ^ 2 -
      ((iteratedDeriv 1 f x).re ^ 2 - (f x).re * (iteratedDeriv 2 f x).re) *
        ((iteratedDeriv 3 f x).re ^ 2 -
          (iteratedDeriv 2 f x).re * (iteratedDeriv 4 f x).re) := by
  obtain ⟨p, hp, hlim⟩ := hf
  have h := Polynomial.tendsto_eval_iterate_derivative_of_tendstoLocallyUniformly hlim
  have h1 := ((h 1 x).pow 2).sub ((h 0 x).mul (h 2 x))
  have h2 := ((h 2 x).pow 2).sub ((h 1 x).mul (h 3 x))
  have h3 := ((h 3 x).pow 2).sub ((h 2 x).mul (h 4 x))
  apply ge_of_tendsto (by simpa only [iteratedDeriv_zero] using (h2.pow 2).sub (h1.mul h3))
  filter_upwards [] with n
  simpa only [secondTuranForm, laguerreForm, eval_sub, eval_mul, eval_pow,
    Function.iterate_succ_apply', Function.iterate_zero_apply] using
    (hp n).secondTuranForm_eval_nonneg hx

end RealRooted
