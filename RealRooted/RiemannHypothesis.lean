module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hadamard
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros

/-!
# The Riemann hypothesis and xi Jensen polynomials

For `γ(n) = n! ξ⁽²ⁿ⁾(1/2) / (2n)!`, define
`J_{d,n}(X) = ∑_{k=0}^d binom(d,k) γ(n+k) X^k`.
Mathlib's `RiemannHypothesis` is equivalent to every `J_{d,n}` splitting over `ℝ`.
Already the unshifted family `J_{d,0}` suffices for the converse.

The analytic proof uses the entire function `Θ(z²) = ξ(1/2 + z)`. Its growth bound,
Hadamard factorization and zero-set criterion are proved in the imported modules;
the real-rootedness theorem has no additional analytic hypotheses.

## References

* Cormac O'Sullivan, *Zeros of Jensen polynomials and asymptotics for the Riemann
  xi function*, Research in the Mathematical Sciences 8 (2021), article 46,
  Theorem 1.1, https://arxiv.org/abs/2007.13582.
-/

@[expose] public section

open Polynomial Complex

namespace RealRooted

/-- The degree-`d`, shift-`n` Jensen polynomial of the normalized xi coefficients. -/
noncomputable def riemannXiJensenPolynomial (d n : ℕ) : ℝ[X] :=
  jensenPolynomial d (fun k => riemannXiCoeff (n + k))

/-- The coefficients in the binomial normalization of the xi Jensen polynomial. -/
@[simp]
theorem coeff_riemannXiJensenPolynomial (d n k : ℕ) :
    (riemannXiJensenPolynomial d n).coeff k =
      if k ≤ d then (d.choose k : ℝ) * riemannXiCoeff (n + k) else 0 :=
  coeff_jensenPolynomial d _ k

/-- RH is equivalent to the square-variable xi function belonging to the
Laguerre–Pólya class. -/
theorem riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta :
    RiemannHypothesis ↔ IsLaguerrePolya riemannXiTheta := by
  rw [riemannHypothesis_iff_riemannXiTheta_zeros]
  constructor
  · exact isLaguerrePolya_of_orderLE_one orderLE_riemannXiTheta
      differentiable_riemannXiTheta riemannXiTheta_zero_ne_zero riemannXiTheta_conj
  · intro h z hz
    exact h.im_eq_zero_of_eq_zero (fun hzero => riemannXiTheta_zero_ne_zero
      (congrFun hzero 0)) hz

/-- Under Mathlib's Riemann hypothesis, every xi Jensen polynomial splits over the reals. -/
theorem riemannXiJensenPolynomial_splits (hRH : RiemannHypothesis) (d n : ℕ) :
    (riemannXiJensenPolynomial d n).Splits := by
  have h := riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH
  exact h.jensenPolynomial_shift_splits d n

/-- The unshifted xi Jensen polynomials alone characterize Mathlib's RH. -/
theorem riemannHypothesis_iff_riemannXiJensenPolynomial_zero_splits :
    RiemannHypothesis ↔ ∀ d, (riemannXiJensenPolynomial d 0).Splits := by
  rw [riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta]
  simpa only [riemannXiJensenPolynomial, Nat.zero_add] using
    isLaguerrePolya_iff_jensenPolynomial_splits differentiable_riemannXiTheta
      (fun k => (ofReal_riemannXiCoeff k).symm)

/-- **The xi Jensen criterion for RH**: every degree and every nonnegative shift
is hyperbolic exactly when Mathlib's `RiemannHypothesis` holds. -/
theorem riemannHypothesis_iff_riemannXiJensenPolynomial_splits :
    RiemannHypothesis ↔ ∀ d n, (riemannXiJensenPolynomial d n).Splits := by
  constructor
  · exact riemannXiJensenPolynomial_splits
  · intro h
    exact riemannHypothesis_iff_riemannXiJensenPolynomial_zero_splits.mpr (fun d => h d 0)

end RealRooted
