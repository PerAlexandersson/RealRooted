module

import RealRooted.RiemannHypothesis
public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.Hermite.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hermite
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros

/-!
# The Hermite Jensen criterion for the Riemann hypothesis

This is Theorem 1.2 of Cormac O'Sullivan, *Zeros of Jensen polynomials and
asymptotics for the Riemann xi function* (2021), https://arxiv.org/abs/2007.13582.
The normalization is exactly `Σ binom(d,k) γ(n+k) H_{d-k}(X)`, with physicists'
Hermite polynomials. Already the unshifted family characterizes RH.
-/

@[expose] public section

open Polynomial Complex

namespace RealRooted

/-- The Hermite Jensen polynomial of the normalized xi coefficients. -/
noncomputable def riemannXiHermitePolynomial (d n : ℕ) : ℝ[X] :=
  hermiteJensenPolynomial d (fun k => riemannXiCoeff (n + k))

/-- Under RH, every xi Hermite Jensen polynomial splits over the reals. -/
theorem riemannXiHermitePolynomial_splits (hRH : RiemannHypothesis) (d n : ℕ) :
    (riemannXiHermitePolynomial d n).Splits := by
  have hf := riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH
  simpa only [riemannXiHermitePolynomial, riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using
    (hf.iterate_deriv n).hermiteJensenPolynomial_splits d

/-- The unshifted Hermite Jensen family characterizes Mathlib's RH. -/
theorem riemannHypothesis_iff_riemannXiHermitePolynomial_zero_splits :
    RiemannHypothesis ↔ ∀ d, (riemannXiHermitePolynomial d 0).Splits := by
  constructor
  · intro h d
    exact riemannXiHermitePolynomial_splits h d 0
  · intro h
    have hF := (isLaguerrePolya_mul_exp_neg_sq_iff differentiable_riemannXiTheta
      riemannXiTheta_conj).mpr (by
        simpa only [riemannXiHermitePolynomial, riemannXiCoeff, Nat.zero_add] using h)
    apply riemannHypothesis_iff_riemannXiTheta_zeros.mpr
    intro z hz
    apply hF.im_eq_zero_of_eq_zero ?_ (by simp [hz])
    intro hzero
    have h0 := congrFun hzero 0
    exact riemannXiTheta_zero_ne_zero (by simpa using h0)

/-- **O'Sullivan's Hermite criterion:** RH holds exactly when the Hermite Jensen
polynomials split for every degree and shift. -/
theorem riemannHypothesis_iff_riemannXiHermitePolynomial_splits :
    RiemannHypothesis ↔ ∀ d n, (riemannXiHermitePolynomial d n).Splits := by
  constructor
  · exact riemannXiHermitePolynomial_splits
  · intro h
    exact riemannHypothesis_iff_riemannXiHermitePolynomial_zero_splits.mpr (fun d => h d 0)

end RealRooted
