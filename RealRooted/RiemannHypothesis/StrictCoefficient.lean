module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.RiemannHypothesis.JensenSimple
import RealRooted.SimpleRoots.QuadraticDiscriminant
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Strict raw xi Turán inequalities under RH

The checked simple-root theorem for the degree-two Jensen polynomial gives a
strictly positive discriminant. This conditional proof does not
supply the unconditional Fourier-kernel argument of Csordas--Varga (1988).
-/

public section

open Polynomial

namespace RealRooted

/-- The degree-two shifted xi Jensen polynomial in coefficient form. -/
private theorem riemannXiJensenPolynomial_two (n : ℕ) :
    riemannXiJensenPolynomial 2 n = C (riemannXiCoeff n) +
      C (2 * riemannXiCoeff (n + 1)) * X + C (riemannXiCoeff (n + 2)) * X ^ 2 := by
  norm_num [riemannXiJensenPolynomial, jensenPolynomial, Finset.sum_range_succ,
    ← C_mul_X_pow_eq_monomial, C_ofNat]

/-- RH gives strict log-concavity of the raw exponential xi Taylor data. -/
theorem riemannXiCoeff_strict_logConcave (hRH : RiemannHypothesis) (n : ℕ) :
    riemannXiCoeff n * riemannXiCoeff (n + 2) < riemannXiCoeff (n + 1) ^ 2 := by
  have hsimple : IsSimpleRealRooted
      (C (riemannXiCoeff (n + 2)) * X ^ 2 +
        C (2 * riemannXiCoeff (n + 1)) * X + C (riemannXiCoeff n)) := by
    convert isSimpleRealRooted_riemannXiJensenPolynomial hRH 2 n using 1
    rw [riemannXiJensenPolynomial_two]
    ring
  have h := hsimple.discrim_pos (riemannXiCoeff_pos (n + 2)).ne'
  dsimp only [discrim] at h
  nlinarith

end RealRooted
