module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
public import RealRooted.SimpleRoots
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.StrictOperator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FiniteGaussian
import RealRooted.Hermite.PolynomialGaussian
import RealRooted.Hermite.PoulainJensenSimple
import RealRooted.SimpleRoots.Reflection
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Strict LP differential operators and simple Jensen roots

This proves the polynomial-input strict operator theorem and the simple-root
assertion of corrected Craven–Csordas (1994), Proposition 4.1(1), with no
growth restriction. Infinite-zero symbols are handled by multiplicity descent;
finite-zero symbols are polynomial–Gaussian products.

The exclusions differ: arbitrary-input strictness excludes all polynomial
times exponential symbols, including polynomials. Jensen simplicity excludes
only nonconstant exponential factors; polynomial symbols are included.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- A polynomial–Gaussian factorization with positive Gaussian coefficient
gives a strict operator on nonzero real-rooted polynomial inputs. -/
private theorem simple_of_polynomial_gaussian {f : ℂ → ℂ} {q p : ℝ[X]} {a b : ℝ}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (hb : 0 < b)
    (hfactor : ∀ z, f z = (q.map ofRealHom).eval z *
      exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2))
    (hp0 : p ≠ 0) (hp : p.Splits) : IsSimpleRealRooted (taylorDifferentialOperator f p) := by
  have heq : f = fun z => (q.map ofRealHom).eval z *
      exp ((a : ℂ) * z + ((-b / 2 : ℝ) : ℂ) * z ^ 2) := by
    funext z
    rw [hfactor]
    congr 2
    push_cast
    ring
  rw [heq]
  exact simple_taylor_polynomial_gaussian hq hq0 a (by linarith) hp0 hp

/-- An LP symbol nonzero at zero strictly regularizes all nonzero split
polynomial inputs unless it is a polynomial times a real exponential. -/
theorem IsLaguerrePolya.simple_operator_of_not_exp_polynomial {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hne : ∀ (q : ℝ[X]) (a : ℝ), f ≠ fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z))
    {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) :
    IsSimpleRealRooted (taylorDifferentialOperator f p) := by
  rcases Set.finite_or_infinite {r : ℝ | f r = 0} with hfin | hinf
  · obtain ⟨q, a, b, hq, hq0, hb, hfactor⟩ :=
      hf.exists_polynomial_gaussian_of_finite_zeros hf0 hfin
    have hbpos : 0 < b := by
      by_contra hnot
      have hb0 : b = 0 := by linarith
      apply hne q a
      funext z
      simpa [hb0] using hfactor z
    exact simple_of_polynomial_gaussian hq hq0 hbpos hfactor hp0 hp
  · exact hf.simple_operator_of_infinite_zeros hf0 hinf hp0 hp

/-- Simplicity of the monomial differential image transfers to the Jensen
polynomial even when its final Taylor coefficient vanishes. -/
private theorem simple_jensen_of_power_image {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0) (d : ℕ)
    (hsimple : IsSimpleRealRooted (taylorDifferentialOperator f (X ^ d))) :
    IsSimpleRealRooted (jensenPolynomial d (fun k => (iteratedDeriv k f 0).re)) := by
  rw [taylorDifferentialOperator_X_pow] at hsimple
  have hconst : (jensenPolynomial d (fun k => (iteratedDeriv k f 0).re)).coeff 0 ≠ 0 := by
    simp only [coeff_jensenPolynomial, Nat.zero_le, ite_true, Nat.choose_zero_right,
      Nat.cast_one, one_mul, iteratedDeriv_zero]
    intro hz
    have hreal := ofReal_re_iteratedDeriv_zero hf.conj 0
    simp only [iteratedDeriv_zero, hz, ofReal_zero] at hreal
    exact hf0 hreal.symm
  refine ⟨?_, hf.jensenPolynomial_splits d,
    hsimple.2.2.of_reflect hconst (hf.jensenPolynomial_splits d)
      (natDegree_jensenPolynomial_le d _)⟩
  intro hz
  exact hconst (by simp [hz])

/-- Corrected Craven–Csordas Proposition 4.1(1), simple-root assertion:
all Jensen polynomials of an LP symbol nonzero at zero are simple unless
the symbol is a polynomial times an exponential of nonzero real slope. -/
theorem IsLaguerrePolya.simple_jensen_of_not_exp_polynomial {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hne : ∀ (q : ℝ[X]) (a : ℝ), a ≠ 0 →
      f ≠ fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d (fun k => (iteratedDeriv k f 0).re)) := by
  rcases Set.finite_or_infinite {r : ℝ | f r = 0} with hfin | hinf
  · obtain ⟨q, a, b, hq, hq0, hb, hfactor⟩ :=
      hf.exists_polynomial_gaussian_of_finite_zeros hf0 hfin
    rcases hb.eq_or_lt with hb0 | hbpos
    · have ha : a = 0 := by
        by_contra ha
        apply hne q a ha
        funext z
        simpa [← hb0] using hfactor z
      have heq : f = fun z => (q.map ofRealHom).eval z := by
        funext z
        simpa [← hb0, ha] using hfactor z
      rw [heq]
      have hdata : (fun k => (iteratedDeriv k (fun z => (q.map ofRealHom).eval z) 0).re) =
          (fun k => (k.factorial : ℝ) * q.coeff k) := by
        funext k
        simp [iteratedDeriv_fun_eval, eval_zero_iterate_derivative]
      rw [hdata]
      exact simple_jensenPolynomial_polynomial hq hq0 d
    · exact simple_jensen_of_power_image hf hf0 d
        (simple_of_polynomial_gaussian hq hq0 hbpos hfactor
          (pow_ne_zero d X_ne_zero) (Splits.X.pow d))
  · exact hf.simple_jensen_of_infinite_zeros hf0 hinf d

end RealRooted
