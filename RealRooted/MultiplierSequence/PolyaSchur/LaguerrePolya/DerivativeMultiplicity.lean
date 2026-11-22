module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.LaguerreInequalities.Strict
import RealRooted.LaguerreInequalities.DerivativeFormula
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Multiplicity descent for an entire LP derivative shift

A multiple zero of the nonzero function `f' + a f` forces one higher order
of vanishing of `f`. The strict first Laguerre equality classification handles
the first two equations; triangular differentiation recovers every higher
derivative. The nonzero-output assumption excludes annihilated exponentials.
This is the entire-function step in Craven–Csordas (1994), Lemma 4.2.
-/

public section

open Complex

namespace RealRooted

/-- The derivative of an ordinary exponential multiple is its slope times itself. -/
private theorem deriv_eq_slope_mul_of_eq_exp {f : ℂ → ℂ} {b : ℝ}
    (heq : ∀ z, f z = f 0 * exp ((b : ℂ) * z)) (z : ℂ) :
    _root_.deriv f z = (b : ℂ) * f z := by
  have hd := (((hasDerivAt_id' z).const_mul (b : ℂ)).cexp).const_mul (f 0)
  have hf : f = fun w => f 0 * exp ((b : ℂ) * w) := funext heq
  conv_lhs => rw [hf]
  rw [hd.deriv, heq z]
  ring

/-- A double zero of a nonzero real derivative shift of an LP function
forces its first three Taylor derivatives to vanish. -/
theorem IsLaguerrePolya.vanishing_of_linear_double_zero {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (a : ℝ)
    (hne : ∃ z, _root_.deriv f z + (a : ℂ) * f z ≠ 0) {x : ℝ}
    (hzero : _root_.deriv f x + (a : ℂ) * f x = 0)
    (hderiv : _root_.deriv (_root_.deriv f) x + (a : ℂ) * _root_.deriv f x = 0) :
    f x = 0 ∧ _root_.deriv f x = 0 ∧ _root_.deriv (_root_.deriv f) x = 0 := by
  have h0r := congrArg Complex.re hzero
  have h1r := congrArg Complex.re hderiv
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at h0r h1r
  have hlag : laguerreCoefficient f x 1 = 0 := by
    rw [laguerreCoefficient_one hf.differentiable hf.conj]
    simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    linear_combination (_root_.deriv f x).re * h0r - (f x).re * h1r
  rcases (hf.laguerre_one_eq_zero_iff x).mp hlag with hmult | ⟨b, hb⟩
  · refine ⟨hmult.1, hmult.2, ?_⟩
    simpa only [hmult.2, mul_zero, add_zero] using hderiv
  · have hdf := deriv_eq_slope_mul_of_eq_exp hb
    have hconst : ((b : ℂ) + a) * f 0 = 0 := by
      have hprod : (((b : ℂ) + a) * f 0) * exp ((b : ℂ) * x) = 0 := by
        rw [hdf x, hb x] at hzero
        linear_combination hzero
      exact (mul_eq_zero.mp hprod).resolve_right (exp_ne_zero _)
    obtain ⟨z, hz⟩ := hne
    apply (hz ?_).elim
    rw [hdf z, hb z]
    calc
      _ = (((b : ℂ) + a) * f 0) * exp ((b : ℂ) * z) := by ring
      _ = 0 := by rw [hconst, zero_mul]

/-- If the first `k ≥ 2` derivatives of a nonzero real derivative shift
vanish, the first `k+1` derivatives of the LP input vanish. -/
theorem IsLaguerrePolya.vanishing_of_linear_differential {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (a : ℝ)
    (hne : ∃ z, _root_.deriv f z + (a : ℂ) * f z ≠ 0) {x : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hzero : ∀ j < k, iteratedDeriv (j + 1) f x + (a : ℂ) * iteratedDeriv j f x = 0) :
    ∀ j < k + 1, iteratedDeriv j f x = 0 := by
  have h0 : _root_.deriv f x + (a : ℂ) * f x = 0 := by simpa using hzero 0 (by lia)
  have h1 : _root_.deriv (_root_.deriv f) x + (a : ℂ) * _root_.deriv f x = 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hzero 1 (by lia)
  have hbase := (hf.vanishing_of_linear_double_zero a hne h0 h1).1
  intro j hj
  induction j with
  | zero => exact hbase
  | succ j ih =>
      have hprev := ih (by lia)
      have hnext := hzero j (by lia)
      simpa only [hprev, mul_zero, add_zero] using hnext

end RealRooted
