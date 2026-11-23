/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentParity
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Monic orthogonal parity from symmetric measures

Reflection-invariant real measures have vanishing odd power integrals. The
actual monic moment polynomial therefore has the parity of its degree whenever
the corresponding finite Hankel determinant is nonzero. The identity also
includes the degree-zero polynomial of the zero measure.

No integrability premise is needed for the parity identity: odd Bochner
integrals vanish even when they are undefined and hence take value zero.
Interpreting the moment pairing as an integral of a polynomial product still
uses the usual finite-moment assumptions in the corresponding integration API.
-/

public section

open Polynomial

namespace MeasureTheory

/-- Every odd power integral vanishes for a reflection-invariant real measure. -/
theorem integral_pow_eq_zero_of_odd {mu : Measure ℝ} [mu.IsNegInvariant]
    {n : ℕ} (hn : Odd n) : (∫ x : ℝ, x ^ n ∂mu) = 0 :=
  integral_eq_zero_of_odd fun x => hn.neg_pow x

/-- Reflection symmetry of a measure gives parity of its monic moment polynomial. -/
theorem monicMomentPolynomial_integral_eval_neg {mu : Measure ℝ} [mu.IsNegInvariant]
    (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix (fun k => ∫ x : ℝ, x ^ k ∂mu) n).det)
    (x : ℝ) :
    (monicMomentPolynomial (fun k => ∫ y : ℝ, y ^ k ∂mu) n).eval (-x) =
      (-1 : ℝ) ^ n *
        (monicMomentPolynomial (fun k => ∫ y : ℝ, y ^ k ∂mu) n).eval x :=
  monicMomentPolynomial_eval_neg _ (fun _ hn => integral_pow_eq_zero_of_odd hn) n hdet x

/-- The measure specialization in even degree. -/
theorem even_monicMomentPolynomial_integral {mu : Measure ℝ} [mu.IsNegInvariant]
    (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix (fun k => ∫ x : ℝ, x ^ k ∂mu) n).det)
    (hn : Even n) :
    Function.Even (monicMomentPolynomial (fun k => ∫ x : ℝ, x ^ k ∂mu) n).eval :=
  even_monicMomentPolynomial _ (fun _ hk => integral_pow_eq_zero_of_odd hk) n hdet hn

/-- The measure specialization in odd degree. -/
theorem odd_monicMomentPolynomial_integral {mu : Measure ℝ} [mu.IsNegInvariant]
    (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix (fun k => ∫ x : ℝ, x ^ k ∂mu) n).det)
    (hn : Odd n) :
    Function.Odd (monicMomentPolynomial (fun k => ∫ x : ℝ, x ^ k ∂mu) n).eval :=
  odd_monicMomentPolynomial _ (fun _ hk => integral_pow_eq_zero_of_odd hk) n hdet hn

end MeasureTheory
