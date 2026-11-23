/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentChristoffelLocal

/-!
# Paired orthogonal recurrences for Stieltjes moments

The monic orthogonal families for `μ k` and `μ (k+1)` satisfy two coupled
Christoffel identities. Their positive norm ratios are the even and odd
formal Stieltjes numerators. This derives those ratios from moment matrices;
it does not assume a continued-fraction representation.
-/

public section

namespace Polynomial

/-- The even Stieltjes numerator, indexed from zero, is the shifted norm ratio. -/
@[expose] noncomputable def momentStieltjesEven (μ : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentNormSq (fun k => μ (k + 1)) n / momentNormSq μ n

/-- The odd Stieltjes numerator is the next unshifted norm divided by the shifted norm. -/
@[expose] noncomputable def momentStieltjesOdd (μ : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentNormSq μ (n + 1) / momentNormSq (fun k => μ (k + 1)) n

/-- Positive unshifted and shifted Hankel forms give positive even numerators. -/
theorem momentStieltjesEven_pos (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) (n : ℕ) :
    0 < momentStieltjesEven μ n :=
  div_pos (momentNormSq_pos _ n (hshift (n + 1)))
    (momentNormSq_pos μ n (hpos (n + 1)))

/-- The corresponding odd numerators are also positive. -/
theorem momentStieltjesOdd_pos (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) (n : ℕ) :
    0 < momentStieltjesOdd μ n :=
  div_pos (momentNormSq_pos μ (n + 1) (hpos (n + 2)))
    (momentNormSq_pos _ n (hshift (n + 1)))

/-- The shifted degree-`n` polynomial, multiplied by `X`, lies in the span of
the unshifted degree-`n+1` and degree-`n` polynomials, with the even norm ratio. -/
theorem X_mul_monicMomentPolynomial_shift (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) (n : ℕ) :
    X * monicMomentPolynomial (fun k => μ (k + 1)) n =
      monicMomentPolynomial μ (n + 1) +
        C (momentStieltjesEven μ n) * monicMomentPolynomial μ n := by
  exact X_mul_monicMomentPolynomial_shift_of_isUnit μ n
    (isUnit_iff_ne_zero.mpr (hpos n).det_pos.ne')
    (isUnit_iff_ne_zero.mpr (hpos (n + 1)).det_pos.ne')
    (isUnit_iff_ne_zero.mpr (hshift n).det_pos.ne')
    (momentNormSq_pos μ n (hpos (n + 1))).ne'

/-- The unshifted degree-`n+1` polynomial lies in the span of the shifted
degree-`n+1` and degree-`n` polynomials, with the odd norm ratio. -/
theorem monicMomentPolynomial_eq_shift_add (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) (n : ℕ) :
    monicMomentPolynomial μ (n + 1) =
      monicMomentPolynomial (fun k => μ (k + 1)) (n + 1) +
        C (momentStieltjesOdd μ n) *
          monicMomentPolynomial (fun k => μ (k + 1)) n := by
  exact monicMomentPolynomial_eq_shift_add_of_isUnit μ n
    (isUnit_iff_ne_zero.mpr (hpos (n + 1)).det_pos.ne')
    (isUnit_iff_ne_zero.mpr (hshift n).det_pos.ne')
    (isUnit_iff_ne_zero.mpr (hshift (n + 1)).det_pos.ne')
    (momentNormSq_pos _ n (hshift (n + 1))).ne'

end Polynomial
