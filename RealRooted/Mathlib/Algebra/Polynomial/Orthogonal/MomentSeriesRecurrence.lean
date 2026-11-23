/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentSeries
public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentChristoffel
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentSeriesLocal

/-!
# Euler–Gauss equations for orthogonal moments

The paired Christoffel polynomial identities imply the alternating formal
series recurrence, including the initial mass-normalized moment series.
Every coefficient identity follows from finite polynomial moment pairings.
-/

public section

namespace Polynomial

/-- The first normalized moment series starts the Euler–Gauss recurrence. -/
theorem momentOrthogonalSeries_zero_sub_one (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) :
    momentOrthogonalSeries μ 0 - 1 =
      PowerSeries.C (momentStieltjesEven μ 0) * PowerSeries.X *
        momentOrthogonalSeries (fun k => μ (k + 1)) 0 := by
  apply momentOrthogonalSeries_zero_sub_one_of_ne_zero
  · simpa only [momentNormSq_zero] using (momentNormSq_pos μ 0 (hpos 1)).ne'
  · simpa only [momentNormSq_zero, Nat.zero_add] using
      (momentNormSq_pos (fun k => μ (k + 1)) 0 (hshift 1)).ne'

/-- The first Christoffel identity gives the odd Euler–Gauss step. -/
theorem momentOrthogonalSeries_shift_sub (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) (n : ℕ) :
    momentOrthogonalSeries (fun k => μ (k + 1)) n - momentOrthogonalSeries μ n =
      PowerSeries.C (momentStieltjesOdd μ n) * PowerSeries.X *
        momentOrthogonalSeries μ (n + 1) := by
  exact momentOrthogonalSeries_shift_sub_of_identity μ n
    (X_mul_monicMomentPolynomial_shift μ hpos hshift n)
    (isUnit_iff_ne_zero.mpr (hpos (n + 1)).det_pos.ne')
    (momentNormSq_pos μ n (hpos (n + 1))).ne'
    (momentNormSq_pos (fun k => μ (k + 1)) n (hshift (n + 1))).ne'
    (momentNormSq_pos μ (n + 1) (hpos (n + 2))).ne'

/-- The second Christoffel identity gives the next even Euler–Gauss step. -/
theorem momentOrthogonalSeries_succ_sub_shift (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) (n : ℕ) :
    momentOrthogonalSeries μ (n + 1) -
        momentOrthogonalSeries (fun k => μ (k + 1)) n =
      PowerSeries.C (momentStieltjesEven μ (n + 1)) * PowerSeries.X *
        momentOrthogonalSeries (fun k => μ (k + 1)) (n + 1) := by
  exact momentOrthogonalSeries_succ_sub_of_identity μ n
    (monicMomentPolynomial_eq_shift_add μ hpos hshift n)
    (isUnit_iff_ne_zero.mpr (hshift (n + 1)).det_pos.ne')
    (momentNormSq_pos μ (n + 1) (hpos (n + 2))).ne'
    (momentNormSq_pos (fun k => μ (k + 1)) n (hshift (n + 1))).ne'
    (momentNormSq_pos (fun k => μ (k + 1)) (n + 1) (hshift (n + 2))).ne'

end Polynomial
