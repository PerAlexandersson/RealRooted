/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentChristoffel
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentSeriesRecurrence
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.EulerPaired

/-!
# Strict Hankel positivity gives a positive Stieltjes fraction

The monic orthogonal polynomials for the original and shifted moments give
paired Euler–Gauss series. Their positive norm ratios therefore produce the
actual formal continued-fraction expansion. Merely defining determinant
ratios or observing nonnegative coefficients would not give this identity.

This is the strict case of the classical moment/S-fraction criterion in
Sokal, "When does a hypergeometric function pFq belong to the Laguerre–Pólya
class LP+?", Appendix A, Proposition 7. Finite-rank moment families require
a separate terminating case.
-/

public section

namespace Polynomial

/-- Positive definiteness of every unshifted and shifted Hankel matrix yields
a strictly positive formal S-fraction, with even and odd numerators given by
the corresponding orthogonal norm ratios. -/
theorem exists_pos_stieltjesTail_of_hankel_posDef (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef) :
    ∃ a : ℕ → ℝ, (∀ k, 0 < a k) ∧
      (∀ n, a (2 * n) = momentStieltjesEven μ n ∧
        a (2 * n + 1) = momentStieltjesOdd μ n) ∧
      PowerSeries.mk μ = PowerSeries.C (μ 0) * PowerSeries.stieltjesTail a 0 := by
  obtain ⟨a, ha, hseries⟩ := PowerSeries.exists_stieltjesTail_of_paired
    (momentOrthogonalSeries_zero_sub_one μ hpos hshift)
    (momentOrthogonalSeries_shift_sub μ hpos hshift)
    (momentOrthogonalSeries_succ_sub_shift μ hpos hshift)
  refine ⟨a, ?_, ha, ?_⟩
  · intro k
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [(ha n).1]
      exact momentStieltjesEven_pos μ hpos hshift n
    · rw [(ha n).2]
      exact momentStieltjesOdd_pos μ hpos hshift n
  · have hm0 : μ 0 ≠ 0 := by
      simpa only [momentNormSq_zero] using (momentNormSq_pos μ 0 (hpos 1)).ne'
    rw [← hseries]
    ext k
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      coeff_momentOrthogonalSeries_zero]
    field_simp [hm0]

end Polynomial
