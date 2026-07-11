import RealRooted.AissenSchoenbergWhitney

/-!
# Aissen--Schoenberg--Whitney challenge entry point

Human statement:
https://www.symmetricfunctions.com/polyaFrequency.htm#aissenSchoenbergWhitney

Original publication: M. Aissen, I. J. Schoenberg, and A. M. Whitney,
"On the generating functions of totally positive sequences. I",
J. Analyse Math. 2 (1952), 93--103.

This module exposes the forward Aissen--Schoenberg--Whitney target and the
proved reverse direction.  The Toeplitz/PF infrastructure remains in
`RealRooted.AissenSchoenbergWhitney`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace AissenSchoenbergWhitney

/-- Challenge-facing name for the Toeplitz total-nonnegativity condition on
the coefficient sequence of a polynomial. -/
abbrev CoefficientsPolyaFrequency (p : ℝ[X]) : Prop :=
  IsPolyaFreqSeq p.coeff

/-- Challenge-facing name for having only real nonpositive roots. -/
abbrev HasRealNonposRoots (p : ℝ[X]) : Prop :=
  p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Forward ASW target: PF coefficients imply real non-positive roots. -/
theorem forwardTarget {p : ℝ[X]}
    (hpf : CoefficientsPolyaFrequency p) :
    HasRealNonposRoots p :=
  RealRooted.aissenSchoenbergWhitneyForward hpf

/-- Reverse ASW theorem: real non-positive roots imply PF coefficients. -/
theorem reverseTheorem :
    ∀ {p : ℝ[X]},
      HasNonnegCoeffs p →
      HasRealNonposRoots p →
      CoefficientsPolyaFrequency p :=
  fun hp ⟨hsplits, hroots⟩ =>
    RealRooted.aissenSchoenbergWhitney_reverse hp hsplits hroots

end AissenSchoenbergWhitney
end Challenges
end RealRooted
