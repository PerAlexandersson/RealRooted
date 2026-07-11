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

/-- Forward ASW target: PF coefficients imply real non-positive roots. -/
theorem forwardTarget {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n ↦ p.coeff n)) :
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0 :=
  RealRooted.aissenSchoenbergWhitneyForward hpf

/-- Reverse ASW theorem: real non-positive roots imply PF coefficients. -/
theorem reverseTheorem {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p)
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsPolyaFreqSeq (fun n ↦ p.coeff n) :=
  RealRooted.aissenSchoenbergWhitney_reverse hpnn hsplits hroots

end AissenSchoenbergWhitney
end Challenges
end RealRooted
