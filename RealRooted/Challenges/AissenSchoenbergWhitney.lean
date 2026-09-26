import RealRooted.AissenSchoenbergWhitney

/-!
# Aissen--Schoenberg--Whitney challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "aissen-schoenberg-whitney"
authors = ["Aissen", "Schoenberg", "Whitney"]
years = [1952]

[[definitions]]
name = "RealRooted.IsPolyaFreqSeq"
module = "RealRooted.AissenSchoenbergWhitneyBase"

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.forwardTheorem"

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.reverseTheorem"
-->

<!-- realrooted-catalog-content -->
# Aissen–Schoenberg–Whitney

A finite nonnegative sequence is Pólya-frequency exactly when its generating
polynomial has only real nonpositive roots. The selected theorems prove both
directions for polynomial coefficients.

## References

M. Aissen, I. J. Schoenberg, and A. M. Whitney, “On the generating functions
of totally positive sequences. I,” *Journal of Analyse Mathématique* 2 (1952),
93–103.  See the
[Pólya-frequency overview on symmetricfunctions.com](https://www.symmetricfunctions.com/polyaFrequency.htm#aissenSchoenbergWhitney).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/polyaFrequency.htm#aissenSchoenbergWhitney

Original publication: M. Aissen, I. J. Schoenberg, and A. M. Whitney,
"On the generating functions of totally positive sequences. I",
J. Analyse Math. 2 (1952), 93--103.

This module exposes the proved forward and reverse Aissen--Schoenberg--Whitney
directions.  The Toeplitz/PF infrastructure remains in
`RealRooted.AissenSchoenbergWhitney`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace AissenSchoenbergWhitney

/-- Checked forward ASW theorem: PF coefficients imply real non-positive roots. -/
theorem forwardTheorem :
    ∀ {p : ℝ[X]}, IsPolyaFreqSeq p.coeff →
      p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0 :=
  RealRooted.aissenSchoenbergWhitneyForward

/-- Reverse ASW theorem: real non-positive roots imply PF coefficients. -/
theorem reverseTheorem :
    ∀ {p : ℝ[X]},
      HasNonnegCoeffs p →
      (p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) →
      IsPolyaFreqSeq p.coeff :=
  fun hp ⟨hsplits, hroots⟩ =>
    RealRooted.aissenSchoenbergWhitney_reverse hp hsplits hroots

end AissenSchoenbergWhitney
end Challenges
end RealRooted
