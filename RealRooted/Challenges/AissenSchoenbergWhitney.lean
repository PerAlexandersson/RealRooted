import RealRooted.AissenSchoenbergWhitney

/-!
# Aissen--Schoenberg--Whitney challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "aissen-schoenberg-whitney"

[[definitions]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.CoefficientsPolyaFrequency"

[[definitions]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.HasRealNonposRoots"

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.forwardTheorem"

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.reverseTheorem"
-->

<!-- realrooted-catalog-content -->
# Aissen–Schoenberg–Whitney

For a real polynomial `p`, `CoefficientsPolyaFrequency p` abbreviates the
Pólya-frequency condition on its coefficient sequence.  `HasRealNonposRoots p`
packages real splitting together with the assertion that every root is
nonpositive.  The forward theorem proves that Pólya-frequency coefficients
force this real nonpositive-root property.  The reverse theorem proves the
converse under the explicit nonnegative-coefficient hypothesis used by the
formalization.

The catalog intentionally selects the checked forward and reverse theorems;
the internal `forwardTarget` spelling is not itself a catalog entry.

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

/-- Challenge-facing name for the Toeplitz total-nonnegativity condition on
the coefficient sequence of a polynomial. -/
abbrev CoefficientsPolyaFrequency (p : ℝ[X]) : Prop :=
  IsPolyaFreqSeq p.coeff

/-- Challenge-facing name for having only real nonpositive roots. -/
abbrev HasRealNonposRoots (p : ℝ[X]) : Prop :=
  p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Compatibility proposition for the forward ASW implication. -/
abbrev forwardTarget : Prop :=
  ∀ {p : ℝ[X]}, CoefficientsPolyaFrequency p → HasRealNonposRoots p

/-- Checked forward ASW theorem: PF coefficients imply real non-positive roots. -/
theorem forwardTheorem : forwardTarget :=
  fun hpf => RealRooted.aissenSchoenbergWhitneyForward hpf

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
