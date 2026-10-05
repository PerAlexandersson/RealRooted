import RealRooted.Wagner.NonpositiveRoots

/-!
# Wagner challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "wagner"
authors = ["Wagner"]
years = [1992]

[[theorems]]
name = "RealRooted.Challenges.Wagner.commonRight_add"
label = "A sum of polynomials interlacing h interlaces h"

[[theorems]]
name = "RealRooted.Challenges.Wagner.commonLeft_add"
label = "The common-left version"

[[theorems]]
name = "RealRooted.Challenges.Wagner.mulX_iff"
label = "Multiplication by x reverses interlacing"
-->

<!-- realrooted-catalog-content -->
# Wagner’s lemma

If $f$ and $g$ have positive leading coefficients and both interlace $h$,
then $f + g$ interlaces $h$. Likewise, if $f$ and $g$ have positive leading
coefficients and $h$ interlaces both, then $h$ interlaces $f + g$. For
polynomials with nonpositive roots and positive leading coefficients whose
degrees differ by one, multiplication by $X$ reverses the interlacing
orientation.

## References

D. G. Wagner, “Total positivity of Hadamard products,” *Journal of
Mathematical Analysis and Applications* 163 (1992), 459–483.  See the
[contextual statement on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#wagnerLemma).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#wagnerLemma

Original publication: D. G. Wagner, "Total positivity of Hadamard products",
J. Math. Anal. Appl. 163 (1992), 459--483.

This module records the three forms of Wagner's lemma used in the catalog.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Wagner

/-- Wagner (1): if `f` and `g` have positive leading coefficients and both
interlace `h`, then `f + g` interlaces `h`. -/
theorem commonRight_add {f g h : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfh : StrictInterl f h) (hgh : StrictInterl g h) :
    StrictInterl (f + g) h :=
  RealRooted.StrictInterl.add_of_right_of_posLeadingCoeff hfh hgh hf hg

/-- Wagner (2): if `f` and `g` have positive leading coefficients and `h`
interlaces both, then `h` interlaces `f + g`. -/
theorem commonLeft_add {f g h : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hhf : StrictInterl h f) (hhg : StrictInterl h g) :
    StrictInterl h (f + g) := by
  simpa using RealRooted.StrictInterl.sum_left_of_common_left_signed [f, g] h
    (by simp [hhf, hhg]) (by simp [hf, hg]) (by simp)

/-- Wagner (3): `f` interlaces `g` if and only if `g` interlaces `X * f`.

This is the Lean orientation of the catalog statement
`g \interl f` iff `f \interl t g`: here `f` is the shorter polynomial and
`g` is the longer one. -/
theorem mulX_iff {f g : ℝ[X]}
    (hf : RealRooted.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Wagner.HasNonposRootsPosLeading g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g (X * f) :=
  RealRooted.Wagner.mulX_iff hf hg hdeg

end Wagner
end Challenges
end RealRooted
