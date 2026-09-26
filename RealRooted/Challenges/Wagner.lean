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

[[theorems]]
name = "RealRooted.Challenges.Wagner.commonLeft_add"

[[theorems]]
name = "RealRooted.Challenges.Wagner.mulX_iff"
-->

<!-- realrooted-catalog-content -->
# Wagner’s lemma

If `f` and `g` both interlace `h`, then `f + g` interlaces `h`; the analogous
common-left statement also holds. For polynomials with nonpositive roots,
multiplication by `X` reverses the interlacing orientation.

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

/-- Wagner (1): if `f` and `g` both interlace `h`, then `f + g` interlaces
`h`. -/
theorem commonRight_add {f g h : ℝ[X]}
    (hf : RealRooted.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Wagner.HasNonposRootsPosLeading g)
    (hfh : StrictInterl f h) (hgh : StrictInterl g h) :
    StrictInterl (f + g) h :=
  RealRooted.Wagner.commonRight_add hf hg hfh hgh

/-- Wagner (2): if `h` interlaces both `f` and `g`, then `h` interlaces
`f + g`.

This is the checked common-left form used by the catalog.  The reusable proof
is in `RealRooted.Wagner.NonpositiveRoots`; the separate theorem
`commonLeft_add_checked` exposes the lower-level algebraic interface. -/
theorem commonLeft_add {f g h : ℝ[X]}
    (hf : RealRooted.Wagner.HasNonposRootsPosLeading f)
    (hg : RealRooted.Wagner.HasNonposRootsPosLeading g)
    (hhf : StrictInterl h f) (hhg : StrictInterl h g) :
    StrictInterl h (f + g) :=
  RealRooted.Wagner.commonLeft_add hf hg hhf hhg

/-- Checked two-summand common-left form currently available in the core
Wagner module. -/
theorem commonLeft_add_checked :
    ∀ {f g h : ℝ[X]},
      (hhf : StrictInterl h f) → (hhg : StrictInterl h g) →
      (hf_pos : HasPosLeadingCoeff f) → (hg_pos : HasPosLeadingCoeff g) →
      (hfg_ne : (f + g) ≠ 0) → (hfg_splits : (f + g).Splits) →
      (hcop : IsCoprime f g) →
      StrictInterl h (f + g) :=
  RealRooted.Wagner.commonLeft_add_checked

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
