import RealRooted.CommonInterleaver.RootDesc
import RealRooted.PosCombo
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
label = "Multiplication by x reverses interlacing, in either degree pattern"

[[theorems]]
name = "RealRooted.StrictInterl.nonneg_combo_left"
module = "RealRooted.PosCombo"
label = "If f ≪ g, then f ≪ af + bg for a, b ≥ 0"

[[theorems]]
name = "RealRooted.StrictInterl.nonneg_combo_right"
module = "RealRooted.PosCombo"
label = "If f ≪ g, then af + bg ≪ g for a, b ≥ 0"

[[theorems]]
name = "RealRooted.Challenges.Wagner.strictInterl_of_consecutive_of_endpoint"
label = "A consecutive chain with interlacing endpoints is an interlacing sequence"
-->

<!-- realrooted-catalog-content -->
# Wagner’s lemma

If $f$ and $g$ have positive leading coefficients and both interlace $h$,
then $f + g$ interlaces $h$. Likewise, if $f$ and $g$ have positive leading
coefficients and $h$ interlaces both, then $h$ interlaces $f + g$. If every
real root of $f$ and of $g$ is nonpositive, then $f$ interlaces $g$ if and only
if $g$ interlaces $Xf$. No degree condition is needed: both $\deg g = \deg f + 1$
and $\deg g = \deg f$ are covered.

Two consequences for nonnegative combinations: if $f$ interlaces $g$, both
have positive leading coefficients, and $a, b \ge 0$ are not both zero, then
$f$ interlaces $af + bg$, and $af + bg$ interlaces $g$.

Interlacing is not transitive, but a chain can be closed up. If
$F_a \ll F_{a+1} \ll \dots \ll F_b$ and also $F_a \ll F_b$, then
$F_i \ll F_j$ for all $a \le i \le j \le b$.

## References

D. G. Wagner, “Total positivity of Hadamard products,” *Journal of
Mathematical Analysis and Applications* 163 (1992), 459–483.  See the
[contextual statement on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#wagnerLemma).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#wagnerLemma

Original publication: D. G. Wagner, "Total positivity of Hadamard products",
J. Math. Anal. Appl. 163 (1992), 459--483.

This module records the three forms of Wagner's lemma used in the catalog,
the two nonnegative-combination consequences and the chain proposition.
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
    StrictInterl h (f + g) :=
  RealRooted.StrictInterl.add_of_left hhf hhg hf hg

/-- Wagner (3): if every real root of `f` and of `g` is nonpositive, then `f`
interlaces `g` if and only if `g` interlaces `X * f`.

This is the Lean orientation of the catalog statement
`g \interl f` iff `f \interl t g`.  No degree hypothesis is needed: either
side forces `g.natDegree = f.natDegree + 1` or `g.natDegree = f.natDegree`. -/
theorem mulX_iff {f g : ℝ[X]}
    (hf : ∀ r ∈ f.roots, r ≤ 0) (hg : ∀ r ∈ g.roots, r ≤ 0) :
    StrictInterl f g ↔ StrictInterl g (X * f) :=
  RealRooted.strictInterl_iff_mul_X_of_roots_nonpos hf hg

/-- **Wagner's chain proposition.** If `F a ≪ F (a + 1) ≪ ⋯ ≪ F b` and also
`F a ≪ F b`, then `F i ≪ F j` whenever `a ≤ i ≤ j ≤ b`. -/
theorem strictInterl_of_consecutive_of_endpoint {F : ℕ → ℝ[X]} {a b i j : ℕ}
    (hcons : ∀ k, a ≤ k → k < b → StrictInterl (F k) (F (k + 1)))
    (hext : StrictInterl (F a) (F b)) (hai : a ≤ i) (hij : i ≤ j) (hjb : j ≤ b) :
    StrictInterl (F i) (F j) :=
  strictInterl_chain_of_consecutive_of_endpoint F a b hcons hext i j hai hij hjb

end Wagner
end Challenges
end RealRooted
