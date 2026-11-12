module

import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.PosCombo
public import RealRooted.Wagner.NonpositiveRoots
import RealRooted.Wagner.LeftSum
import RealRooted.WagnerRightSum
import RealRooted.WagnerX.NonnegativeRoots
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Wagner challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "wagner"
formalized = "2026-07-10"
tags = []
references = [
  "Wagner1992",
]
authors = ["Wagner"]
years = [1992]

[[definitions]]
name = "RealRooted.weightedSum"
module = "RealRooted.WeightedSum"
label = "The weighted sum of a list of weight–polynomial pairs"

[[theorems]]
name = "RealRooted.Challenges.Wagner.commonRight_add"
label = "A sum of polynomials interlacing h interlaces h"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Wagner.commonLeft_add"
label = "The common-left version"

[[theorems]]
name = "RealRooted.Challenges.Wagner.mulX_iff"
label = "Multiplication by x reverses interlacing, in either degree pattern"

[[theorems]]
name = "RealRooted.StrictInterl.nonneg_combo_left"
module = "RealRooted.PosCombo"
label = "If f ≪ g, then f ≪ af + bg for a, b ≥ 0 not both zero"

[[theorems]]
name = "RealRooted.StrictInterl.nonneg_combo_right"
module = "RealRooted.PosCombo"
label = "If f ≪ g, then af + bg ≪ g for a, b ≥ 0 not both zero"

[[theorems]]
name = "RealRooted.Challenges.Wagner.strictInterl_of_consecutive_of_endpoint"
label = "A consecutive chain with interlacing endpoints is an interlacing sequence"

[[theorems]]
name = "RealRooted.StrictInterl.add_of_right_of_no_common_right"
module = "RealRooted.WagnerRightSum"
label = "Wagner's sum theorem when f + g has no root in common with h"

[[theorems]]
name = "RealRooted.StrictInterl.weightedSum_right_of_nonneg"
module = "RealRooted.WeightedSum"
label = "A nonnegative weighted sum of polynomials interlacing h interlaces h"

[[theorems]]
name = "RealRooted.StrictInterl.sum_right"
module = "RealRooted.WeightedSum"
label = "A finite sum of polynomials interlacing h interlaces h"

[[theorems]]
name = "RealRooted.strictInterl_mul_X_of_strictInterl_of_nonneg"
module = "RealRooted.WagnerX.NonnegativeRoots"
label = "If f ≪ g and both have nonnegative coefficients, then g ≪ xf"

[[theorems]]
name = "RealRooted.StrictInterl.mul_X_sub_C_both_iff"
module = "RealRooted.WagnerX.ListInterlacing"
label = "Multiplying both sides by a common linear factor preserves interlacing, and conversely"
-->

<!-- realrooted-catalog-content -->
# Wagner’s lemma

We write $f\ll g$ (`StrictInterl f g`) as on the
[interlacing page](/RealRooted/concepts/interlacing/).

If $f$ and $g$ have positive leading coefficients and both interlace $h$,
then $f + g$ interlaces $h$. Likewise, if $f$ and $g$ have positive leading
coefficients and $h$ interlaces both, then $h$ interlaces $f + g$. If every
real root of $f$ and of $g$ is nonpositive, then $f$ interlaces $g$ if and only
if $g$ interlaces $Xf$. No degree condition is needed: both $\deg g = \deg f + 1$
and $\deg g = \deg f$ are covered.

Two consequences for nonnegative combinations: if $f$ interlaces $g$, both
have positive leading coefficients, and $a, b \ge 0$ are not both zero, then
$f$ interlaces $af + bg$, and $af + bg$ interlaces $g$.

**Finite sums.** Wagner's lemma extends by induction to finitely many summands.
If $f_1,\dots,f_k$ all interlace $h$ and have positive leading coefficients, and
$a_1,\dots,a_k\ge0$ are weights, not all zero, then the weighted sum
$\sum_i a_i f_i$ interlaces $h$; in particular $\sum_i f_i \ll h$ for $k\ge1$.
The two-summand case needs no coprimeness hypothesis. It is proved by induction
on $\deg h$: a root shared by $h$ and $f+g$ is cancelled, and when there is no
shared root, the claim follows from the signs of $f+g$ at the roots of $h$.

**Multiplication by $x$ and by a linear factor.** If $f\ll g$ and both have
nonnegative coefficients, then $g\ll xf$. Multiplying both polynomials by a common
factor $x-r$ preserves interlacing, and cancelling such a factor reverses this: $f\ll g$
if and only if $(x-r)f\ll(x-r)g$.

Interlacing is not transitive, but a chain can be closed up. If
$F_a \ll F_{a+1} \ll \dots \ll F_b$ and also $F_a \ll F_b$, then
$F_i \ll F_j$ for all $a \le i \le j \le b$.

## Relation to SymCat

The headline formalizes the common-right addition clause of
[Wagner’s lemma](sf:wagnerLemma). The common-left addition and multiplication-by-$x$
clauses are published separately below.

## References

See [@Wagner1992] and the
[contextual statement on symmetricfunctions.com](sf:wagnerLemma).
<!-- /realrooted-catalog-content -->

Human statement:
sf:wagnerLemma

Original publication: D. G. Wagner, "Total positivity of Hadamard products",
J. Math. Anal. Appl. 163 (1992), 459--483.

This module records the three forms of Wagner's lemma used in the catalog,
the two nonnegative-combination consequences and the chain proposition.
-/

public section

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
