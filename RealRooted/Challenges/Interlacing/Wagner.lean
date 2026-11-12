module

public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.PosCombo
public import RealRooted.Wagner.LeftSum
public import RealRooted.Wagner.NonpositiveRoots
public import RealRooted.WagnerRightSum
public import RealRooted.WagnerX.ListInterlacing
public import RealRooted.WagnerX.NonnegativeRoots
public import RealRooted.WeightedSum

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
name = "RealRooted.StrictInterl.add_of_right_of_posLeadingCoeff"
module = "RealRooted.WagnerRightSum"
label = "A sum of polynomials interlacing h interlaces h"
headline = true

[[theorems]]
name = "RealRooted.StrictInterl.add_of_left"
module = "RealRooted.Wagner.LeftSum"
label = "The common-left version"

[[theorems]]
name = "RealRooted.strictInterl_iff_mul_X_of_roots_nonpos"
module = "RealRooted.WagnerX.NonnegativeRoots"
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
name = "RealRooted.strictInterl_chain_of_consecutive_of_endpoint"
module = "RealRooted.CommonInterleaver.RootDesc"
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

Interlacing is preserved by sums of polynomials with a common interlacing partner, and
multiplication by $x$ reverses it for polynomials with nonpositive roots.

## Results

We write $f\ll g$ if $f$ interlaces $g$ as on the
[interlacing page](/RealRooted/concepts/interlacing/); common roots are allowed unless stated.
Polynomials $f,g$ below have positive leading coefficients where stated.

**Theorem (Wagner's lemma).** Let $f,g$ have positive leading coefficients.

1. If $f\ll h$ and $g\ll h$, then $f+g\ll h$.
2. If $h\ll f$ and $h\ll g$, then $h\ll f+g$.
3. If all real roots of $f$ and $g$ are nonpositive, then $f\ll g$ if and only if $g\ll xf$.

No degree condition is needed in (3): both $\deg g=\deg f$ and $\deg g=\deg f+1$ occur. If
$f\ll g$ and both have nonnegative coefficients, then $g\ll xf$.

**Proposition (finite sums).** Let $f_1,\dots,f_k$ have positive leading coefficients with
$f_i\ll h$ for all $i$, and let $a_1,\dots,a_k\ge0$, not all zero. Then $\sum_ia_if_i\ll h$. In
particular $\sum_if_i\ll h$ for $k\ge1$. If $f+g$ has no root in common with $h$, part (1) holds
under the same hypotheses.

**Proposition (nonnegative combinations).** Let $f\ll g$ have positive leading coefficients and
let $a,b\ge0$ be not both zero. Then $f\ll af+bg$ and $af+bg\ll g$.

**Proposition (common factor).** For $r\in\mathbb R$, $f\ll g$ if and only if
$(x-r)f\ll(x-r)g$.

**Proposition (chains).** If $F_a\ll F_{a+1}\ll\dots\ll F_b$ and $F_a\ll F_b$, then
$F_i\ll F_j$ for all $a\le i\le j\le b$.

## Relation to SymCat

The common-right addition clause is [Wagner’s lemma](sf:wagnerLemma) on symmetricfunctions.com.

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
