module

public import RealRooted.Basic.ProperPosition

/-!
# Interlacing

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "interlacing"
formalized = "2026-10-05"
tags = []
references = [
  "Fisk2006x",
]
authors = ["Fisk"]
years = [2006]

[[definitions]]
name = "RealRooted.StrictInterl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing f ≪ g of nonzero real-rooted polynomials"

[[definitions]]
name = "RealRooted.Interl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing, allowing zero polynomials"

[[definitions]]
name = "RealRooted.Interlaces"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing with degrees differing by one"

[[definitions]]
name = "RealRooted.IsSturmSeq"
module = "RealRooted.Basic.ProperPosition"
label = "Sturm sequence"

[[theorems]]
name = "RealRooted.Interlaces.iff_strictInterl_and_natDegree"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing with a degree gap of one"
headline = true

[[theorems]]
name = "RealRooted.StrictInterl.natDegree_eq_or_eq_succ"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing polynomials differ in degree by at most one"

[[theorems]]
name = "RealRooted.StrictInterl.toInterl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing implies interlacing in the sense allowing zero polynomials"
-->

<!-- realrooted-catalog-content -->
# Interlacing

Two real-rooted polynomials interlace if their roots alternate. Interlacing is the standard
tool for proving that a sequence of polynomials is real-rooted. The convention below is used
throughout the catalog; a page that departs from it says so.

## Results

Let $f$ and $g$ be nonzero real-rooted polynomials with roots $s_1\le\dotsb\le s_k$ and
$r_1\le\dotsb\le r_m$, listed with multiplicity. We say that $f$ *interlaces* $g$, and write
$f\ll g$, if either

- $m=k+1$ and $r_1\le s_1\le r_2\le s_2\le\dotsb\le s_k\le r_{k+1}$, or
- $m=k$ and $s_1\le r_1\le s_2\le r_2\le\dotsb\le s_k\le r_k$.

Thus $g$ has the largest root, and common and repeated roots are allowed. Some statements also
allow $f=0$ or $g=0$; the zero polynomial then interlaces every polynomial and is interlaced by
every polynomial. A sequence $p_0,p_1,\dotsc$ is a *Sturm sequence* if $p_{i+1}\ll p_i$ and
$\deg p_{i+1}=\deg p_i-1$ for every $i$.

**Theorem.** If $f\ll g$, then $\deg g=\deg f$ or $\deg g=\deg f+1$. The first alternative of
the definition holds exactly when $f\ll g$ and $\deg g=\deg f+1$.

## Use

By [Obreschkoff's theorem](rr:obreschkoff), $f\ll g$ or $g\ll f$ holds exactly when every real
linear combination of $f$ and $g$ is real-rooted. Interlacing sequences arise from
[three-term recurrences](rr:favard) and from [principal submatrices](rr:cauchy-interlacing),
interlacing is preserved by [differential operators with real-rooted symbol](rr:hermite-poulain),
and families with a [common interleaver](rr:common-interleavers) have real-rooted sums.

## References

[@Fisk2006x]. See also [interlacing on symmetricfunctions.com](sf:interlacesPolynomial).
<!-- /realrooted-catalog-content -->
-/

