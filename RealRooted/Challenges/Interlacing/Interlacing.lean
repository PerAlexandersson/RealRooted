module

public import RealRooted.Basic.ProperPosition

/-!
# Interlacing of real-rooted polynomials

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
label = "Interlaces is interlacing with a degree increase"
headline = true

[[theorems]]
name = "RealRooted.StrictInterl.natDegree_eq_or_eq_succ"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing polynomials differ in degree by at most one"

[[theorems]]
name = "RealRooted.StrictInterl.toInterl"
module = "RealRooted.Basic.ProperPosition"
label = "f ≪ g implies Interl f g, the relation allowing zero polynomials"
-->

<!-- realrooted-catalog-content -->
# Interlacing of real-rooted polynomials

Two nonzero real-rooted polynomials interlace if their roots alternate, with the second of the
same degree as the first or of one higher degree.

## Results

Let $f$ and $g$ be nonzero real-rooted polynomials with roots $s_1\le\dotsb\le s_k$ and
$r_1\le\dotsb\le r_m$, listed with multiplicity. We write $f\ll g$ (`StrictInterl f g`), and say
that $f$ *interlaces* $g$, if either

- $m=k+1$ and $r_1\le s_1\le r_2\le s_2\le\dotsb\le s_k\le r_{k+1}$, or
- $m=k$ and $s_1\le r_1\le s_2\le r_2\le\dotsb\le s_k\le r_k$.

In both cases $g$ has the largest root. Common roots and repeated roots are allowed.

The relation `Interl f g` holds if $f=0$, $g=0$ or $f\ll g$. The relation `Interlaces f g` is
the first case alone. A list $p_0,p_1,\dotsc$ of polynomials is a *Sturm sequence*
(`IsSturmSeq`) if `Interlaces` holds for each consecutive pair $p_{i+1},p_i$; the degrees then
drop by one at each step.

**Theorem.** If $f\ll g$, then $\deg g=\deg f$ or $\deg g=\deg f+1$. Moreover `Interlaces f g`
holds if and only if $f\ll g$ and $\deg g=\deg f+1$.

## References

See [@Fisk2006x] and the
[interlacing overview on symmetricfunctions.com](sf:interlacesPolynomial).
<!-- /realrooted-catalog-content -->
-/

