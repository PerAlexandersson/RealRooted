import RealRooted.Basic.ProperPosition

/-!
# Interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "interlacing"
authors = ["Fisk"]
years = [2006]

[[definitions]]
name = "RealRooted.StrictInterl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing f ≪ g"

[[definitions]]
name = "RealRooted.Interl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing, allowing zero polynomials"

[[definitions]]
name = "RealRooted.Interlaces"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing with degrees differing by one"
-->

<!-- realrooted-catalog-content -->
# Polynomial interlacing

Let $f$ and $g$ be nonzero real-rooted polynomials with roots
$s_1 \leq \dotsb \leq s_k$ and $r_1 \leq \dotsb \leq r_m$, listed with multiplicity. We write
$f \ll g$ (`StrictInterl f g`) if either

- $m = k + 1$ and $r_1 \leq s_1 \leq r_2 \leq s_2 \leq \dotsb \leq s_k \leq r_{k+1}$, or
- $m = k$ and $s_1 \leq r_1 \leq s_2 \leq r_2 \leq \dotsb \leq s_k \leq r_k$.

In both cases $g$ has the largest root. Shared and repeated roots are allowed.
The relation `Interl f g` also holds when $f$ or $g$ is zero, and
`Interlaces f g` is the case $m = k + 1$ alone.

## References

Steve Fisk, [“Polynomials, roots, and
interlacing,”](https://arxiv.org/abs/math/0612833) arXiv:math/0612833 (2006).
See also the
[interlacing overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacesPolynomial).
<!-- /realrooted-catalog-content -->
-/
