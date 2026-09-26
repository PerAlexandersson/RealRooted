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

[[definitions]]
name = "RealRooted.Interl"
module = "RealRooted.Basic.ProperPosition"

[[definitions]]
name = "RealRooted.Interlaces"
module = "RealRooted.Basic.ProperPosition"
-->

<!-- realrooted-catalog-content -->
# Polynomial interlacing

`StrictInterl f g` means that two nonzero real-rooted polynomials have
interlacing roots in the project’s oriented convention. `Interl f g` also
allows either polynomial to be zero. Shared and repeated roots are permitted.

## References

Steve Fisk, [“Polynomials, roots, and
interlacing,”](https://arxiv.org/abs/math/0612833) arXiv:math/0612833 (2006).
See also the
[interlacing overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacesPolynomial).
The definitions and root-list conventions are formalized in
`RealRooted.Basic.ProperPosition`, with the canonical list interleaving
bridges in `RealRooted.Basic`.
<!-- /realrooted-catalog-content -->
-/
