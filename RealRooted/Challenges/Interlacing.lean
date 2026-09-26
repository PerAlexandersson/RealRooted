import RealRooted.Basic.ProperPosition

/-!
# Interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "interlacing"

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

The project uses `StrictInterl f g` for proper position with `f` on the left:
both polynomials must be nonzero and split over the reals, and their ordered
roots either alternate at equal degree or interlace when the right polynomial
has one larger degree.  Thus the right endpoint has the rightmost root in the
differ-by-one case.  The inequalities are weak, so shared roots and repeated
roots are allowed; the word `Strict` excludes the zero-polynomial case and
does not mean that all roots are distinct.

`Interl f g` is the zero-aware relation: either polynomial may be zero, or the
nonzero pair satisfies `StrictInterl`.  `Interlaces g f` describes the case in
which the degrees differ by one.  Its first argument is the shorter polynomial;
the second has degree exactly one larger and contains the alternating root
list.

## References

Steve Fisk, [“Polynomials, roots, and
interlacing,”](https://arxiv.org/abs/math/0612833) arXiv:math/0612833 (2006).
The definitions and root-list conventions are formalized in
`RealRooted.Basic.ProperPosition`, with the canonical list interleaving
bridges in `RealRooted.Basic`.
<!-- /realrooted-catalog-content -->
-/
