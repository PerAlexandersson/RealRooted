import RealRooted.NarayanaTransformation.Endpoints

/-!
# Narayana polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "narayana"

[[definitions]]
name = "RealRooted.narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Coefficients"

[[definitions]]
name = "RealRooted.narayanaTransform"
module = "RealRooted.NarayanaTransformation.Coefficients"

[[theorems]]
name = "RealRooted.splits_narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Endpoints"

[[theorems]]
name = "RealRooted.narayanaPolynomialRootLocation"
module = "RealRooted.NarayanaTransformation.Endpoints"

[[theorems]]
name = "RealRooted.narayanaTransformPreservesPF"
module = "RealRooted.NarayanaTransformation.Endpoints"
-->

<!-- realrooted-catalog-content -->
# Generalized Narayana polynomials

The canonical family in this page is the two-parameter polynomial

`Nₘ,ₙ(x) = Σₖ (binom(n,k) binom(n+m,k) / binom(m+k,k)) xᵏ`,

with the sum represented in Lean by `narayanaPolynomial m n`.  The associated
`narayanaTransform m` sends the monomial `X^k` to `Nₘ,ₖ`.  The selected
theorems prove real splitting for every generalized Narayana polynomial,
package the family as Pólya-frequency polynomials, and prove preservation of
Pólya-frequency polynomials under this transform.

These are the generalized transformation results developed in
`RealRooted.NarayanaTransformation`.  They are distinct from the
recurrence-facing conditional family in
`RealRooted.CombinatorialExamples.Narayana`; the two are not identified by
this catalogue.

## References

The coefficient normalization is the generalized Narayana polynomial of
Mao–Wang, Eq. (1.2), and the root-location input is the
Dominici–Johnston–Jordaan theorem used as Lemma 2.5 in the transformation
development.  The precise citations and formal recurrence interfaces are
recorded in the imported `RealRooted.NarayanaTransformation` modules.
<!-- /realrooted-catalog-content -->
-/
