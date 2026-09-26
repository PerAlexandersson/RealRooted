import RealRooted.NarayanaTransformation.Endpoints

/-!
# Narayana polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "narayana"
authors = ["Mao", "Wang", "Dominici", "Johnston", "Jordaan"]
years = [2013, 2026]

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

`N_{n,m}(x) = Σₖ (binom(n,k) binom(n+m,k) / binom(m+k,k)) xᵏ`,

represented in Lean by `narayanaPolynomial m n`, whose Lean arguments are in
the order `(m, n)`.  The associated `narayanaTransform m` sends the monomial
`X^k` to `N_{k,m}`.  The selected theorems prove real splitting for every
generalized Narayana polynomial,
package the family as Pólya-frequency polynomials, and prove preservation of
Pólya-frequency polynomials under this transform.

These are the generalized transformation results developed in
`RealRooted.NarayanaTransformation`.  They are distinct from the
recurrence-facing conditional family in
`RealRooted.CombinatorialExamples.Narayana`; the two are not identified by
this catalog.

## References

The coefficient normalization is from Jianxi Mao and Lijie Wang, [“The
Narayana transformation,”](https://arxiv.org/abs/2607.01572) arXiv:2607.01572
(2026), Eq. (1.2).  The root-location input is D. Dominici, S. J. Johnston,
and K. Jordaan, [“Real zeros of 2F1 hypergeometric
polynomials,”](https://arxiv.org/abs/1301.4771) *Journal of Computational and
Applied Mathematics* 247 (2013), 152–161, used as Lemma 2.5 in the
transformation development.  See also the
[Narayana real-rootedness examples on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedCatalan.htm#ex:narayanaSturm).
<!-- /realrooted-catalog-content -->
-/
