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

`narayanaPolynomial m n` is the generalized Narayana polynomial with
parameters `(m, n)`. These polynomials are Pólya-frequency, and the associated
Narayana transform preserves Pólya-frequency polynomials.

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
