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
label = "Generalized Narayana polynomials"

[[definitions]]
name = "RealRooted.narayanaTransform"
module = "RealRooted.NarayanaTransformation.Coefficients"
label = "Narayana transform"

[[theorems]]
name = "RealRooted.splits_narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.narayanaPolynomialRootLocation"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are Pólya-frequency"

[[theorems]]
name = "RealRooted.narayanaTransformPreservesPF"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "The Narayana transform preserves Pólya-frequency polynomials"
headline = true
-->

<!-- realrooted-catalog-content -->
# Generalized Narayana polynomials

For $m, n \geq 0$, the generalized Narayana polynomial is

$$N_{n,m}(x) = \sum_{k=0}^{n} \frac{\binom{n}{k}\binom{n+m}{k}}{\binom{m+k}{k}}\, x^k.$$

For $m = 1$ the coefficients are Narayana numbers; for example
$N_{2,1}(x) = 1 + 3x + x^2$. These polynomials are Pólya-frequency, and the Narayana transform
$x^n \mapsto N_{n,m}(x)$ preserves Pólya-frequency polynomials.

## References

The coefficient normalization is from Jianxi Mao and Lijie Wang, [“The
Narayana transformation,”](https://arxiv.org/abs/2607.01572) arXiv:2607.01572
(2026), Eq. (1.2).  The root-location input is D. Dominici, S. J. Johnston,
and K. Jordaan, [“Real zeros of 2F1 hypergeometric
polynomials,”](https://arxiv.org/abs/1301.4771) *Journal of Computational and
Applied Mathematics* 247 (2013), 152–161, which is Lemma 2.5 in Mao–Wang.
See also the
[Narayana real-rootedness examples on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedCatalan.htm#ex:narayanaSturm).
<!-- /realrooted-catalog-content -->
-/
