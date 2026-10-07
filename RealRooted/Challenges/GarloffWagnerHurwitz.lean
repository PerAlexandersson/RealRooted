import RealRooted.GarloffWagner.HurwitzStable

/-!
# Garloff–Wagner Hurwitz-stability challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "garloff-wagner-hurwitz"
authors = ["Garloff", "Wagner"]
years = [1996]

[[theorems]]
name = "RealRooted.IsHurwitzStable.hadamardProduct"
module = "RealRooted.GarloffWagner.HurwitzStable"
label = "Hadamard products of Hurwitz-stable polynomials are stable"
headline = true

[[theorems]]
name = "RealRooted.isHurwitzStable_oddEvenPolynomial_zero_left_iff"
module = "RealRooted.GarloffWagner.HurwitzStable"
label = "q(x²) is Hurwitz stable iff q is a nonzero PF polynomial"

[[theorems]]
name = "RealRooted.IsHurwitzStable.isPFPolynomial_oddEvenPolynomial"
module = "RealRooted.GarloffWagner.HurwitzStable"
label = "Both parts of a Hurwitz-stable polynomial are PF"
-->

<!-- realrooted-catalog-content -->
# Hadamard products of Hurwitz-stable polynomials

A real polynomial is *Hurwitz stable* if its coefficients are nonnegative and it has no
zero with positive real part. The Hadamard product of $a = \sum_k a_k x^k$ and
$b = \sum_k b_k x^k$ is $a \ast b = \sum_k a_k b_k x^k$.

**Theorem (Garloff–Wagner).** If $a$ and $b$ are Hurwitz stable and $a \ast b \neq 0$,
then $a \ast b$ is Hurwitz stable.

The proof writes $a = q(x^2) + x\,p(x^2)$. By the Hermite–Biehler theorem, $a$ is Hurwitz
stable exactly when the odd and even parts interlace, $p \ll q$, or one of them vanishes
and the other is a PF polynomial (real-rooted with nonnegative coefficients). The
Hadamard product acts on the two parts separately, and both alternatives are preserved:
interlacing by Garloff and Wagner's theorem on Hadamard products of interlacing pairs, and
PF polynomials by Maló's theorem. The coefficient condition $a \ast b \neq 0$ excludes
products of polynomials with disjoint supports, which vanish.

## References

J. Garloff and D. G. Wagner, “Hadamard products of stable polynomials are stable,”
*Journal of Mathematical Analysis and Applications* 202 (1996), 797–809, Theorem 1. See
the [Hadamard-product overview](https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proof lives in
`RealRooted.GarloffWagner.HurwitzStable`; the interlacing and PF ingredients are on the
`hadamard-products` page, and the Hermite–Biehler correspondence on the
`hermite-biehler-hurwitz` page.
-/
