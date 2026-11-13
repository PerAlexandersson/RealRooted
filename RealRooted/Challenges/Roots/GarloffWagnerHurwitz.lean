module

import RealRooted.GarloffWagner.HurwitzStable

/-!
# Hadamard products of Hurwitz-stable polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "garloff-wagner-hurwitz"
formalized = "2026-06-10"
tags = []
references = [
  "GarloffWagner1996",
]
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

The coefficientwise product of two Hurwitz-stable real polynomials is Hurwitz stable unless it
vanishes.

## Results

A real polynomial is *Hurwitz stable* if its coefficients are nonnegative and it has no zero with
positive real part. The Hadamard product of $a=\sum_k a_kx^k$ and $b=\sum_k b_kx^k$ is
$a\ast b=\sum_k a_kb_kx^k$.

**Theorem (Garloff–Wagner).** [@GarloffWagner1996, Thm. 1] If $a$ and $b$ are Hurwitz stable
and $a\ast b\ne0$, then $a\ast b$ is Hurwitz stable.

**Proposition (even and odd parts).** Write $a=q(x^2)+x\,p(x^2)$. If $a$ is Hurwitz stable,
then $p$ and $q$ are Pólya frequency polynomials (real-rooted with nonnegative coefficients).
For real $q$, the polynomial $q(x^2)$ is Hurwitz stable if and only if $q\ne0$ and $q$ is a
Pólya frequency polynomial.

## Proof

By the Hermite–Biehler theorem, $a$ is Hurwitz stable exactly when $p\ll q$ with both nonzero
and nonnegative coefficients, or one of $p,q$ vanishes and the other is a Pólya frequency
polynomial. The Hadamard product acts on the two parts separately, and both alternatives are
preserved: interlacing by [@GarloffWagner1996, Thm. 4(b)], and Pólya frequency polynomials by
the Schur–Malo theorem. The condition $a\ast b\ne0$ excludes products of polynomials with
disjoint supports.

## References

See [@GarloffWagner1996, Thm. 1] and the
[Hadamard-product overview](sf:hadamardProductTheorems) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proof lives in
`RealRooted.GarloffWagner.HurwitzStable`; the interlacing and PF ingredients are on the
`hadamard-products` page, and the Hermite–Biehler correspondence on the
`hermite-biehler-hurwitz` page.
-/
