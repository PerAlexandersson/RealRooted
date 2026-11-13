module

import RealRooted.BrandenVecchi.ChowInfinitePF
import RealRooted.BrandenVecchi.ChowSignedWords
import RealRooted.BrandenVecchi.ChowTotallyNonneg
import RealRooted.BrandenVecchi.ChowZeroPrefix
import RealRooted.BrandenVecchi.SmirnovSpecialization

/-!
# Chow polynomials of totally nonnegative matrices

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-vecchi"
formalized = "2026-09-12"
tags = []
references = [
  "BrandenVecchi2025x",
]
authors = ["Brändén", "Vecchi"]
years = [2025]

[[definitions]]
name = "RealRooted.BrandenVecchi.chowDerangement"
module = "RealRooted.BrandenVecchi.Chow"
label = "Chow derangement polynomials"

[[definitions]]
name = "RealRooted.BrandenVecchi.chowPolynomial"
module = "RealRooted.BrandenVecchi.Chow"
label = "Chow polynomials of a lower-triangular matrix"

[[definitions]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Chow polynomials of a Pólya frequency symbol"

[[definitions]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow"
module = "RealRooted.BrandenVecchi.ChowSupersymmetric"
label = "Chow polynomials of a supersymmetric symbol"

[[definitions]]
name = "RealRooted.BrandenVecchi.scaledZeroPrefix"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "A sequence shifted by a zero prefix and scaled"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_nonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow polynomials have nonnegative coefficients"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Each Chow polynomial is zero or real-rooted"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowDerangement_nonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow derangement polynomials have nonnegative coefficients"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowDerangement_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Each Chow derangement polynomial is zero or real-rooted"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Consecutive Chow polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_chowDerangement_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "The Chow polynomial c_n interlaces the Chow derangement polynomial d_n"

[[theorems]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow_isPFPolynomial"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Pólya frequency symbols give Pólya frequency Chow polynomials"

[[theorems]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow_interl_succ"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Consecutive Chow polynomials of a Pólya frequency symbol interlace"

[[theorems]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow_eq_finiteSignedWordEnumerator"
module = "RealRooted.BrandenVecchi.ChowSignedWords"
label = "Chow polynomials of finite supersymmetric symbols are signed-word enumerators"

[[theorems]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow_replicate_one_nil_eq_smirnov"
module = "RealRooted.BrandenVecchi.SmirnovSpecialization"
label = "Chow polynomials of (1+z)^m are Smirnov word descent polynomials"

[[theorems]]
name = "RealRooted.BrandenVecchi.three_zero_prefix_constant_isPolyaFreqSeq"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "The sequence 0, 0, 0, 1, 1, 1, ... is a Pólya frequency sequence"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_three_zero_prefix_six_not_splits"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "For the sequence 0, 0, 0, 1, 1, ..., c_6 = x² + x + 1 is not real-rooted"
-->

<!-- realrooted-catalog-content -->
# Chow polynomials of totally nonnegative matrices

Chow polynomials and Chow derangement polynomials of a lower-unitriangular totally nonnegative
matrix are real-rooted or zero, consecutive Chow polynomials interlace, and each Chow polynomial
interlaces the Chow derangement polynomial of the same index.

## Results

We use the [zero-aware interlacing convention](rr:about). For a lower-triangular matrix $A$, the
*Chow derangement polynomials* are
$d_0=1$ and
$$
d_n=x\,S_{n-1}\Bigl(\sum_{k<n}A(n,k)\,d_k\Bigr),\qquad
S_m(q)=\frac{x^mq(1/x)-q}{x-1}\quad(n\ge1),
$$
and the *Chow polynomials* are $c_n=\sum_{k\le n}A(n,k)\,d_k$. For the incidence data of a
poset these generalize the Chow polynomials of matroids and posets; see the
[Chow-polynomial definition on symmetricfunctions.com](sf:chowPolynomialDefinition).

**Theorem (Brändén–Vecchi).** Let $A$ be lower unitriangular and totally nonnegative. Then for
every $n$ the polynomials $c_n$ and $d_n$ have nonnegative coefficients and each is zero or
real-rooted. Moreover $c_n\ll c_{n+1}$ and $c_n\ll d_n$ [@BrandenVecchi2025x].

**Theorem (Pólya frequency symbols).** Let $\gamma,\alpha_i,\beta_i\ge0$ with
$\sum_i(\alpha_i+\beta_i)<\infty$, and let $A$ be the lower Toeplitz matrix of the coefficients of
$$
e^{\gamma z}\,\prod_i(1+\alpha_iz)\Big/\prod_i(1-\beta_iz).
$$
Then every $c_n$ is a Pólya frequency polynomial, that is, it has nonnegative coefficients and
only real nonpositive roots, and $c_n\ll c_{n+1}$.

**Theorem (signed words).** For finite lists of real numbers $x_1,\dots,x_p$ and $y_1,\dots,y_q$,
let $A$ be the Toeplitz matrix of $\prod_i(1+x_iz)\big/\prod_j(1-y_jz)$. Then $c_n$ equals the
signed-word enumerator of length-$n$ words by descents and collisions, with the letter weights
$x_i$, $y_j$. For $x_1=\dots=x_m=1$ and no $y_j$, it is the descent polynomial of the Smirnov
words of length $n$ in $m$ letters.

**Proposition (zero prefix).** Let $a$ be the sequence $0,0,0,1,1,1,\dots$ and let $A$ be its
Toeplitz matrix. Then $a$ is a Pólya frequency sequence, but $c_6=x^2+x+1$ is not real-rooted.

## Proof

The proof uses the resolution of totally nonnegative matrices by Whitney elimination, as on the
[Brändén–Saud Leite page](rr:branden-leite).

## References

- [@BrandenVecchi2025x]
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.BrandenVecchi`.
-/
