module

import RealRooted.CombinatorialExamples.BorosMoll
import RealRooted.CombinatorialExamples.BorosMoll.Infinite

/-!
# Log-concavity transform of the Boros–Moll rows

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "boros-moll-log-concavity-transform"
formalized = "2026-10-08"
tags = []
references = [
  "XieZhang2026InfiniteLogConcavity",
  "Branden2011b",
  "BorosMoll1999",
]
authors = ["Xie", "Zhang"]
years = [2026]

[[definitions]]
name = "RealRooted.BorosMoll.bmCoeff"
module = "RealRooted.CombinatorialExamples.BorosMoll.Basic"
label = "Boros–Moll coefficients"

[[definitions]]
name = "RealRooted.BorosMoll.bmM"
module = "RealRooted.CombinatorialExamples.BorosMoll.Basic"
label = "Generating polynomial of the log-concavity transform of a Boros–Moll row"

[[theorems]]
name = "RealRooted.BorosMoll.bmM_roots"
module = "RealRooted.CombinatorialExamples.BorosMoll"
label = "For n ≥ 1, M_n has degree n and n simple negative roots"

[[theorems]]
name = "RealRooted.BorosMoll.bmM_strictInterlaces_narayanaN"
module = "RealRooted.CombinatorialExamples.BorosMoll"
label = "The roots of M_n strictly interlace those of the Narayana polynomial N_n"
headline = true

[[definitions]]
name = "RealRooted.Branden.IsInfinitelyLogConcave"
module = "RealRooted.BrandenLC.Infinite"
label = "Infinitely log-concave: every iterate of the transform is nonnegative"

[[theorems]]
name = "RealRooted.Branden.IsPFPolynomial.logConcavityTransform"
module = "RealRooted.BrandenLC"
label = "The log-concavity transform preserves Pólya frequency polynomials"

[[theorems]]
name = "RealRooted.Branden.IsPFPolynomial.isInfinitelyLogConcave"
module = "RealRooted.BrandenLC.Infinite"
label = "Pólya frequency polynomials are infinitely log-concave"

[[theorems]]
name = "RealRooted.BorosMoll.borosMollRow_isInfinitelyLogConcave"
module = "RealRooted.CombinatorialExamples.BorosMoll.Infinite"
label = "For n ≥ 1, the Boros–Moll row d(n) is infinitely log-concave"
-->

<!-- realrooted-catalog-content -->
# Log-concavity transform of the Boros–Moll rows

The log-concavity transform of a Boros–Moll row has simple negative roots that interlace those of
the Narayana polynomial, and every Boros–Moll row is infinitely log-concave.

## Results

The Boros–Moll coefficients are
$$
d_i(n)=2^{-2n}\sum_{k=i}^{n}2^k\binom{2n-2k}{n-k}\binom{n+k}{n}\binom{k}{i}.
$$
The *log-concavity transform* of a sequence $a$ is $L(a)_i=a_i^2-a_{i-1}a_{i+1}$ with $a_{-1}=0$.
Put $M_n(x)=\sum_{i=0}^nL(d(n))_i\,x^i$ and let
$N_n(x)=\sum_{i=0}^n\frac1{i+1}\binom ni\binom{n+1}ix^i$ be the Narayana polynomial. A polynomial
is a *Pólya frequency polynomial* if it has nonnegative coefficients and only real roots, all
nonpositive. A polynomial is *infinitely log-concave* if all iterates of $L$ applied to its
coefficient sequence are nonnegative.

**Theorem (Xie–Zhang).** For $n\ge1$, $M_n$ has degree $n$ and $n$ simple negative roots. They
strictly interlace the $n$ roots of $N_n$, with the roots of $M_n$ leftmost: if
$a_0<\dots<a_{n-1}$ are the roots of $M_n$ and $b_0<\dots<b_{n-1}$ those of $N_n$, then
$a_0<b_0<a_1<b_1<\dots<a_{n-1}<b_{n-1}$ [@XieZhang2026InfiniteLogConcavity].

**Theorem (Brändén).** The log-concavity transform of a Pólya frequency polynomial is a Pólya
frequency polynomial [@Branden2011b]. Hence every Pólya frequency polynomial is infinitely
log-concave.

**Corollary.** For $n\ge1$, the Boros–Moll row $\sum_i d_i(n)x^i$ is infinitely log-concave, as
conjectured by Boros and Moll [@BorosMoll1999]. Its transform $M_n$ is a Pólya frequency
polynomial.

## Proof

For $n\ge36$ the interlacing reduces to the sign of $M_n$ at the zeros of $N_n$, which we bound
using Gaussian quadrature at the zeros of Jacobi polynomials; the cases $1\le n\le35$ are checked
by exact computation. Brändén's theorem follows from moment functionals that do not vanish on
polynomials with roots in a half-plane, together with Laguerre-type approximations.

## References

- [@XieZhang2026InfiniteLogConcavity]
- [@Branden2011b]
- [@BorosMoll1999]

See also [infinite log-concavity](sf:infinitelyLogConcave) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.BorosMoll`.
-/
