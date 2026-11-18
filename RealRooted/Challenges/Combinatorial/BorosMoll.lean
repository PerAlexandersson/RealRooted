module

import RealRooted.BrandenLC
import RealRooted.BrandenLC.Infinite
import RealRooted.CombinatorialExamples.BorosMoll
import RealRooted.CombinatorialExamples.BorosMoll.Core
import RealRooted.CombinatorialExamples.BorosMoll.Infinite

/-!
# Infinite log-concavity of the Boros–Moll sequences

<!-- realrooted-catalog
version = 1
kind = "conjecture"
conjecture = "Boros–Moll infinite log-concavity, recorded in Brändén (2011), Conjecture 8.4"
section = "theorems"
slug = "boros-moll"
formalized = "2026-10-09"
references = [
  "XieZhang2026InfiniteLogConcavity",
  "Branden2011b",
  "BorosMoll1999",
]
authors = ["Boros", "Moll", "Brändén", "Xie", "Zhang"]
years = [1999, 2011, 2026]

[[definitions]]
name = "RealRooted.BorosMoll.bmCoeff"
module = "RealRooted.CombinatorialExamples.BorosMoll.Core"
label = "Boros–Moll coefficients"

[[definitions]]
name = "RealRooted.BorosMoll.bmM"
module = "RealRooted.CombinatorialExamples.BorosMoll.Core"
label = "Generating polynomial of the log-concavity transform of a Boros–Moll row"

[[theorems]]
name = "RealRooted.BorosMoll.bmM_roots"
module = "RealRooted.CombinatorialExamples.BorosMoll"
label = "For n ≥ 1, M_n has degree n and n simple negative roots"

[[theorems]]
name = "RealRooted.BorosMoll.bmM_strictInterlaces_narayanaN"
module = "RealRooted.CombinatorialExamples.BorosMoll"
label = "Xie–Zhang: the roots of M_n strictly interlace those of the Narayana polynomial N_n"

[[definitions]]
name = "RealRooted.Branden.IsInfinitelyLogConcave"
module = "RealRooted.BrandenLC.Infinite"
label = "Infinitely log-concave: every iterate of the transform is nonnegative"

[[theorems]]
name = "RealRooted.Branden.IsPFPolynomial.logConcavityTransform"
module = "RealRooted.BrandenLC"
label = "Brändén: the log-concavity transform preserves Pólya frequency polynomials"

[[theorems]]
name = "RealRooted.Branden.IsPFPolynomial.isInfinitelyLogConcave"
module = "RealRooted.BrandenLC.Infinite"
label = "Pólya frequency polynomials are infinitely log-concave"

[[theorems]]
objects = ["Boros–Moll polynomials"]
property = "log-concave"
name = "RealRooted.BorosMoll.borosMollRow_isInfinitelyLogConcave"
module = "RealRooted.CombinatorialExamples.BorosMoll.Infinite"
label = "Every Boros–Moll sequence d(n), n ≥ 1, is infinitely log-concave"
headline = true
-->

<!-- realrooted-catalog-content -->
# Infinite log-concavity of the Boros–Moll sequences

Boros and Moll conjectured that their coefficient sequences, which arise from a quartic
integral, are infinitely log-concave. Xie and Zhang proved that one log-concavity step turns
each sequence into one with a real-rooted generating polynomial, and Brändén's theorem then
gives infinite log-concavity.

## Results

The Boros–Moll coefficients are
$$
d_i(n)=2^{-2n}\sum_{k=i}^{n}2^k\binom{2n-2k}{n-k}\binom{n+k}{n}\binom{k}{i}.
$$
The *log-concavity transform* of a sequence $a$ is $L(a)_i=a_i^2-a_{i-1}a_{i+1}$ with
$a_{-1}=0$, and $a$ is *infinitely log-concave* if all iterates $L^k(a)$ are nonnegative. Put
$M_n(x)=\sum_{i=0}^nL(d(n))_i\,x^i$ and let
$N_n(x)=\sum_{i=0}^n\frac1{i+1}\binom ni\binom{n+1}ix^i$ be the Narayana polynomial. A
*Pólya frequency polynomial* has nonnegative coefficients and only real roots.

**Theorem (Xie–Zhang).** [@XieZhang2026InfiniteLogConcavity, Thm. 1] For $n\ge1$, $M_n$ has
$n$ simple negative roots, which strictly interlace the roots of $N_n$, with the smallest root
belonging to $M_n$.

**Theorem (Brändén).** [@Branden2011b, §3] The log-concavity transform of a Pólya frequency
polynomial is a Pólya frequency polynomial. Hence every Pólya frequency polynomial is infinitely
log-concave.

**Corollary.** For $n\ge1$, the sequence $d(n)$ is infinitely log-concave, as conjectured by
Boros and Moll [@BorosMoll1999; @Branden2011b, Conj. 8.4].

## Proof

For $n\ge36$ the interlacing reduces to the sign of $M_n$ at the zeros of $N_n$, which we bound
using Gaussian quadrature at the zeros of Jacobi polynomials; the cases $1\le n\le35$ are checked
by exact computation. Brändén's theorem follows from a symmetric function identity that
linearizes the transform, together with Grace–Walsh–Szegő type arguments.

## References

[@XieZhang2026InfiniteLogConcavity, Thm. 1]; [@Branden2011b, §3 and Conj. 8.4];
[@BorosMoll1999]. See also [infinite log-concavity](sf:infinitelyLogConcave) on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
