import RealRooted.CombinatorialExamples.BorosMoll
import RealRooted.CombinatorialExamples.BorosMoll.Infinite

/-!
# Boros–Moll challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "boros-moll-log-concavity-transform"
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
label = "Xie–Zhang: the transform has n simple negative zeros"
headline = true

[[theorems]]
name = "RealRooted.BorosMoll.bmM_strictInterlaces_narayanaN"
module = "RealRooted.CombinatorialExamples.BorosMoll"
label = "Xie–Zhang: its zeros strictly interlace those of the Narayana polynomial"

[[definitions]]
name = "RealRooted.Branden.IsInfinitelyLogConcave"
module = "RealRooted.BrandenLC.Infinite"
label = "Infinitely log-concave: every iterate of the transform is nonnegative"

[[theorems]]
name = "RealRooted.Branden.IsPFPolynomial.logConcavityTransform"
module = "RealRooted.BrandenLC"
label = "Brändén: the log-concavity transform preserves Pólya-frequency polynomials"

[[theorems]]
name = "RealRooted.Branden.IsPFPolynomial.isInfinitelyLogConcave"
module = "RealRooted.BrandenLC.Infinite"
label = "Pólya-frequency polynomials are infinitely log-concave"

[[theorems]]
name = "RealRooted.BorosMoll.borosMollRow_isInfinitelyLogConcave"
module = "RealRooted.CombinatorialExamples.BorosMoll.Infinite"
label = "The Boros–Moll rows are infinitely log-concave"
headline = true
-->

<!-- realrooted-catalog-content -->
# The log-concavity transform of the Boros–Moll rows

The Boros–Moll coefficients
$$
d_i(n) = 2^{-2n} \sum_{k=i}^{n} 2^k \binom{2n-2k}{n-k} \binom{n+k}{n} \binom{k}{i}
$$
arise in the Taylor expansion of a quartic integral. The *log-concavity transform*
of a row is $L(d(n))_i = d_i(n)^2 - d_{i-1}(n)\, d_{i+1}(n)$; write
$M_n(x) = \sum_i L(d(n))_i x^i$, and let
$N_n(x) = \sum_{i=0}^n \frac{1}{i+1} \binom{n}{i} \binom{n+1}{i} x^i$ be the
Narayana polynomial.

**Theorem** (Xie–Zhang). For $n \geq 1$, $M_n$ has $n$ simple negative zeros, and they
strictly interlace the zeros of $N_n$, those of $M_n$ being the leftmost.

**Theorem** (Brändén). If $p$ has nonnegative coefficients and only real, nonpositive
zeros, then so does its log-concavity transform. Hence every Pólya-frequency polynomial is
*infinitely log-concave*: all iterates of the transform have nonnegative coefficients.

Since $M_n$ is the transform of the row $d(n)$ and is Pólya-frequency, the Boros–Moll rows
are infinitely log-concave, as conjectured by Boros and Moll. All three statements are
formalized. The formal proof of Brändén's theorem is not Brändén's: Aristotle found a
different argument with moment functionals that do not vanish on polynomials whose zeros
lie in a half-plane, together with Laguerre-type approximations.

## Proof idea

The interlacing reduces to the sign of $M_n$ at the zeros of $N_n$. For $n \geq 36$ the
paper writes these values through moment and coefficient identities, bounds partial sums
with a boundary recurrence, and controls the remaining weighted sums by Gaussian
quadrature at the zeros of Jacobi polynomials. The cases $n \leq 35$ are checked by exact
certificates evaluated in the kernel. The formal proof was found with the Aristotle prover
(Harmonic) following the paper.

## References

P. Brändén, “Iterated sequences and the geometry of zeros,” *Journal für die reine und
angewandte Mathematik* 658 (2011), 115–131; M. H. Y. Xie and P. B. Zhang, “Infinite
log-concavity of the Boros–Moll sequences,”
arXiv:2609.20653 (2026); G. Boros and V. H. Moll, “An integral hidden in Gradshteyn and
Ryzhik,” *J. Comput. Appl. Math.* 106 (1999), 361–368.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.BorosMoll`.
-/
