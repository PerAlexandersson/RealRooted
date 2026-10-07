import RealRooted.CoefficientShape.Liggett

/-!
# Liggett's theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "liggett-ultra-log-concavity"
authors = ["Liggett"]
years = [1997]

[[definitions]]
name = "RealRooted.CoeffUltraLogConcaveUpTo"
module = "RealRooted.CoefficientShape"
label = "Ultra-log-concavity of order d"

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_mul"
module = "RealRooted.CoefficientShape.Liggett"
label = "Liggett: ultra-log-concavity is closed under products"
headline = true

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_conv"
module = "RealRooted.CoefficientShape.Liggett"
label = "Convolution of ULC(m) and ULC(n) sequences is ULC(m + n)"
-->

<!-- realrooted-catalog-content -->
# Liggett's theorem

A nonnegative sequence $a_0, \dotsc, a_d$ is *ultra-log-concave of order $d$*,
written ULC($d$), if $a_k / \binom{d}{k}$ is log-concave without internal zeros:
$$
k(d-k)\, a_k^2 \geq (k+1)(d-k+1)\, a_{k-1} a_{k+1} \qquad (0 < k < d).
$$
By Newton's inequalities, the coefficients of a real-rooted polynomial of
degree $d$ with nonnegative coefficients are ULC($d$).

**Theorem** (Liggett). If $a$ is ULC($m$) and $b$ is ULC($n$), then their
convolution $c_k = \sum_i a_i b_{k-i}$ is ULC($m+n$). Equivalently,
ultra-log-concave coefficient sequences are closed under multiplication of
polynomials.

This strengthens [Hoggar's theorem](/RealRooted/theorems/hoggar-log-concavity/),
which is the same statement for ordinary log-concavity. The hypothesis on
internal zeros cannot be dropped. The sequence $1, 0, 0, 1$ satisfies the
displayed inequalities for $d = 3$, but its product with $1 + x$ does not
satisfy them for $d = 4$.

## Proof idea

The proof is by induction on $n$. Split the order-$(n+1)$ factor $b$ as
$(n+1) b_j = (n+1-j) b_j + j b_j$. Both parts are ULC($n$), so the induction
hypothesis applies to their convolutions with $a$. The two parts are
likelihood-ratio ordered, which is checked through the log-concave sequence
$b_j \, j! \, (n+1-j)!$. Convolution with the log-concave sequence $a$ preserves
this ordering, by a $2 \times 2$ Cauchy–Binet argument as in Hoggar's theorem.
A real-number inequality then combines the two induction hypotheses.

This elementary argument was found with the Aristotle prover (Harmonic). It is
not Liggett's original proof. Other known proofs use mixed volumes (Gurvits),
the Johnson scheme (Kahn–Neiman) or Lorentzian polynomials (Brändén–Huh).

## References

T. M. Liggett, “Ultra logconcave sequences and negative dependence,” *Journal of
Combinatorial Theory, Series A* 79 (1997), 315–325; L. Gurvits, “A short proof,
based on mixed volumes, of Liggett's theorem on the convolution of
ultra-logconcave sequences,” *Electronic Journal of Combinatorics* 16 (2009), N5.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CoefficientShape.Liggett`.
-/
