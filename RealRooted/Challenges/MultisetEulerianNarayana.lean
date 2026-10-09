import RealRooted.CombinatorialExamples.MultisetEulerianNarayana
import RealRooted.CombinatorialExamples.MultisetEulerianNarayana.GammaOperator

/-!
# Multiset Eulerian–Narayana polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "multiset-eulerian-narayana"
authors = ["Lin", "Ma", "Zhou", "Zhang", "Zhao"]
years = [2021, 2026]

[[definitions]]
name = "RealRooted.MultisetEulerianNarayana.step"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana"
label = "The first-order factor E_{d,a}"

[[definitions]]
name = "RealRooted.MultisetEulerianNarayana.multisetEulerianNarayana"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana"
label = "The multiset Eulerian–Narayana polynomial P_α"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.simpleNegRooted_multisetEulerianNarayana"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana"
label = "P_α has only simple negative zeros"
headline = true

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.strictInterl_partialPoly"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana"
label = "Consecutive partial products strictly interlace"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.coeff_multisetEulerianNarayana_symm"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana"
label = "P_α is palindromic"

[[theorems]]
name = "RealRooted.SimpleNegRooted.darbouxOperator"
module = "RealRooted.EulerOperator.Darboux.NegativeRoots"
label = "Darboux steps preserve simple negative zeros and interlace"

[[theorems]]
name = "RealRooted.Applications.MultisetEulerianNarayana.simpleNegRooted_gammaOperator"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana.GammaOperator"
label = "Zhang–Zhao: the gamma operator preserves simple negative zeros"
-->

<!-- realrooted-catalog-content -->
# Multiset Eulerian–Narayana polynomials

Let $M = \{1^{p_1}, \dotsc, m^{p_m}\}$ be a multiset of size $N$. A weakly
increasing tree on $M$ is a plane tree on $M \cup \{0\}$, rooted at $0$, whose
labels weakly increase along every root-to-leaf path and from left to right
among siblings. Lin, Ma, Ma and Zhou studied the normalized leaf enumerator
$P_M(t)$ of these trees. It interpolates between the Eulerian polynomials
($p_i = 1$) and the Narayana polynomials ($m = 1$). They conjectured that it is
real-rooted.

Zhang and Zhao factor it into first-order steps. Write
$$E_{d,a} f = \frac1a\Bigl(t(1-t) f' + \bigl(a + (d+a)t\bigr) f\Bigr)$$
and, for the composition $\alpha = (p_1, \dotsc, p_m)$ with partial sums $N_j$,
let $a_d(\alpha) = N_j - d$ for the least $j$ with $N_j > d$. Then
$$P_\alpha = E_{N-2, a_{N-2}(\alpha)} \circ \dotsb \circ E_{0, a_0(\alpha)}(1).$$
Here this factorization defines $P_\alpha$. The tree model and the
Lagrange–Bürmann argument behind the factorization are not formalized.

**Theorem** (Zhang–Zhao). For every composition $\alpha$ of $N \ge 1$, the
polynomial $P_\alpha$ has degree $N - 1$, nonnegative coefficients and only
simple negative zeros. Consecutive partial products of the factorization strictly
interlace, and $P_\alpha$ is palindromic.

The conjecture itself also needs the identification of $P_\alpha$ with the leaf
enumerator $P_M$ (Zhang–Zhao, Proposition 2.9). That identification is cited
from the paper, not formalized.

## Proof idea

Each factor is a Darboux operator
$x(1-x) f' + (a + bx) f$ with $a > 0$ and $b > \deg f$. Such an operator raises
the degree by one. At each zero $r$ of $f$ its value is $r(1-r) f'(r)$, which
alternates in sign, so the new zeros interlace the old ones. All parameters
$a_d(\alpha)$ are positive.

## References

Z. Lin, J. Ma, S.-M. Ma and Y. Zhou, “Weakly increasing trees on a multiset,”
*Advances in Applied Mathematics* 129 (2021), 102206; P. B. Zhang and T. Zhao,
“Zeros and interlacing for multiset Eulerian–Narayana polynomials,”
arXiv:2610.00966 (2026).

The real-rootedness theorem was formalized in RealRooted issue #1076.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.MultisetEulerianNarayana`.
-/
