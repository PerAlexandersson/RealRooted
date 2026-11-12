module

import RealRooted.CombinatorialExamples.MultisetEulerianNarayana
import RealRooted.CombinatorialExamples.MultisetEulerianNarayana.GammaOperator
import RealRooted.CombinatorialExamples.MultisetEulerianNarayana.TotallyNonneg
import RealRooted.CombinatorialExamples.MultisetEulerianNarayana.ZeroMonotonicity

/-!
# Multiset Eulerian–Narayana polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "multiset-eulerian-narayana"
formalized = "2026-10-07"
tags = []
references = [
  "ZhangZhao2026x",
  "LinMaMaZhou2021",
]
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
label = "Consecutive partial products interlace without common zeros"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.coeff_multisetEulerianNarayana_symm"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana"
label = "P_α is palindromic"

[[theorems]]
name = "RealRooted.SimpleNegRooted.darbouxOperator"
module = "RealRooted.EulerOperator.Darboux.NegativeRoots"
label = "Darboux steps preserve simple negative zeros and interlace"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.simpleNegRooted_gammaOperator"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana.GammaOperator"
label = "Zhang–Zhao: the gamma operator preserves simple negative zeros"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.exists_hasDerivAt_gammaOperator_input_shift"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana.ZeroMonotonicity"
label = "Zhang–Zhao: output zeros move strictly right with each input zero"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.coefficientTransitionMatrix_eq_closedTransitionMatrix"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana.TotallyNonneg"
label = "Zhang–Zhao: the transition matrix has a closed binomial form"

[[theorems]]
name = "RealRooted.MultisetEulerianNarayana.closedTransitionMatrix_isTotallyNonneg"
module = "RealRooted.CombinatorialExamples.MultisetEulerianNarayana.TotallyNonneg"
label = "Zhang–Zhao: the closed transition matrices are totally nonnegative"
-->

<!-- realrooted-catalog-content -->
# Multiset Eulerian–Narayana polynomials

The multiset Eulerian–Narayana polynomial of a composition of $N$ has degree $N-1$, only simple
negative zeros, and palindromic coefficients; it is built from $N-1$ first-order steps whose
consecutive partial products interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are excluded where stated. Call a real
polynomial $f$ *admissible of degree $m$* if it has degree $m$, positive leading coefficient,
nonnegative coefficients, positive constant term and only simple real zeros; then all zeros
are negative. For $d\in\mathbb N$ and $a>0$ let
$$
E_{d,a} f = \frac1a\Bigl(t(1-t) f' + \bigl(a + (d+a)t\bigr) f\Bigr).
$$
For a composition $\alpha=(p_1,\dots,p_m)$ of $N\ge1$ with partial sums $N_j=p_1+\dots+p_j$, put
$a_d(\alpha)=N_j-d$ for the least $j$ with $N_j>d$. The multiset Eulerian–Narayana polynomial is
$$
P_\alpha = E_{N-2,\,a_{N-2}(\alpha)} \circ \dotsb \circ E_{0,\,a_0(\alpha)}(1).
$$
Zhang and Zhao [@ZhangZhao2026x] obtain this formula for the leaf enumerator $P_M$ of weakly
increasing trees on a multiset $M$ with multiplicities $\alpha$ (the identification is
[@ZhangZhao2026x, Prop. 2.9]); here the formula is the definition of $P_\alpha$.

**Theorem (Zhang–Zhao).** [@ZhangZhao2026x] For a composition $\alpha$ of $N\ge1$, $P_\alpha$
is admissible of degree $N-1$ and $P_\alpha$ is palindromic: its coefficients of $t^k$ and
$t^{N-1-k}$ agree for $0\le k\le N-1$. Let $Q_0=1$ and $Q_{d+1}=E_{d,a_d(\alpha)}Q_d$. Then
$Q_d\ll Q_{d+1}$ and $Q_d,Q_{d+1}$ have no common zero, for $0\le d\le N-2$.

**Theorem (Zhang–Zhao, Lemma 3.2).** For $a>0$ and a polynomial $\Gamma$ admissible of degree
$m$, put
$$
\Phi_{d,a}\Gamma=\Gamma+\frac{t(1-4t)\Gamma'+2dt\Gamma}{a},\qquad d\in\{2m,2m+1\}.
$$
If $d=2m$ then $\Phi_{d,a}\Gamma$ is admissible of degree $m$; if $d=2m+1$ it is admissible of
degree $m+1$.

**Theorem (Zhang–Zhao, Proposition 3.4).** Let $a>0$, let $p=\prod_{j=1}^n(t-r_j)$ with
distinct negative $r_j$, and let $d\in\{2n,2n+1\}$. If $\rho$ is a zero of $\Phi_{d,a}p$ and
$r_i$ is replaced by $r_i+s$, then $\rho$ moves along a differentiable branch $\rho(s)$ of
zeros of the new polynomial with $\rho'(0)>0$.

**Theorem (Zhang–Zhao, Theorem 1.3).** [@ZhangZhao2026x, Thm. 1.3] Let $p,r\ge1$. Let $K_{p,r}$
be the $(p+r)\times p$ matrix whose entry in row $k$ and column $\ell$ (from $0$) is $0$ unless
$\ell\le k\le\ell+r$, and then
$$
\binom{p-\ell+r}{k-\ell}\binom{\ell+1+r}{r-k+\ell}
\frac{(\ell+1)(p+r-k)+(p-\ell)(k-\ell)}{(\ell+1+r)(p-\ell+r)}.
$$
Then $K_{p,r}$ is totally nonnegative. It is the product of the coefficient matrices of the
steps $E_{p+s-1,a_s}$, $0\le s<r$, with $a_0=1$ and $a_s=r-s+1$ for $s\ge1$, each a
nonnegative lower bidiagonal matrix, restricted to the first $p$ columns.

## Proof

Each step is a Darboux operator $t(1-t)f'+(a+bt)f$ with $a>0$ and $b>\deg f$. It raises the
degree by one; at a zero $r$ of $f$ its value is $r(1-r)f'(r)$, which alternates in sign, so the
new zeros interlace the old ones. The parameters $a_d(\alpha)$ are positive for $d<N$.

## References

For the tree model and the conjecture that $P_M$ is real-rooted, see [@LinMaMaZhou2021]; the
interlacing result is [@ZhangZhao2026x].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.MultisetEulerianNarayana`.
-/
