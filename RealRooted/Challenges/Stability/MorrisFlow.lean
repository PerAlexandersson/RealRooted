module

import RealRooted.MultivariateStability.MorrisDFlow
import RealRooted.MultivariateStability.MorrisEigenfunction
import RealRooted.MultivariateStability.MorrisOperator

/-!
# Real stability of Morris eigenfunctions

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "morris-flow"
formalized = "2026-10-16"
references = [
  "LiuZhang2026bx",
]
authors = ["Liu", "Zhang"]
years = [2026]

[[definitions]]
name = "RealRooted.LiuZhang.morrisA"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The operator $A_q = ∑ x_i^2 ∂_i^2$"

[[definitions]]
name = "RealRooted.LiuZhang.morrisB"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The operator $B_q$ of the Morris flow"

[[definitions]]
name = "RealRooted.LiuZhang.morrisD"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The Morris operator $D_q = B_q - A_q$"

[[definitions]]
name = "RealRooted.LiuZhang.morrisEigenvalue"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The eigenvalue $ε_λ$ of $D_q$"

[[definitions]]
name = "RealRooted.LiuZhang.morrisDExp"
module = "RealRooted.MultivariateStability.MorrisDFlow"
label = 'The flow $\exp(t D_q)$ on symmetric polynomials of bounded degree'

[[definitions]]
name = "RealRooted.LiuZhang.normalizedMorrisDExp"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = 'The normalized flow $\exp(-t ε_λ) \exp(t D_q) E_λ$'

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisDExp_of_symmetric"
module = "RealRooted.MultivariateStability.MorrisDFlow"
label = 'Liu–Zhang: for $t ≥ 0$, $\exp(t D_q)$ preserves real stability of symmetric polynomials'

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisElementary"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "The elementary product $E_λ$ is real stable"

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.normalizedMorrisDExp"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = 'The normalized flow $\exp(-t ε_λ) \exp(t D_q) E_λ$ is real stable for $t ≥ 0$'

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.of_normalizedMorrisDExp_tendsto"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "A nonzero coefficientwise limit of the normalized flow is real stable"

[[theorems]]
name = "RealRooted.LiuZhang.existsUnique_morrisEigenfunction"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "$D_q$ has a unique eigenfunction in the dominance downset with top coefficient 1"

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisEigenfunction"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "Liu–Zhang: the normalized eigenfunctions of the Morris operator $D_q$ are real stable"
headline = true
-->

<!-- realrooted-catalog-content -->
# Real stability of Morris eigenfunctions

The Morris operator $D_q$ is a second-order differential operator on symmetric polynomials in
$q$ variables. Liu and Zhang prove that the flow $e^{tD_q}$ preserves real stability for
$t\ge0$, and that the normalized eigenfunctions of $D_q$ are real stable.

## Results

On symmetric polynomials in $x_1,\dotsc,x_q$ we consider the differential operators
$$
A_q=\sum_{i=1}^qx_i^2\partial_i^2,\qquad
B_q=2\sum_{1\le i<j\le q}\frac{x_i^2\partial_i-x_j^2\partial_j}{x_i-x_j},\qquad D_q=B_q-A_q,
$$
where $\partial_i=\partial/\partial x_i$. The operator $B_q$ maps symmetric polynomials to
symmetric polynomials. A real polynomial is *real stable* if it has no zeros when all variables
lie in the open upper half-plane; in particular it is nonzero
([real stability](rr:real-stability)). We write $\operatorname{Sym}_{q,\le N}$ for the real space
of symmetric polynomials in $q$ variables of total degree at most $N$, and $e^{tD_q}$ for the
exponential of the restriction of $D_q$ to this space.

**Theorem (Liu–Zhang).** [@LiuZhang2026bx, Thm. 1.2] Let $t\ge0$ and $N\in\mathbb N$. If
$P\in\operatorname{Sym}_{q,\le N}$ is real stable, then $e^{tD_q}P$ is real stable.

For a partition $\lambda$ of $N$ with at most $q$ parts, the elementary product is
$E_\lambda=\prod_je_{\lambda'_j}$, where $\lambda'$ is the conjugate partition and $e_k$ is the
$k$th elementary symmetric polynomial in $x_1,\dotsc,x_q$; it is real stable. Put
$$
\varepsilon_\lambda=2\sum_{(i,j)\in[\lambda]}(q+1-i-j),
$$
the sum over the cells of the Ferrers diagram of $\lambda$.

**Proposition (normalized flow).** The polynomial $e^{-t\varepsilon_\lambda}\,e^{tD_q}E_\lambda$
is real stable for every $t\ge0$ and has total degree at most $N$. A coefficientwise limit of
this flow along $t=n\to\infty$ through the natural numbers that is nonzero and of total degree at
most $N$ is real stable.

**Theorem (Liu–Zhang).** [@LiuZhang2026bx, Thm. 1.3] Let $\lambda$ be a partition of $N$ with at
most $q$ parts such that $\lambda_i-\lambda_{i+1}\le1$ for $1\le i<q$. Let $V_\lambda$ be the span
of the monomial symmetric polynomials $m_\mu$ for partitions $\mu\preceq\lambda$ in dominance order
with at most $q$ parts. There is a unique $P\in V_\lambda$ with $D_qP=\varepsilon_\lambda P$ whose
coefficient of $m_\lambda$ is $1$, and $P$ is real stable.

## Use

Liu and Zhang built the flow to prove that the $h^*$-polynomials of a variation of the Morris
constant term, studied by Xin and Zhang, are real-rooted and $\gamma$-positive, as Xin and
Zhang conjectured.

## Proof

The flows $e^{-tA_q}$, a product of coordinate operators on the monomial basis, and $e^{tB_q}$,
diagonal on the elementary basis, preserve real stability, and the Lie–Trotter product formula
writes $e^{t(B_q-A_q)}$ as a limit of alternating products of the two. A nonzero coefficientwise
limit of real stable polynomials of bounded degree is real stable. For the eigenfunction, $D_q$
is triangular in the monomial basis on the dominance downset of $\lambda$ with diagonal entries
$\varepsilon_\mu$, and when $\lambda_i-\lambda_{i+1}\le1$ the eigenvalue $\varepsilon_\lambda$ is
the largest, so the normalized flow from $E_\lambda$ converges to $P$.

## References

[@LiuZhang2026bx, Thms. 1.2, 1.3 and Lemma 4.4]
<!-- /realrooted-catalog-content -->
-/
