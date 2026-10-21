import RealRooted.MultivariateStability.MorrisDFlow
import RealRooted.MultivariateStability.MorrisEigenfunction
import RealRooted.MultivariateStability.MorrisOperator

/-!
# Morris flow challenge entry point

<!-- realrooted-catalog
version = 1
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
label = "The operator A_q = Σ xᵢ² ∂ᵢ²"

[[definitions]]
name = "RealRooted.LiuZhang.morrisB"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The operator B_q of the Morris flow"

[[definitions]]
name = "RealRooted.LiuZhang.morrisD"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The Morris operator D_q = B_q − A_q"

[[definitions]]
name = "RealRooted.LiuZhang.morrisEigenvalue"
module = "RealRooted.MultivariateStability.MorrisOperator"
label = "The eigenvalue ε_λ of D_q"

[[definitions]]
name = "RealRooted.LiuZhang.morrisDExp"
module = "RealRooted.MultivariateStability.MorrisDFlow"
label = "The flow exp(t D_q) on symmetric polynomials of bounded degree"

[[definitions]]
name = "RealRooted.LiuZhang.normalizedMorrisDExp"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "The normalized flow exp(−t ε_λ) exp(t D_q) E_λ"

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisDExp"
module = "RealRooted.MultivariateStability.MorrisDFlow"
label = "Liu–Zhang, Theorem 4.9: exp(t D_q) preserves real stability for t ≥ 0"
headline = true

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisDExp_of_symmetric"
module = "RealRooted.MultivariateStability.MorrisDFlow"
label = "Theorem 4.9 for a symmetric polynomial with a total-degree bound"

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisElementary"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "The elementary product E_λ is real stable (Lemma 4.4)"

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.normalizedMorrisDExp"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "The normalized Morris flow is real stable for t ≥ 0"

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.of_normalizedMorrisDExp_tendsto"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "A nonzero coefficientwise limit of the normalized flow is real stable"

[[theorems]]
name = "RealRooted.LiuZhang.existsUnique_morrisEigenfunction"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "Liu–Zhang, Theorem 4.12: a unique normalized eigenfunction of D_q"
headline = true

[[theorems]]
name = "RealRooted.LiuZhang.MvRealStable.morrisEigenfunction"
module = "RealRooted.MultivariateStability.MorrisEigenfunction"
label = "Liu–Zhang, Theorem 4.12: the normalized eigenfunction is real stable"
headline = true
-->

<!-- realrooted-catalog-content -->
# The Morris flow and its stable eigenfunctions

Following Liu and Zhang [@LiuZhang2026bx], we work with symmetric polynomials in
$x_1, \dotsc, x_q$ and the differential operators
$$
A_q = \sum_{i=1}^{q} x_i^2 \partial_i^2, \qquad
B_q = 2 \sum_{1 \leq i < j \leq q}
  \frac{x_i^2 \partial_i - x_j^2 \partial_j}{x_i - x_j}, \qquad
D_q = B_q - A_q ,
$$
where $\partial_i = \partial/\partial x_i$. The operators $A_q$ and $B_q$ do not commute, and
$B_q$ maps symmetric polynomials to symmetric polynomials. A real polynomial is *real stable*
if it has no zeros when all variables lie in the open upper half-plane; in particular it is
nonzero (see [real stability](/RealRooted/theorems/real-stability/)). We write
$\operatorname{Sym}_{q,\leq N}$ for the finite-dimensional real space of symmetric polynomials
in $q$ variables of total degree at most $N$.

**Theorem** (Liu–Zhang, Theorem 4.9). [@LiuZhang2026bx, Thm. 4.9]
Let $t \geq 0$ and $N \in \mathbb N$. If
$P \in \operatorname{Sym}_{q,\leq N}$ is real stable, then $e^{t D_q} P$ is real stable.

In the Lean statement, $e^{tD_q}$ is the exponential of the restriction of $D_q$ to
$\operatorname{Sym}_{q,\leq N}$, acting through a coordinate chart of that space
(`morrisDExp`), and a variant is stated directly for a symmetric polynomial $P$ with
$\deg P \leq N$.

For a partition $\lambda$ of $N$ with at most $q$ parts, the elementary product $E_\lambda$ is
$\prod_j e_{\lambda'_j}$, where $\lambda'$ is the conjugate partition and $e_k$ is the $k$th
elementary symmetric polynomial in $x_1, \dotsc, x_q$. It is real stable. The eigenvalue is
$$
\varepsilon_\lambda = 2 \sum_{(i,j) \in [\lambda]} (q + 1 - i - j),
$$
the sum over the cells of the Ferrers diagram of $\lambda$, and `morrisEigenvalue` is its
integer-valued form. The normalized flow is
$$
t \;\longmapsto\; e^{-t \varepsilon_\lambda}\, e^{t D_q} E_\lambda
$$
(`normalizedMorrisDExp`). It is real stable for every $t \geq 0$, and has total degree at most
$N$. A coefficientwise limit of this flow as $t = n \to \infty$ through the natural numbers,
which is nonzero and of total degree at most $N$, is real stable.

**Theorem** (Liu–Zhang, Theorem 4.12). [@LiuZhang2026bx, Thm. 4.12]
Let $\lambda$ be a partition of $N$ with at most $q$
parts such that $\lambda_i - \lambda_{i+1} \leq 1$ for $1 \leq i < q$. Let $V_\lambda$ be the
span of the monomial symmetric polynomials $m_\mu$ for partitions $\mu \preceq \lambda$ in
dominance order with at most $q$ parts.

1. There is a unique $P \in V_\lambda$ with $D_q P = \varepsilon_\lambda P$ whose coefficient of
   $m_\lambda$ is $1$.
2. Every such $P$ is real stable.

## Proof idea

For Theorem 4.9 we use that $A_q$ and $B_q$ separately generate real stability preserving flows.
The flow $e^{-tA_q}$ is a product of coordinate operators acting on the monomial basis, and
$e^{tB_q}$ acts diagonally on the elementary basis. On the finite-dimensional space
$\operatorname{Sym}_{q,\leq N}$, the Lie–Trotter product formula expresses $e^{t(B_q - A_q)}$
as a limit of alternating products of these two flows. Each product preserves real stability.
A coefficientwise limit of polynomials of bounded degree which is nonzero is again real stable,
and $e^{tD_q}$ is invertible, so the limit is nonzero for nonzero input.

For Theorem 4.12 we start from the real stable polynomial $E_\lambda$. On the finite dominance
downset of $\lambda$, the operator $D_q$ is triangular in the monomial basis with diagonal
entries $\varepsilon_\mu$. Under the adjacent-drop condition $\lambda_i - \lambda_{i+1} \leq 1$,
the eigenvalue $\varepsilon_\lambda$ is strictly larger than $\varepsilon_\mu$ for all other
$\mu \preceq \lambda$, which gives a spectral gap. The normalized flow
$e^{-t\varepsilon_\lambda} e^{tD_q} E_\lambda$ therefore converges, coefficientwise, to the
normalized eigenfunction. Real stability of each member of the flow passes to the limit, since
the limit is nonzero. Uniqueness of the normalized eigenfunction then transfers the conclusion
to every normalized eigenfunction.

## References

See [@LiuZhang2026bx]. Theorems 4.9 and 4.12 here are Theorems 1.2 and 1.3
of that paper, and Lemma 4.4 is its real-stability result for $E_\lambda$.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The operators and the eigenvalue are in
`RealRooted.MultivariateStability.MorrisOperator`, the flow in
`RealRooted.MultivariateStability.MorrisDFlow`, and the eigenfunction results in
`RealRooted.MultivariateStability.MorrisEigenfunction`.
-/
