module

import RealRooted.Hadamard.Kostov.Eigen
import RealRooted.Hadamard.Kostov.Roots
import RealRooted.Hadamard.Kostov.TwoStep

/-!
# Kostov's Bernstein eigenpolynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "kostov-eigenpolynomials"
formalized = "2026-10-12"
references = [
  "Kostov2010",
]
authors = ["Kostov"]
years = [2015]

[[definitions]]
name = "RealRooted.Kostov.eigenpolynomial"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "The canonical reduced Bernstein eigenpolynomial"

[[definitions]]
name = "RealRooted.Kostov.eigenvalue"
module = "RealRooted.Hadamard.Kostov.Bernstein"
label = "Eigenvalue candidates for the Schur–Szegő coefficient map"

[[theorems]]
name = "RealRooted.Kostov.linearPart_hasEigenvector"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "Every eigenvalue candidate has a nonzero eigenvector"

[[theorems]]
name = "RealRooted.Kostov.linearPart_eigenspace_line"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "Each candidate eigenspace is one-dimensional"

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_hasEigenvector"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "A reduced eigenpolynomial gives its coefficient-map eigendirection"

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_monic"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "The reduced eigenpolynomial is monic"

[[theorems]]
name = "RealRooted.Kostov.natDegree_eigenpolynomial"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "The reduced eigenpolynomial has its indexed degree"

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_roots_simple_pos"
module = "RealRooted.Hadamard.Kostov.Roots"
label = "Kostov: eigenpolynomials have simple positive roots"
headline = true

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_splits"
module = "RealRooted.Hadamard.Kostov.Roots"
label = "The eigenpolynomials split over the reals"

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_strictInterl"
module = "RealRooted.Hadamard.Kostov.Roots"
label = "Kostov, Theorem 3: consecutive eigenpolynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_two_step"
module = "RealRooted.Hadamard.Kostov.TwoStep"
label = "Kostov, Theorem 4: the two-step root comparison"
headline = true

[[theorems]]
name = "RealRooted.Kostov.reverse_eigenpolynomial"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "The reduced eigenpolynomial is reciprocal up to sign"

[[theorems]]
name = "RealRooted.Kostov.eval_one_eigenpolynomial_of_odd"
module = "RealRooted.Hadamard.Kostov.Eigen"
label = "Odd reduced eigenpolynomials vanish at one"
-->

<!-- realrooted-catalog-content -->
# Kostov's eigenpolynomials of the Schur--Szegő coefficient map

Fix $n\geq2$. Kostov's coefficient map sends the coefficients of a monic
polynomial with a root at $-1$ to the elementary symmetric functions of the
parameters in its Schur--Szegő factorization. For $0\leq k<n-1$, put
$$
\lambda_k=\frac{n^k}{(n-1)^{\underline{k}}}.
$$
The linear part of the map has each $\lambda_k$ as an eigenvalue, with a
one-dimensional eigenspace. For $0\leq j\leq n-3$, the reduced
eigenpolynomial $Q_{n,j}$ gives an eigendirection for $\lambda_{j+1}$; it is
monic of degree $j$, satisfies
$X^jQ_{n,j}(1/X)=(-1)^jQ_{n,j}(X)$, and vanishes at $1$ when $j$ is odd.

For $0\leq j\leq n-3$, the roots of $Q_{n,j}$ are simple and positive. For
$1\leq j\leq n-4$, Kostov's Theorem 3 [@Kostov2010, Thm. 3] says that
$Q_{n,j}\ll Q_{n,j+1}$. For $1\leq j\leq n-5$, his Theorem 4
[@Kostov2010, Thm. 4] compares the roots of $Q_{n,j}$ and $Q_{n,j+2}$, with
the shared central root $1$ when $j$ is odd. The proofs pass through the
eigenproblem of a Bernstein-type operator, real zeros by a compactness
argument, Descartes' rule of signs, and a Wronskian argument.

## References

See [@Kostov2010].
<!-- /realrooted-catalog-content -->
-/
