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
label = "Kostov, Theorem 3: consecutive eigenpolynomials strictly interlace"
headline = true

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_two_step"
module = "RealRooted.Hadamard.Kostov.TwoStep"
label = "Kostov, Theorem 4: the two-step root comparison"
headline = true
-->

<!-- realrooted-catalog-content -->
# Kostov's eigenpolynomials of the Schur--Szegő coefficient map

Fix a degree $n$. Kostov's coefficient map sends the coefficients of a monic polynomial
with a root at $-1$ to the elementary symmetric functions of the parameters in its
Schur--Szegő factorization. We show that the linear part of this map has the eigenvalues
$\lambda_k$, each with a one-dimensional eigenspace, and we identify the eigenvectors
through the reduced eigenpolynomials $Q_{n,j}$: each $Q_{n,j}$ is monic of degree
$j$, satisfies $X^j Q_{n,j}(1/X) = (-1)^j Q_{n,j}(X)$, and vanishes at $1$ when
$j$ is odd.

The roots of $Q_{n,j}$ are simple and positive. Kostov's Theorem 3
[@Kostov2010, Thm. 3] says that consecutive eigenpolynomials $Q_{n,j}$ and
$Q_{n,j+1}$ strictly interlace, and his Theorem 4 [@Kostov2010, Thm. 4] compares
the roots of $Q_{n,j}$ and $Q_{n,j+2}$, with the shared central root $1$ when $j$
is odd. The proofs pass through the eigenproblem of a Bernstein-type operator, real zeros by
a compactness argument, Descartes' rule of signs, and a Wronskian argument.

## References

See [@Kostov2010].
<!-- /realrooted-catalog-content -->
-/
