module

import RealRooted.Hadamard.Kostov.Eigen
import RealRooted.Hadamard.Kostov.Roots
import RealRooted.Hadamard.Kostov.TwoStep

/-!
# Kostov's eigenpolynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "kostov-eigenpolynomials"
formalized = "2026-10-12"
tags = []
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

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_splits"
module = "RealRooted.Hadamard.Kostov.Roots"
label = "The eigenpolynomials are real-rooted"

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_strictInterl"
module = "RealRooted.Hadamard.Kostov.Roots"
label = "Kostov, Theorem 3: consecutive eigenpolynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.Kostov.eigenpolynomial_two_step"
module = "RealRooted.Hadamard.Kostov.TwoStep"
label = "Kostov, Theorem 4: the two-step root comparison"

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
# Kostov's eigenpolynomials

Every monic polynomial of degree $n$ with a root at $-1$ is a Schur–Szegő composition of $n-1$
polynomials $(x+1)^{n-1}(x+a_j)$, and Kostov studied the map from its coefficients to the
elementary symmetric functions of the $a_j$. The eigenvectors of the linear part of this map are
given by polynomials with simple positive roots, and consecutive ones interlace.

## Results

Fix $n\ge2$. *Kostov's coefficient map* sends the coefficients of a monic polynomial of degree
$n$ with a root at $-1$ to the elementary symmetric functions of the parameters $a_j$ in its
Schur–Szegő factorization [@KostovShapiro2006]. For $0\le k<n-1$ put
$$
\lambda_k=\frac{n^k}{(n-1)(n-2)\cdots(n-k)} .
$$

**Theorem (eigenvalues).** The linear part of the map has each $\lambda_k$ as an eigenvalue, with
a one-dimensional eigenspace.

**Theorem (reduced eigenpolynomials).** For $0\le j\le n-3$ there is a reduced eigenpolynomial
$Q_{n,j}$ giving an eigendirection for $\lambda_{j+1}$. It is monic of degree $j$, satisfies
$X^jQ_{n,j}(1/X)=(-1)^jQ_{n,j}(X)$, and vanishes at $1$ when $j$ is odd. Its roots are real,
simple and positive.

**Theorem (Kostov).** [@Kostov2010, Thm. 3] For $1\le j\le n-4$ we have
$Q_{n,j}\ll Q_{n,j+1}$.

**Theorem (Kostov).** [@Kostov2010, Thm. 4] Let $1\le j\le n-5$, let
$x_0<\dots<x_{j-1}$ be the roots of $Q_{n,j}$ and $z_0<\dots<z_{j+1}$ those of $Q_{n,j+2}$. For
$0\le i<j/2$,
$$
z_i<x_i<z_{i+1},\qquad z_{j-i}<x_{j-1-i}<z_{j+1-i},
$$
and for odd $j$ the middle roots satisfy $x_{(j-1)/2}=z_{(j+1)/2}=1$.

## Proof

In suitable coordinates the eigenproblem becomes that of a Bernstein-type operator. The proofs
then use a compactness argument for real zeros, Descartes' rule of signs, and a Wronskian
argument.

## References

- [@Kostov2010]
- [@KostovShapiro2006]
<!-- /realrooted-catalog-content -->
-/
