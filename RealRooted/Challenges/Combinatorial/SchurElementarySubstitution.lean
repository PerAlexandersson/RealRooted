module

import RealRooted.Schur.ElementaryPositivity
import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.Interlacing
import RealRooted.Schur.PositiveRoots
import RealRooted.Schur.Rectangular
import RealRooted.Schur.Roots
import RealRooted.TotallyNonnegPencil.CornerInterlacing

/-!
# Real zeros of deformed skew Schur determinants

<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "schur-elementary-substitution"
formalized = "2026-11-07"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.Schur.elementarySubstitution"
module = "RealRooted.Schur.ElementaryToeplitz"
label = "Φ(t) = det(M + tV): e_r replaced by e_r + t in a dual Jacobi–Trudi matrix"

[[definitions]]
name = "RealRooted.Schur.rectangularElementarySubstitution"
module = "RealRooted.Schur.Rectangular"
label = "Signed elementary substitution for a rectangular shape"

[[theorems]]
name = "RealRooted.Schur.elementarySubstitution_isRealRooted"
module = "RealRooted.Schur.Roots"
label = "Replacing e_r by e_r + t in a dual Jacobi–Trudi determinant gives a real-rooted polynomial"
headline = true

[[theorems]]
name = "RealRooted.Schur.roots_elementarySubstitution_neg"
module = "RealRooted.Schur.Roots"
label = "With even parity all roots are negative"

[[theorems]]
name = "RealRooted.Schur.elementarySubstitution_isRealRooted_of_odd"
module = "RealRooted.Schur.PositiveRoots"
label = "With odd parity the polynomial is also real-rooted"

[[theorems]]
name = "RealRooted.Schur.roots_elementarySubstitution_pos_of_odd"
module = "RealRooted.Schur.PositiveRoots"
label = "With odd parity all roots are positive"

[[theorems]]
name = "RealRooted.Schur.elementaryMatrix_isTotallyNonneg"
module = "RealRooted.Schur.ElementaryToeplitz"
label = "Dual Jacobi–Trudi matrices at a nonnegative alphabet are totally nonnegative"

[[theorems]]
name = "RealRooted.Schur.det_elementaryMatrix_pos_of_nonneg"
module = "RealRooted.Schur.ElementaryPositivity"
label = "Their determinant is positive when each skew column height is at most p"

[[theorems]]
name = "RealRooted.Schur.strictInterl_elementarySubstitution_succ"
module = "RealRooted.Schur.Interlacing"
label = "Removing the first column gives an interlacing polynomial"

[[theorems]]
name = "RealRooted.Schur.rectangularElementarySubstitution_isRealRooted"
module = "RealRooted.Schur.Rectangular"
label = "Rectangular substitutions are nonzero and real-rooted"

[[theorems]]
name = "RealRooted.Schur.strictInterl_rectangularElementarySubstitution"
module = "RealRooted.Schur.Rectangular"
label = "Rectangular substitutions of consecutive widths interlace"

[[theorems]]
name = "Matrix.IsTotallyNonneg.strictInterl_checkerboardPencil_succ"
module = "RealRooted.TotallyNonnegPencil.CornerInterlacing"
label = "det(A′ + t cb(B′)) ≪ det(A + t cb(B)) for totally nonnegative A, B"

-->

<!-- realrooted-catalog-content -->
# Real zeros of deformed skew Schur determinants

Replacing one elementary symmetric function $e_r$ by $e_r+t$ in the dual Jacobi–Trudi
determinant of a skew Schur function, evaluated at nonnegative reals, gives a polynomial in $t$
with only real zeros. A parity condition on the positions of $e_r$ decides whether the zeros are
negative or positive.

## Results

For a finite alphabet $\alpha$ let $e_m(\alpha)$ be the coefficient of $x^m$ in
$\prod_i(1+\alpha_i x)$, with $e_m=0$ for $m<0$. For weakly decreasing column heights
$h=\lambda'$ and $k=\mu'$ (the shorter list padded with zeros to a common length $n$), set
$a_i=h_i-i$, $b_j=k_j-j$, and for $r\in\mathbb Z$
$$
M_{ij}=e_{a_i-b_j}(\alpha),\qquad V_{ij}=\mathbf 1_{a_i=b_j+r},\qquad
\Phi_{\lambda/\mu,r}(t;\alpha)=\det(M+tV),
$$
with indices from $0$. Here $\det M=s_{\lambda/\mu}(\alpha)$ in dual Jacobi–Trudi form, and
$\Phi$ replaces $e_r$ by $e_r+t$ in every position with $a_i=b_j+r$.

**Theorem (real zeros).** Let $\alpha$ be a finite alphabet of nonnegative reals with $p$ positive
letters, let $h,k$ be weakly decreasing with $k_i\le h_i\le k_i+p$, and let $r\in\mathbb Z$. Then
$M$ is totally nonnegative and $\det M>0$. If $i+j$ is even whenever $a_i=b_j+r$, then
$\Phi_{\lambda/\mu,r}$ is a nonzero Pólya frequency polynomial with only real, strictly negative
zeros. If $i+j$ is odd whenever $a_i=b_j+r$, then
$\Phi_{\lambda/\mu,r}$ is nonzero and real-rooted with only strictly positive zeros.

**Theorem (consecutive shapes).** Under the hypotheses above with $n+1$ columns and even parity,
the shape $(\lambda/\mu)^-$ with its first column removed satisfies
$\Phi_{(\lambda/\mu)^-,r}\ll\Phi_{\lambda/\mu,r}$.

**Theorem (rectangles).** Let $\alpha$ have at least $r$ positive letters, let $j\ge0$, and put
$$
F_n(t)=\det\Bigl(e_{r-u+v}(\alpha)+(-1)^{r+j}\,t\,\mathbf 1_{r-u+v=j}\Bigr)_{u,v=0}^{n-1},
\qquad F_0=1.
$$
Then every $F_n$ is nonzero and real-rooted with strictly negative zeros, and
$F_n\ll F_{n+1}$ for all $n\ge0$, with no parity condition on $r$ or $j$.

**Theorem (pencils).** Let $A,B$ be totally nonnegative matrices of size $n+1$ with $\det A>0$,
and let $\mathrm{cb}(B)_{ij}=(-1)^{i+j}B_{ij}$. Let $A',B'$ be obtained by removing the first
row and column and suppose $\det A'>0$. Then
$$
\det(A'+t\,\mathrm{cb}(B'))\ll\det(A+t\,\mathrm{cb}(B)).
$$
The same holds when the last row and column are removed instead, if the resulting section of
$A$ has positive determinant; $B$ need be neither triangular nor invertible. Consequently, if
$a_i,b_j$ are strictly decreasing, $M$ is totally nonnegative with $\det M>0$ and $i+j$ is even
whenever $a_i=b_j+r$, then $\det(M+tV)$ is a Pólya frequency polynomial.

## Use

Under the size and parity conditions, every skew Schur function at nonnegative reals has a
real-rooted deformation, and rectangles give interlacing sequences with no parity condition. The
pencil theorem holds for all [totally nonnegative matrices](rr:totally-nonnegative-matrices);
compare the interlacing inequalities of Li and Mathias.

## Proof

The matrix $V$ is an ordered submatrix of the identity, hence totally nonnegative, and even
parity makes it invariant under the checkerboard sign change, so the pencil theorem applies.
Positivity of $\det M$ follows because, for $a_i>0$, every minor of the Toeplitz matrix of
$\prod_i(x+a_i)$ with strictly increasing rows and columns inside its band is strictly positive.
For odd parity we reflect $t\mapsto-t$.

## References

C.-K. Li and R. Mathias,
[Interlacing Inequalities for
Totally Nonnegative Matrices](https://cklixx.people.wm.edu/tpinter.pdf).
<!-- /realrooted-catalog-content -->
-/
