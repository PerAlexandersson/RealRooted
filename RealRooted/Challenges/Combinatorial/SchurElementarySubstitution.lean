module

public import RealRooted.Schur.ConstantColumns
public import RealRooted.Schur.Rectangular
public import RealRooted.TotallyNonnegPencil.CornerInterlacing
import RealRooted.Schur.MinorPositivity

/-!
# Schur elementary-coordinate substitutions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "schur-elementary-substitution"
formalized = "2026-11-07"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.Schur.activeMatrix"
module = "RealRooted.Schur.ElementarySubstitution"
label = "Positions affected by an elementary-coordinate substitution"

[[definitions]]
name = "RealRooted.Schur.elementarySubstitution"
module = "RealRooted.Schur.ElementaryToeplitz"
label = "Elementary-coordinate specialization defined by a determinant"

[[theorems]]
name = "RealRooted.Schur.elementaryMatrix_isTotallyNonneg"
module = "RealRooted.Schur.ElementaryToeplitz"
label = "Elementary skew Jacobi–Trudi matrices are totally nonnegative"

[[theorems]]
name = "RealRooted.Schur.elementarySubstitution_isPFPolynomial"
module = "RealRooted.Schur.ElementaryToeplitz"
label = "Parity-compatible specialization assuming positive constant determinant"

[[theorems]]
name = "Matrix.IsTotallyNonneg.strictInterl_checkerboardPencil_succ"
module = "RealRooted.TotallyNonnegPencil.CornerInterlacing"
label = "Corner-section interlacing for general totally nonnegative pencils"

[[theorems]]
name = "RealRooted.Schur.isPFPolynomial_det_active"
module = "RealRooted.Schur.ElementarySubstitution"
label = "Conditional parity criterion for a totally nonnegative determinant pencil"

[[theorems]]
name = "RealRooted.Schur.det_elementaryMatrix_pos_of_nonneg"
module = "RealRooted.Schur.ElementaryPositivity"
label = "Positive constant determinant from the number of positive letters"

[[theorems]]
name = "RealRooted.Schur.elementarySubstitution_isRealRooted"
module = "RealRooted.Schur.Roots"
label = "Real-rooted dual Jacobi–Trudi specialization under alphabet-size and parity hypotheses"
headline = true

[[theorems]]
name = "RealRooted.Schur.roots_elementarySubstitution_neg"
module = "RealRooted.Schur.Roots"
label = "All roots of the parity-compatible specialization are strictly negative"

[[theorems]]
name = "Matrix.IsTotallyNonneg.strictInterl_checkerboardPencil_castSucc"
module = "RealRooted.TotallyNonnegPencil.CornerInterlacing"
label = "Consecutive leading sections of general TN pencils interlace"

[[definitions]]
name = "RealRooted.Schur.rectangularElementarySubstitution"
module = "RealRooted.Schur.Rectangular"
label = "Signed rectangular elementary-coordinate deformation"

[[definitions]]
name = "RealRooted.Schur.repeatColumns"
module = "RealRooted.Schur.Stretching"
label = "Horizontal stretching by repetition of column heights"

[[theorems]]
name = "RealRooted.Schur.elementarySubstitution_isRealRooted_of_odd"
module = "RealRooted.Schur.PositiveRoots"
label = "Real-rootedness under odd active-position parity"

[[theorems]]
name = "RealRooted.Schur.roots_elementarySubstitution_pos_of_odd"
module = "RealRooted.Schur.PositiveRoots"
label = "Strictly positive roots under odd active-position parity"

[[theorems]]
name = "RealRooted.Schur.repeatColumns_isRealRooted"
module = "RealRooted.Schur.Stretching"
label = "Every horizontal stretch is real-rooted under even boundary parity"

[[theorems]]
name = "RealRooted.Schur.roots_repeatColumns_neg"
module = "RealRooted.Schur.Stretching"
label = "Strictly negative roots under all horizontal stretches"

[[theorems]]
name = "RealRooted.Schur.repeatColumns_isRealRooted_of_odd"
module = "RealRooted.Schur.Stretching"
label = "Every horizontal stretch is real-rooted under odd boundary parity"

[[theorems]]
name = "RealRooted.Schur.roots_repeatColumns_pos"
module = "RealRooted.Schur.Stretching"
label = "Strictly positive roots for odd-parity horizontal stretches"

[[theorems]]
name = "RealRooted.Schur.elementarySubstitution_eq_det_add_X_one"
module = "RealRooted.Schur.ConstantColumns"
label = "Constant skew column height gives det(M+tI)"

[[theorems]]
name = "RealRooted.Schur.repeatColumns_isRealRooted_of_constant_height"
module = "RealRooted.Schur.ConstantColumns"
label = "All constant-column-height stretches are real-rooted"

[[theorems]]
name = "RealRooted.Schur.roots_repeatColumns_neg_of_constant_height"
module = "RealRooted.Schur.ConstantColumns"
label = "Constant-column-height stretches have negative roots"

[[theorems]]
name = "RealRooted.Schur.repeatColumns_double_isRealRooted"
module = "RealRooted.Schur.ConstantColumns"
label = "Duplicating rows gives real-rooted families for every even moving coordinate"

[[theorems]]
name = "RealRooted.Schur.roots_repeatColumns_double_neg"
module = "RealRooted.Schur.ConstantColumns"
label = "Duplicated-row families have negative roots under all stretches"

[[theorems]]
name = "RealRooted.Schur.strictInterl_elementarySubstitution_succ"
module = "RealRooted.Schur.Interlacing"
label = "Consecutive compatible skew suffixes interlace"

[[theorems]]
name = "RealRooted.Schur.rectangularElementarySubstitution_eq_det"
module = "RealRooted.Schur.Rectangular"
label = "The rectangular definition equals the signed elementary substitution"

[[theorems]]
name = "RealRooted.Schur.rectangularElementarySubstitution_isRealRooted"
module = "RealRooted.Schur.Rectangular"
label = "Every signed rectangular specialization is real-rooted"

[[theorems]]
name = "RealRooted.Schur.roots_rectangularElementarySubstitution_neg"
module = "RealRooted.Schur.Rectangular"
label = "Every signed rectangular specialization has negative roots"

[[theorems]]
name = "RealRooted.Schur.strictInterl_rectangularElementarySubstitution"
module = "RealRooted.Schur.Rectangular"
label = "Consecutive rectangular widths interlace for every moving coordinate"

[[theorems]]
name = "RealRooted.Schur.det_toeplitz_prod_linear_pos"
module = "RealRooted.Schur.MinorPositivity"
label = "Supported minors of Toeplitz matrices of positive linear-factor products are positive"

[[theorems]]
name = "RealRooted.Schur.det_bidiagonal_submatrix_pos"
module = "RealRooted.Schur.MinorPositivity"
label = "Supported minors of a bidiagonal Toeplitz matrix are strictly positive"
-->

<!-- realrooted-catalog-content -->
# Schur elementary-coordinate substitutions

Replacing one elementary symmetric function $e_r$ by $e_r+t$ in the dual Jacobi–Trudi
determinant of a skew Schur function, evaluated at a nonnegative alphabet, gives a polynomial
in $t$ with only real zeros. A parity condition on the positions where $e_r$ occurs decides
whether the zeros are negative or positive.

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
$\Phi$ replaces $e_r$ by $e_r+t$ in every position with $a_i=b_j+r$, also when $r$ exceeds the
number of letters.

**Theorem.** Let $\alpha$ be a finite alphabet of nonnegative reals with $p$ positive letters,
let $h,k$ be weakly decreasing with $k_i\le h_i\le k_i+p$, and let $r\in\mathbb Z$. Then $M$ is
totally nonnegative and $\det M>0$. If $i+j$ is even whenever $a_i=b_j+r$, then
$\Phi_{\lambda/\mu,r}$ is a nonzero Pólya frequency polynomial with only real, strictly negative
zeros (constants and empty shapes included). If $i+j$ is odd whenever $a_i=b_j+r$, then
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

Further consequences: let $\lambda^{(m)}/\mu^{(m)}$ repeat each column $m$ times, with
$r\in\mathbb N$. If $h_i+k_j+r$ is even for all $i,j$, every $\Phi_{\lambda^{(m)}/\mu^{(m)},r}$
is nonzero and real-rooted with strictly negative zeros, and if it is odd for all $i,j$, with
strictly positive zeros. If $h_i=k_i+r$ for all $i$ and $r\le p$, then $\Phi=\det(M+tI)$ and all
stretches have strictly negative real zeros with no parity condition. If $k_i\le h_i$ and
$2h_i\le 2k_i+p$, doubling both height lists gives nonzero real-rooted polynomials with strictly
negative zeros for the moving coordinate $2r$, for every $r,m\ge0$.

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
