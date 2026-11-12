module

public import RealRooted.Schur.ConstantColumns
public import RealRooted.Schur.Rectangular
public import RealRooted.TotallyNonnegPencil.CornerInterlacing
import RealRooted.Schur.MinorPositivity

/-!
# Schur elementary-coordinate substitution challenge

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

**Provenance.** The parity-compatible specialization theorem, its stretching
and truncation variants, and the checkerboard pencil interlacing behind them
are new results; their proofs were developed for RealRooted and are of independent research
interest.

**Formalization status:** checked Lean proofs cover both parity cases,
horizontal stretching, duplicated rows, constant skew column height,
compatible nested skew truncations, and signed rectangular consecutive
interlacing. Schur functions themselves are not defined here: the objects are
determinants of elementary coefficients (dual Jacobi–Trudi matrices), and no
bridge to an independent definition of skew Schur functions is formalized.

## Checked matrix criterion

Let $a_i$ and $b_j$ be strictly decreasing integer lists and let
$V_{ij}=\mathbf1_{a_i=b_j+r}$. If $M$ is totally nonnegative with
$\det M>0$, and $i+j$ is even at every active position, then
$\det(M+tV)$ is a Pólya-frequency polynomial. The proof identifies $V$
as an ordered submatrix of the identity and applies the existing
checkerboard determinant-pencil theorem. The assumptions on $M$ are
explicit hypotheses of the checked theorem.

## Checked dual Jacobi–Trudi specialization

For column heights $h=\lambda'$ and $k=\mu'$ (padding $k$ with zeros), set
$a_i=h_i-i$, $b_j=k_j-j$, and

$$
M_{ij}=e_{a_i-b_j}(\alpha),\qquad
\Phi_{\lambda/\mu,r}(t;\alpha)=\det(M+tV).
$$

We use this dual Jacobi–Trudi determinant of elementary coefficients as the
definition, with `elementaryPolynomial` equal to $\prod_i(1+\alpha_i x)$. Here $e_0=1$
and $e_m=0$ for negative indices. Substitution is made before alphabet
specialization: even if $r$ exceeds the alphabet size, the moving
coordinate becomes $t$, rather than disappearing.

For a nonnegative alphabet with at least as many positive letters as the
maximum skew column height, both total nonnegativity of $M$ and
$\det M>0$ are checked. Under even active-position parity, the polynomial
is nonzero, splits over the reals, and has strictly negative roots.
Nonzero constants, repeated roots, and empty shapes are included.
The proof of strict positivity uses a positive Cauchy–Binet summand in
the product of elementary bidiagonal factors. Odd active-position parity
gives strictly positive zeros by reflecting the parameter; this is also checked.

Uniform parity of both padded column-height lists gives the result under
every simultaneous horizontal stretch: stretching repeats columns, not
their heights. Both signs are checked, including empty stretches. Duplicating
every row doubles both column-height lists, so every even moving coordinate
gives negative roots after any stretch. Constant skew column height $r$
gives $V=I$ and negative roots after every stretch without uniform boundary parity,
provided the alphabet has at least $r$ positive letters.

## Consecutive rectangular and skew interlacing

For a nonnegative alphabet with at least $r$ positive letters, define

$$
F_n(t)=\det\left(e_{r-p+q}(\alpha)
 +(-1)^{j-r}t\,\mathbf1_{r-p+q=j}\right)_{p,q=0}^{n-1},\qquad F_0=1.
$$

For every moving coordinate $j\ge1$, the checked conclusions are negative real zeros
and oriented weak interlacing $F_{n-1}\preceq F_n$. Equal degrees and
common roots are allowed; no general strictness is asserted.
The general matrix step is checked: consecutive southeast sections of a
checkerboard-signed TN pencil interlace when their constant determinants
are positive. The proof uses nonnegative northwest-corner perturbations
of both matrices, followed by the compatibility criterion. No triangularity
is required of the variable matrix. Its rectangular application is checked
for every height and moving coordinate. The sign uses $(-1)^{r+j}$ in Lean,
which has the same parity as the integer exponent $j-r$.

For even-parity skew shapes, consecutive suffixes of the two boundary lists
also interlace. This does not assert interlacing between successive horizontal
stretches of an arbitrary shape: their degrees can differ by more than one.

This challenge does not prove the conjecture relating a real limiting Toeplitz
spectrum to finite real-rootedness.

## Positive supported minors

For positive $a_i$, the infinite Toeplitz matrix of the coefficient sequence of
$\prod_{i\in s}(x+a_i)$ has a band of width $|s|$ below the diagonal. Every minor whose
rows and columns are strictly increasing and lie in that band, that is, with
$\mathrm{col}_i\le\mathrm{row}_i\le\mathrm{col}_i+|s|$, is strictly positive. The proof starts
with the bidiagonal matrix of a single factor, whose supported minors are positive for
$a>0$, and multiplies one linear factor at a time, since Toeplitz matrices of coefficient
sequences multiply with the polynomials.

## References

- Chi-Kwong Li and Roy Mathias,
  [Interlacing Inequalities for Totally Nonnegative Matrices](https://cklixx.people.wm.edu/tpinter.pdf).
<!-- /realrooted-catalog-content -->
-/
