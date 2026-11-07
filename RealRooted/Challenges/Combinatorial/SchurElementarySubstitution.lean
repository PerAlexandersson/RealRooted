module

public import RealRooted.Schur.Roots
public import RealRooted.TotallyNonnegPencil.CornerInterlacing

/-!
# Schur elementary-coordinate substitution challenge

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "schur-elementary-substitution"
formalized = "2026-11-07"

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
label = "Real-rooted skew Schur specialization under alphabet-size and parity hypotheses"
headline = true

[[theorems]]
name = "RealRooted.Schur.roots_elementarySubstitution_neg"
module = "RealRooted.Schur.Roots"
label = "All roots of the parity-compatible specialization are strictly negative"
-->

<!-- realrooted-catalog-content -->
# Schur elementary-coordinate substitutions

**Formalization status:** the even-parity skew Schur specialization now has
a checked real-rootedness proof with strictly negative zeros. Both total
nonnegativity and strict determinant positivity follow from the alphabet
and shape hypotheses. Odd-parity positive zeros, stretching corollaries,
and the Schur application of consecutive interlacing remain open in [issue #2443](https://github.com/PerAlexandersson/RealRooted/issues/2443).
Those remaining results are targets, not claims of completed Lean proofs.

## Checked matrix criterion

Let $a_i$ and $b_j$ be strictly decreasing integer lists and let
$V_{ij}=\mathbf1_{a_i=b_j+r}$. If $M$ is totally nonnegative with
$\det M>0$, and $i+j$ is even at every active position, then
$\det(M+tV)$ is a Pólya-frequency polynomial. The proof identifies $V$
as an ordered submatrix of the identity and applies the existing
checkerboard determinant-pencil theorem. The assumptions on $M$ are
explicit hypotheses of the checked theorem.

## Checked skew Schur specialization

For column heights $h=\lambda'$ and $k=\mu'$ (padding $k$ with zeros), set
$a_i=h_i-i$, $b_j=k_j-j$, and

$$
M_{ij}=e_{a_i-b_j}(\alpha),\qquad
\Phi_{\lambda/\mu,r}(t;\alpha)=\det(M+tV).
$$

We use this dual Jacobi–Trudi determinant as the definition; a bridge to
an independent symmetric-function definition is not required. Here $e_0=1$
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
should give positive zeros instead; that reflection corollary remains open.

Uniform parity of both padded column-height lists should yield the result
under every simultaneous horizontal stretch: stretching repeats columns,
not their heights. Constant skew column height $r$ gives $V=I$.

## Consecutive rectangular interlacing target

For a nonnegative alphabet with at least $r$ positive letters, define

$$
F_n(t)=\det\left(e_{r-p+q}(\alpha)
 +(-1)^{j-r}t\,\mathbf1_{r-p+q=j}\right)_{p,q=0}^{n-1},\qquad F_0=1.
$$

For every moving coordinate $j\ge1$, the target is negative real zeros
and oriented weak interlacing $F_{n-1}\preceq F_n$. Equal degrees and
common roots are allowed; no general strictness is asserted.
The general matrix step is checked: consecutive southeast sections of a
checkerboard-signed TN pencil interlace when their constant determinants
are positive. The proof uses nonnegative northwest-corner perturbations
of both matrices, followed by the compatibility criterion. No triangularity
is required of the variable matrix. Applying this theorem to rectangular
Schur matrices remains open; determinant positivity is now available from
the alphabet-size theorem.

The unrestricted arbitrary-shape specialization is false. Neither this
challenge nor its checked conditional criterion proves the conjecture
relating a real limiting Toeplitz spectrum to finite real-rootedness.

## References

- [Supplied proof note and implementation plan](https://github.com/PerAlexandersson/RealRooted/issues/2443).
- Chi-Kwong Li and Roy Mathias,
  [Interlacing Inequalities for Totally Nonnegative Matrices](https://cklixx.people.wm.edu/tpinter.pdf).
<!-- /realrooted-catalog-content -->
-/
