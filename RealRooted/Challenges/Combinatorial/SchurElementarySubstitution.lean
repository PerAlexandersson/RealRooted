module

public import RealRooted.Schur.ElementarySubstitution

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

[[theorems]]
name = "RealRooted.Schur.isPFPolynomial_det_active"
module = "RealRooted.Schur.ElementarySubstitution"
label = "Conditional parity criterion for a totally nonnegative determinant pencil"
headline = true
-->

<!-- realrooted-catalog-content -->
# Schur elementary-coordinate substitutions

**Formalization status:** the conditional matrix criterion below is checked.
The full Schur specialization, stretching corollaries, and consecutive
interlacing remain open in [issue #2443](https://github.com/PerAlexandersson/RealRooted/issues/2443).
They are targets here, not claims of completed Lean proofs.

## Checked matrix criterion

Let $a_i$ and $b_j$ be strictly decreasing integer lists and let
$V_{ij}=\mathbf1_{a_i=b_j+r}$. If $M$ is totally nonnegative with
$\det M>0$, and $i+j$ is even at every active position, then
$\det(M+tV)$ is a Pólya-frequency polynomial. The proof identifies $V$
as an ordered submatrix of the identity and applies the existing
checkerboard determinant-pencil theorem. The assumptions on $M$ are
explicit hypotheses of the checked theorem.

## Schur specialization target

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

For a positive alphabet of size at least the maximum skew column height,
the remaining proof obligations are total nonnegativity of $M$ and
$\det M>0$. Under even active-position parity the target conclusion is
strictly negative real zeros. Odd active-position parity gives positive
zeros instead. Nonzero constants, repeated roots, and empty shapes must
be included explicitly.

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
The intended general matrix proof uses nonnegative corner perturbations
of both matrices in a TN pencil, followed by the existing compatibility
criterion. This interlacing result requires its own proof; individual
real-rootedness does not suffice.

The unrestricted arbitrary-shape specialization is false. Neither this
challenge nor its checked conditional criterion proves the conjecture
relating a real limiting Toeplitz spectrum to finite real-rootedness.

## References

- [Supplied proof note and implementation plan](https://github.com/PerAlexandersson/RealRooted/issues/2443).
- Chi-Kwong Li and Roy Mathias,
  [Interlacing Inequalities for Totally Nonnegative Matrices](https://cklixx.people.wm.edu/tpinter.pdf).
<!-- /realrooted-catalog-content -->
-/
