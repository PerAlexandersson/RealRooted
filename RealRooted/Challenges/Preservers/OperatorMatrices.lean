module

import RealRooted.OperatorMatrix.LocalToGlobal
import RealRooted.OperatorMatrix.Composition
import RealRooted.OperatorMatrix.Directed
import RealRooted.OperatorMatrix.MixedLemma
import RealRooted.OperatorMatrix.OneThetaX
import RealRooted.OperatorMatrix.OneThetaXBoards
import RealRooted.OperatorMatrix.OneThetaXBoardsExtra
import RealRooted.OperatorMatrix.EulerDerivativeLag
import RealRooted.OperatorMatrix.CouplingThresholds

/-!
# Operator matrices preserving ordered PF vectors

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "operator-matrices-ordered-pf"
formalized = "2026-11-03"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.OperatorMatrix.IsOrderedPF"
module = "RealRooted.OperatorMatrix.LocalToGlobal"
label = "Ordered PF vector"

[[definitions]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF"
module = "RealRooted.OperatorMatrix.LocalToGlobal"
label = "An operator matrix preserves ordered PF vectors"

[[definitions]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPFPair"
module = "RealRooted.OperatorMatrix.LocalToGlobal"
label = "A two-by-two operator block preserves ordered PF pairs"

[[definitions]]
name = "RealRooted.OperatorMatrix.Letter"
module = "RealRooted.OperatorMatrix.OneThetaX"
label = "The alphabet {1, θ, X}"

[[definitions]]
name = "RealRooted.OperatorMatrix.Letter.IsAllowedBlock"
module = "RealRooted.OperatorMatrix.OneThetaX"
label = "The thirteen allowed two-by-two blocks over {1, θ, X}"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.iff_forall_blocks_of_two_le"
module = "RealRooted.OperatorMatrix.LocalToGlobal"
label = "Local-to-global: ordered-PF preservation reduces to two-by-two blocks"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPFPair.iff_isAllowedBlock"
module = "RealRooted.OperatorMatrix.OneThetaX"
label = "A two-by-two block over {1, θ, X} preserves ordered PF pairs iff it is one of thirteen"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.letters_iff"
module = "RealRooted.OperatorMatrix.OneThetaX"
label = "Classification of ordered-PF preserving matrices over {1, θ, X}"
headline = true

[[theorems]]
name = "RealRooted.interl_derivative_add_derivative_add_X_mul_derivative"
module = "RealRooted.OperatorMatrix.MixedLemma"
label = "Mixed differential lemma: p' + q' ≪ q + X p' for PF p ≪ q"

[[theorems]]
name = "RealRooted.interl_iff_interl_X_mul"
module = "RealRooted.OperatorMatrix.Directed"
label = "X-duality: p ≪ q if and only if q ≪ X p for PF p and q"

[[theorems]]
name = "RealRooted.interl_add_X_mul_add_of_interl"
module = "RealRooted.OperatorMatrix.Directed"
label = "p ≪ q gives p + q ≪ X p + q for PF p and q"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.two_two_iff"
module = "RealRooted.OperatorMatrix.Composition"
label = "A two-by-two operator matrix preserves ordered PF vectors iff its block does"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.mul"
module = "RealRooted.OperatorMatrix.Composition"
label = "Products of ordered-PF preserving matrices preserve ordered PF vectors"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.one_theta_iff_upperRightRectangle"
module = "RealRooted.OperatorMatrix.OneThetaXBoards"
label = "Boards over {1, θ}: the 1 entries form an upper-right rectangle"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.theta_x_iff_rowCut_or_columnCut"
module = "RealRooted.OperatorMatrix.OneThetaXBoards"
label = "Boards over {θ, X}: a row cut or a column cut"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.one_row_letters_iff"
module = "RealRooted.OperatorMatrix.OneThetaXBoardsExtra"
label = "One-row matrices over {1, θ, X}: entries weakly decrease from left to right"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.one_column_letters_iff"
module = "RealRooted.OperatorMatrix.OneThetaXBoardsExtra"
label = "One-column matrices over {1, θ, X}: entries weakly increase from top to bottom"

[[theorems]]
name = "RealRooted.OperatorMatrix.card_oneThetaRectangleBoards"
module = "RealRooted.OperatorMatrix.OneThetaXBoardsExtra"
label = "There are exactly m n + 1 boards over {1, θ}"

[[theorems]]
name = "RealRooted.OperatorMatrix.card_thetaXCutBoards"
module = "RealRooted.OperatorMatrix.OneThetaXBoardsExtra"
label = "There are exactly m + n boards over {θ, X}"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.eulerDerivativeLag_twoStep"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "The matrix of P(n+2) = θP(n+1) + Xθ P(n) preserves ordered PF vectors"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.eulerDerivativeLag_transition_iff"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "Exactly the two alternating identity/Euler transitions preserve ordered PF vectors"

[[theorems]]
name = "RealRooted.OperatorMatrix.EulerDerivativeLag.splits_of_recurrence_one_X"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "Every row of P(n+2) = θP(n+1) + Xθ P(n) with P(0) = 1, P(1) = X splits"

[[definitions]]
name = "RealRooted.OperatorMatrix.CouplingRayCriterion"
module = "RealRooted.OperatorMatrix.CouplingThresholds"
label = "The scalar ray predicate for a coupling of two first-order operator blocks"

[[theorems]]
name = "RealRooted.OperatorMatrix.couplingRayCriterion_iff_sqrt_bounds"
module = "RealRooted.OperatorMatrix.CouplingThresholds"
label = "The ray criterion is equivalent to -2√(wtJ) ≤ S ≤ J + 2√(wtJ) for all t > 0"

[[theorems]]
name = "RealRooted.OperatorMatrix.couplingRayCriterion_quadratic_iff_of_boundary"
module = "RealRooted.OperatorMatrix.CouplingThresholds"
label = "For quadratic data on the boundary of the parameter cone the ray quantifier is eliminated"

[[theorems]]
name = "RealRooted.OperatorMatrix.couplingRayCriterion_cap_add_of_proportional"
module = "RealRooted.OperatorMatrix.CouplingThresholds"
label = "Raising the degree cap does not change the criterion for proportional blocks"

[[theorems]]
name = "RealRooted.OperatorMatrix.rayCriterion_theta_polar_iff"
module = "RealRooted.OperatorMatrix.CouplingThresholds"
label = "The (θ, polar) coupling holds exactly when N² ≤ 4w"
-->

<!-- realrooted-catalog-content -->
# Operator matrices preserving ordered PF vectors

A matrix of linear operators on polynomials preserves ordered Pólya frequency vectors if and
only if every $2\times2$ submatrix does. For entries among $1$, $\theta=x\,d/dx$ and $x$, exactly
thirteen $2\times2$ blocks do, which decides which operator recurrences of this kind have
interlacing PF rows.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. On this page $f\ll g$ also holds when $f$ or $g$ is zero, as in the
[zero-aware convention](rr:about). A vector $(f_1,\dotsc,f_n)$ is an *ordered PF vector* if
every $f_i$ is PF and $f_i\ll f_k$ for $i<k$.

An $m\times n$ *operator matrix* $M=(M_{ij})$ has real-linear operators on $\mathbb R[x]$
as entries and acts by $(Mf)_i=\sum_j M_{ij}f_j$. It *preserves ordered PF vectors* if $Mf$
is an ordered PF vector whenever $f$ is. A block $\begin{pmatrix}a&b\\c&d\end{pmatrix}$
*preserves ordered PF pairs* if, for all PF $f\ll g$, the polynomials $af+bg$ and $cf+dg$
are PF and $af+bg\ll cf+dg$.

**Theorem (local to global).** Let $m,n\ge2$. Then $M$ preserves ordered PF vectors if and
only if every $2\times2$ submatrix on rows $i<k$ and columns $j<l$, adjacent or not,
preserves ordered PF pairs. A $2\times2$ matrix preserves ordered PF vectors if and only if
its four entries form a block preserving ordered PF pairs, and products of matrices that
preserve ordered PF vectors preserve them.

**Theorem (blocks over $\{1,\theta,x\}$).** Let the entries be the identity $1$, the operator
$\theta$ and multiplication by $x$. A $2\times2$ block over this alphabet preserves ordered PF
pairs if and only if it is one of the following thirteen, written as (top row)/(bottom row):

- $(1,1)/(1,1)$, $(1,1)/(\theta,\theta)$, $(1,1)/(x,1)$, $(1,1)/(x,x)$;
- $(\theta,1)/(\theta,1)$, $(\theta,1)/(\theta,\theta)$, $(\theta,1)/(x,\theta)$;
- $(\theta,\theta)/(\theta,\theta)$, $(\theta,\theta)/(x,x)$;
- $(x,1)/(x,1)$, $(x,1)/(x,x)$, $(x,\theta)/(x,\theta)$, $(x,x)/(x,x)$.

Hence an $m\times n$ matrix over $\{1,\theta,x\}$ with $m,n\ge2$ preserves ordered PF vectors if
and only if every $2\times2$ submatrix is one of the thirteen blocks. A one-row matrix does if
and only if its entries weakly decrease from left to right in the order $1<\theta<x$, and a
one-column matrix if and only if its entries weakly increase from top to bottom. For
$m,n\ge2$, a matrix over $\{1,\theta\}$ does exactly when its entries equal to $1$ form an
upper-right rectangle, possibly empty ($mn+1$ matrices), and a matrix over $\{\theta,x\}$ does
exactly when all rows are equal, with $x$ columns followed by $\theta$ columns, or all columns
are equal, with $\theta$ rows followed by $x$ rows ($m+n$ matrices).

**Proposition.** For PF polynomials $p$ and $q$:

- if $p\ll q$, then $p'+q'\ll q+xp'$;
- $p\ll q$ if and only if $q\ll xp$;
- if $p\ll q$, then $p+q\ll xp+q$.

**Corollary (Euler-derivative lag recurrence).** Let $P_{n+2}=\theta P_{n+1}+x\,\theta P_n$.
The matrix
$$
\begin{pmatrix}x\theta&\theta\\ x(\theta^2+\theta)&x\theta+\theta^2\end{pmatrix}
$$
sends $(P_n,P_{n+1})$ to $(P_{n+2},P_{n+3})$ and preserves ordered PF vectors. Among the
nine transitions between the lag factors $1$, $\theta$ and $x$, exactly the two alternating
identity/Euler transitions preserve ordered PF vectors. If $P_0=1$ and $P_1=x$, then every
$P_n$ is real-rooted.

For couplings of two first-order blocks $a+b\theta+cx+e\,x(N-\theta)$, a scalar criterion on
the negative ray with a weight $w\ge0$ reduces to explicit inequalities. For the pair
$(\theta,\,x(N-\theta))$ it holds exactly when $N^2\le4w$, and for the reversed pair, with
$N\ge1$, exactly when $(N-1)^2\le4w$.

## References

- [Matrices preserving interlacing sequences](rr:matrix-interlacing), for entries that are
  multiplications by polynomials
- [Operators preserving interlacing](rr:operator-preservers)
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.OperatorMatrix`
modules named in the metadata.
-/
