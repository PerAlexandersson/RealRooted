module

import RealRooted.OperatorMatrix.LocalToGlobal
import RealRooted.OperatorMatrix.Composition
import RealRooted.OperatorMatrix.Directed
import RealRooted.OperatorMatrix.MixedLemma
import RealRooted.OperatorMatrix.OneThetaX
import RealRooted.OperatorMatrix.OneThetaXBoards
import RealRooted.OperatorMatrix.OneThetaXBoardsExtra
import RealRooted.OperatorMatrix.EulerDerivativeLag

/-!
# Operator matrices preserving ordered PF vectors

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "operator-matrices-ordered-pf"
formalized = "2026-11-03"
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
name = "RealRooted.OperatorMatrix.preservesOrderedPF_iff_preservesBlock_of_two_le"
module = "RealRooted.OperatorMatrix.LocalToGlobal"
label = "Local-to-global: ordered-PF preservation reduces to two-by-two blocks"
headline = true

[[theorems]]
name = "RealRooted.OperatorMatrix.preservesOrderedPFPair_iff_isAllowedBlock"
module = "RealRooted.OperatorMatrix.OneThetaX"
label = "A two-by-two block over {1, θ, X} preserves ordered PF pairs iff it is one of thirteen"
headline = true

[[theorems]]
name = "RealRooted.OperatorMatrix.preservesOrderedPF_letters_iff"
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
name = "RealRooted.OperatorMatrix.preservesOrderedPF_two_two_iff"
module = "RealRooted.OperatorMatrix.Composition"
label = "A two-by-two operator matrix preserves ordered PF vectors iff its block does"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.mul"
module = "RealRooted.OperatorMatrix.Composition"
label = "Products of ordered-PF preserving matrices preserve ordered PF vectors"

[[theorems]]
name = "RealRooted.OperatorMatrix.preservesOrderedPF_one_theta_iff_upperRightRectangle"
module = "RealRooted.OperatorMatrix.OneThetaXBoards"
label = "Boards over {1, θ}: the 1 entries form an upper-right rectangle"

[[theorems]]
name = "RealRooted.OperatorMatrix.preservesOrderedPF_theta_x_iff_rowCut_or_columnCut"
module = "RealRooted.OperatorMatrix.OneThetaXBoards"
label = "Boards over {θ, X}: a row cut or a column cut"

[[theorems]]
name = "RealRooted.OperatorMatrix.preservesOrderedPF_one_row_letters_iff"
module = "RealRooted.OperatorMatrix.OneThetaXBoardsExtra"
label = "One-row matrices over {1, θ, X}: entries weakly decrease from left to right"

[[theorems]]
name = "RealRooted.OperatorMatrix.preservesOrderedPF_one_column_letters_iff"
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
name = "RealRooted.OperatorMatrix.EulerDerivativeLag.preservesOrderedPF_twoStep"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "The dense two-step matrix of P(n+2) = θP(n+1) + Xθ P(n) preserves ordered PF vectors"

[[theorems]]
name = "RealRooted.OperatorMatrix.EulerDerivativeLag.preservesOrderedPF_transition_iff"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "Exactly the two alternating identity/Euler transitions preserve ordered PF vectors"

[[theorems]]
name = "RealRooted.OperatorMatrix.EulerDerivativeLag.splits_of_recurrence_one_X"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "Every row of P(n+2) = θP(n+1) + Xθ P(n) with P(0) = 1, P(1) = X splits"
-->

<!-- realrooted-catalog-content -->
# Operator matrices preserving ordered PF vectors

Throughout, a polynomial is **PF** if it is zero or has nonnegative coefficients
and only real, nonpositive roots, and $p\ll q$ is the directed, zero-aware
interlacing of the [interlacing page](/RealRooted/concepts/interlacing/): either
polynomial may be zero, and otherwise $q$ carries the rightmost root. A vector
$(f_1,\dots,f_n)$ of polynomials is an **ordered PF vector** if every $f_i$ is
PF and $f_i\ll f_k$ whenever $i<k$.

An $m\times n$ **operator matrix** $M=(M_{ij})$ has real-linear operators
$M_{ij}$ on $\mathbb R[x]$ as entries and acts by
$(Mf)_i=\sum_j M_{ij}f_j$. It **preserves ordered PF vectors** if $Mf$ is an
ordered PF vector whenever $f$ is. A $2\times2$ block
$\begin{pmatrix}a&b\\c&d\end{pmatrix}$ **preserves ordered PF pairs** if, for all
PF $f\ll g$, the polynomials $af+bg$ and $cf+dg$ are PF and
$af+bg\ll cf+dg$. If the entries are multiplications by polynomials, this is the
setting of the [matrix interlacing](/RealRooted/theorems/matrix-interlacing/) page; here
the entries may also be differential operators.

## Local-to-global principle

**Theorem.** Let $m,n\ge2$. Then $M$ preserves ordered PF vectors if and only if
every $2\times2$ submatrix on rows $i<k$ and columns $j<l$, adjacent or not,
preserves ordered PF pairs.

Consequently a $2\times2$ matrix preserves ordered PF vectors exactly when its
four entries form a block preserving ordered PF pairs, and the property is closed
under matrix products and powers.

## The alphabet $\{1,\theta,x\}$

Let $\theta=x\,d/dx$ be the Euler operator. We classify matrices whose entries lie
in the alphabet $\{1,\theta,x\}$, meaning the identity, $\theta$, and
multiplication by $x$. Three facts about PF polynomials $p\ll q$ drive the
classification:

- $p\ll\theta p\ll xp$ for every PF polynomial $p$;
- ($x$-duality) $p\ll q$ if and only if $q\ll xp$;
- (mixed differential lemma) $p'+q'\ \ll\ q+xp'$.

The mixed differential lemma is the delicate input. It is proved first for
coprime, strictly interlacing inputs by a Lagrange-interpolation residue
computation and then extended to all PF pairs, zeros and repeated roots
included, by separating the merged ordered root lists and passing to a
coefficientwise limit.

**Theorem (blocks).** A $2\times2$ block over $\{1,\theta,x\}$ preserves
ordered PF pairs if and only if it is one of the following thirteen blocks,
written as (top row)/(bottom row):

- $(1,1)/(1,1)$, $(1,1)/(\theta,\theta)$, $(1,1)/(x,1)$, $(1,1)/(x,x)$;
- $(\theta,1)/(\theta,1)$, $(\theta,1)/(\theta,\theta)$, $(\theta,1)/(x,\theta)$;
- $(\theta,\theta)/(\theta,\theta)$, $(\theta,\theta)/(x,x)$;
- $(x,1)/(x,1)$, $(x,1)/(x,x)$, $(x,\theta)/(x,\theta)$, $(x,x)/(x,x)$.

Necessity uses explicit counterexamples; the block $(\theta,1)/(\theta,\theta)$
rests on the mixed differential lemma.

**Theorem (rectangular matrices).** Let $L$ be an $m\times n$ matrix over
$\{1,\theta,x\}$ with $m,n\ge2$. Then $L$ preserves ordered PF vectors if and only
if every $2\times2$ submatrix on rows $i<k$ and columns $j<l$ is one of the
thirteen allowed blocks.

The singleton shapes complete the picture: a one-row matrix preserves ordered PF
vectors exactly when its entries weakly decrease from left to right in the order
$1<\theta<x$, and a one-column matrix exactly when its entries weakly increase
from top to bottom.

For two-letter alphabets the classification becomes explicit boards (for
$m,n\ge2$):

- over $\{1,\theta\}$, the entries equal to $1$ must form an upper-right
  rectangle, possibly empty, so there are exactly $mn+1$ such matrices;
- over $\{\theta,x\}$, either all rows are equal ($x$ columns followed by
  $\theta$ columns) or all columns are equal ($\theta$ rows followed by $x$
  rows), so there are exactly $m+n$ such matrices.

## An application: the Euler-derivative lag recurrence

Consider $P_{n+2}=\theta P_{n+1}+x\,\theta P_n$. The dense matrix
$$
\begin{pmatrix}x\theta&\theta\\ x(\theta^2+\theta)&x\theta+\theta^2\end{pmatrix}
$$
sends $(P_n,P_{n+1})$ to $(P_{n+2},P_{n+3})$. It factors as a product of two
matrices with a zero entry, each of which preserves ordered PF vectors, so the
dense matrix does too. Among the nine mixed transitions between the lag factors
$1$, $\theta$ and $x$, exactly the two alternating identity/Euler edges preserve
ordered PF vectors. With $P_0=1$ and $P_1=x$, the orbit stays ordered PF, so
every $P_n$ is PF and in particular splits over $\mathbb R$.

## What is new

The classification and the supporting differential lemmas were developed in this
library, in Issue #1741 (the $\{1,\theta,x\}$ blocks and the mixed differential
lemma) and Issue #1990 (the endpoint criterion behind $p\ll q\Rightarrow
p+q\ll xp+q$). The formalization cites no external source for them, so we
attribute none. The local-to-global principle has the same $2\times2$ shape as
the criterion on the matrix interlacing page, which is the classical background
for polynomial-matrix entries.

## References

No published source is cited for these results in the formalization. See the
[matrix interlacing](/RealRooted/theorems/matrix-interlacing/) and
[operator preservers](/RealRooted/theorems/operator-preservers/) pages for the
classical background on matrices and operators preserving interlacing.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.OperatorMatrix`
modules named in the metadata.
-/
