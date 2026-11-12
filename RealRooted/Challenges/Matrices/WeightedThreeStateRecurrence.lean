module

import RealRooted.MatrixInterlacing.WeightedThreeState
import RealRooted.MatrixInterlacing.WeightedThreeStateRows
import RealRooted.MatrixInterlacing.WeightedThreeStateStrip
import RealRooted.MatrixInterlacing.WeightedThreeStateStripRoots

/-!
# A weighted three-state interlacing recurrence

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "weighted-three-state-recurrence"
formalized = "2026-10-29"
references = [
  "Branden2015",
]
authors = ["Brändén"]
years = [2015]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.weightedThreeStateMatrix"
module = "RealRooted.MatrixInterlacing.WeightedThreeState"
label = "The three-state matrix [[1, b, d], [0, 1, 1], [X, αX, 1]]"

[[definitions]]
name = "RealRooted.weightedThreeStateRow"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "The row polynomials of the weighted three-state recurrence"

[[definitions]]
name = "RealRooted.weightedStripRow"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStrip"
label = "The normalized rows Q_n with parameters (ρ, e)"

[[theorems]]
name = "RealRooted.PreservesInterlacingSeq0.weightedThreeStateMatrix_iff"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "The three-state matrix preserves interlacing sequences exactly in an explicit region"
headline = true

[[theorems]]
name = "RealRooted.weightedThreeStateRow_interl_succ"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "Consecutive rows interlace"

[[theorems]]
name = "RealRooted.weightedThreeStateRow_isRealRooted"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "Every row is real-rooted"

[[theorems]]
name = "RealRooted.weightedThreeStateRow_roots_neg"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "All roots of every row are negative"

[[theorems]]
name = "RealRooted.weightedThreeState_P_add_three"
module = "RealRooted.MatrixInterlacing.WeightedThreeState"
label = "The third-order recurrence satisfied by the middle coordinate"

[[theorems]]
name = "RealRooted.weightedThreeStateRow_natDegree_halfHeight"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStripRoots"
label = "In the half-height range η ≤ a/2 the n-th row has degree ⌊n/2⌋"

[[theorems]]
name = "RealRooted.weightedStripRow_hasNonnegCoeffs"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStripRoots"
label = "Normalized rows have nonnegative coefficients for ρ ≥ 0 and e ≤ 1/2"

[[theorems]]
name = "RealRooted.weightedThreeStateRow_eq_strip_comp"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStripRoots"
label = "Rescaling of the physical family (a, b, c, η) to the normalized strip rows"

[[theorems]]
name = "RealRooted.weightedStripRow_roots_of_sign_changes"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStripRoots"
label = "Sign changes at ⌊n/2⌋ + 1 points force a normalized row to split with simple roots"

[[theorems]]
name = "RealRooted.existsUnique_characteristicScale_eq"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStrip"
label = "Positive characteristic parametrization of the evaluation point"

[[theorems]]
name = "RealRooted.weightedStripRow_eval_eq_expansion"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStrip"
label = "Q_n(-s) is an explicit expansion in the three characteristic roots"

[[theorems]]
name = "RealRooted.weightedThreeStateAmplitude_gap_pos"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateStrip"
label = "Amplitude inequality for the complex-root contribution"
-->

<!-- realrooted-catalog-content -->
# A weighted three-state interlacing recurrence

In an explicit parameter region, the rows of a three-state recurrence have nonnegative
coefficients, only negative real roots, and consecutive rows interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Let
$$
M=\begin{pmatrix}1&b&d\\0&1&1\\x&\alpha x&1\end{pmatrix}
$$
act on triples by $(R,P,D)\mapsto(R+bP+dD,\;P+D,\;xR+\alpha xP+D)$.

**Theorem (preservation).** By the matrix criterion [@Branden2015, Thm. 7.8.5], $M$ maps an
interlacing sequence of nonnegative real-rooted polynomials (zero terms allowed) to another one
if and only if
$$
0\le b,\qquad 0\le\alpha,\qquad 0\le d,\qquad d\le b,\qquad\alpha\le b.
$$

**Theorem (rows).** Iterate from the seed $(d-\eta,1,0)$ with $\eta\le d$ and keep the middle
coordinate. This gives rows $P_n$ with $P_0=P_1=1$, $P_2=1+(\alpha+d-\eta)x$ and
$$
P_{n+3}=3P_{n+2}+\bigl((\alpha+d)x-3\bigr)P_{n+1}+\bigl(1+(b-\alpha-d)x\bigr)P_n .
$$
Rescale to parameters $(a,b,c,\eta)$ with $c>0$, whose rows begin $1$, $c$, $c^2+(a-\eta)x$. If
$a,b\ge0$, $c>0$, $ac/2\le b$ and $\eta\le\min(a,b/c)$, then every row has nonnegative
coefficients, constant term $c^n$, and only real negative roots, and consecutive rows interlace.

**Proposition (normalized rows).** For $a,c\ne0$ the rows equal $c^n\,Q_n(ax/c^2)$, where the
normalized rows $Q_n$ with parameters $(\rho,e)=(b/(ac),\eta/a)$ satisfy $Q_0=Q_1=1$,
$Q_2=1+(1-e)x$ and
$$
Q_{n+3}=3Q_{n+2}+(x-3)Q_{n+1}+\bigl(1+(\rho-1)x\bigr)Q_n .
$$
For $e\le\tfrac12$ and $\rho\ge0$, the rows $Q_n$ have nonnegative coefficients, positive
coefficients up to degree $\lfloor n/2\rfloor$, degree exactly $\lfloor n/2\rfloor$, and only
negative roots. If $Q_n$ alternates in sign at the points of a strictly increasing list of
$\lfloor n/2\rfloor+1$ points, then $Q_n$ splits with simple roots.

**Proposition (evaluation at $-s$).** Let $\rho>0$ and $s>0$. There is a unique $r\in(0,\rho)$
with $r^3=s(\rho-r)$, and then $Q_n(-s)$ is an explicit combination of $n$-th powers of
$1-r$ and $1+r/2\pm iv$, where $v^2=s+3r^2/4$. For $e\le\tfrac12$ the complex pair dominates
the real mode in amplitude.

## References

The matrix criterion is [@Branden2015, Thm. 7.8.5].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the
`RealRooted.MatrixInterlacing.WeightedThreeState*` modules.
-/
