module

import RealRooted.MatrixInterlacing.SeparatedCharacteristicDeterminant
import RealRooted.MatrixInterlacing.SeparatedCharacteristicRows
import RealRooted.MatrixInterlacing.WeightedThreeStateRows
import RealRooted.OperatorMatrix.EulerDerivativeLag
import RealRooted.OperatorMatrix.LocalToGlobal
import RealRooted.OperatorMatrix.OneThetaX
import RealRooted.Recurrence.CubicTransition
import RealRooted.Recurrence.PFTripleMatrix
import RealRooted.Recurrence.QuarticInterlacing

/-!
# Recurrences from interlacing-preserving matrices

<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "interlacing-matrix-recurrences"
formalized = "2026-11-01"
references = [
  "Branden2015",
  "Wagner1992",
]
authors = ["Wagner", "Brändén"]
years = [1992, 2015]
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.separatedCharacteristicRows_interl_succ"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicRows"
label = "Characteristic polynomial ∏(T − aᵢ) − x∏(T − bⱼ) with aᵢ ≥ 0 ≥ bⱼ: PF rows interlace"
headline = true

[[theorems]]
name = "RealRooted.separatedCharacteristicFinMatrix_charpoly"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicDeterminant"
label = "The companion-type matrix has characteristic polynomial ∏(T − aᵢ) − X ∏(T − bⱼ)"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.iff_forall_blocks_of_two_le"
module = "RealRooted.OperatorMatrix.LocalToGlobal"
label = "An operator matrix preserves ordered PF vectors iff every 2 × 2 submatrix does"

[[theorems]]
name = "RealRooted.OperatorMatrix.PreservesOrderedPF.letters_iff"
module = "RealRooted.OperatorMatrix.OneThetaX"
label = "A matrix over {1, θ, x} preserves ordered PF vectors iff all 2×2 blocks are of 13 types"

[[theorems]]
name = "RealRooted.OperatorMatrix.EulerDerivativeLag.splits_of_recurrence_one_X"
module = "RealRooted.OperatorMatrix.EulerDerivativeLag"
label = "Every row of P(n+2) = θP(n+1) + xθP(n) with P(0) = 1, P(1) = x is real-rooted"

[[theorems]]
name = "RealRooted.PreservesScaledPFTriple.iff"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "[[0,0,1],[λx,0,1],[cx,dx,a+bx]] preserves ordered PF triples iff a, b, d ≥ 0, c ≥ aλ"

[[theorems]]
name = "RealRooted.isOrderedPFTriple_of_recurrence_scaled"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "Third-order recurrences with aκ² − eκ + d ≤ 0 have PF rows in ordered states"

[[theorems]]
name = "RealRooted.PreservesCubicTransition.iff_nonneg"
module = "RealRooted.Recurrence.CubicTransition"
label = "The cubic transition preserves ordered PF triples iff its parameters are nonnegative"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_interl_add_one"
module = "RealRooted.Recurrence.CubicTransition"
label = "Consecutive rows of the cubic family interlace"

[[theorems]]
name = "RealRooted.interl_quarticInterlacingRow_succ"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "Rows of an admissible quartic state interlace when 0 ≤ w ≤ v ≤ u and u > 0"

[[theorems]]
name = "RealRooted.PreservesInterlacingSeq0.weightedThreeStateMatrix_iff"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "[[1, b, d], [0, 1, 1], [x, αx, 1]] preserves interlacing iff 0 ≤ d, α ≤ b"

[[theorems]]
name = "RealRooted.weightedThreeStateRow_interl_succ"
module = "RealRooted.MatrixInterlacing.WeightedThreeStateRows"
label = "Consecutive rows of the weighted three-state recurrence interlace"
-->

<!-- realrooted-catalog-content -->
# Recurrences from interlacing-preserving matrices

A recurrence has Pólya frequency rows with consecutive interlacing when it is one coordinate of
a matrix action that preserves interlacing sequences. Brändén's criterion decides this for
matrices of polynomials; we give an analogue for matrices of differential operators and sharp
parameter ranges for several families of third- and fourth-order recurrences.

## Results

A polynomial is *PF* if it is zero or has nonnegative coefficients and only real nonpositive
roots; here $0\ll f$ and $f\ll0$ for every $f$. A vector $(f_1,\dotsc,f_n)$ is an *ordered PF
vector* if every $f_i$ is PF and $f_i\ll f_k$ for $i<k$; for $n=3$ it is an *ordered PF triple*.

**Theorem (separated characteristic polynomial).** Let $a\in\mathbb R^{h+m}$ and
$b\in\mathbb R^m$ with $a_i\ge0\ge b_j$. There is an explicit $(h+m)\times(h+m)$ matrix $M$
over $\mathbb R[x]$ with
$$
\det(T-M)=\prod_i(T-a_i)-x\prod_j(T-b_j)
$$
that maps ordered PF vectors to ordered PF vectors. Hence for every ordered PF seed $v$, every
coordinate of $M^nv$ is PF and $(M^nv)_i\ll(M^{n+1}v)_i$. By the Cayley–Hamilton theorem these
coordinates solve the recurrence with this characteristic polynomial.

**Theorem (operator matrices).** A matrix whose entries are linear operators on $\mathbb R[x]$
preserves ordered PF vectors if and only if every $2\times2$ submatrix does. With entries $1$,
$\theta=x\,d/dx$ and $x$, exactly thirteen $2\times2$ blocks do, written (top row)/(bottom row):

- $(1,1)/(1,1)$, $(1,1)/(\theta,\theta)$, $(1,1)/(x,1)$, $(1,1)/(x,x)$;
- $(\theta,1)/(\theta,1)$, $(\theta,1)/(\theta,\theta)$, $(\theta,1)/(x,\theta)$;
- $(\theta,\theta)/(\theta,\theta)$, $(\theta,\theta)/(x,x)$;
- $(x,1)/(x,1)$, $(x,1)/(x,x)$, $(x,\theta)/(x,\theta)$, $(x,x)/(x,x)$.

For example, every row of $P_{n+2}=\theta P_{n+1}+x\,\theta P_n$ with $P_0=1$, $P_1=x$ is
real-rooted.

**Theorem (ordered PF triples).** Let $\lambda>0$. The matrix
$\begin{pmatrix}0&0&1\\\lambda x&0&1\\cx&dx&a+bx\end{pmatrix}$ preserves ordered PF triples if
and only if $a,b,d\ge0$ and $c\ge a\lambda$. Consequently, if $a_s,b_s,d_s\ge0$,
$a_s\kappa^2-e_s\kappa+d_s\le0$ for a fixed $\kappa>0$, $P_{-1}=P_0=0$, $P_1=1$ and
$$
P_{s+2}=(a_s+b_sx)P_{s+1}+e_s\,x\,P_s+d_s\,x^2P_{s-1},
$$
then every $P_s$ is PF and $P_s\ll P_{s+1}$.

**Theorem (cubic and quartic families).** For $\alpha,\gamma,w\ge0$, the rows of
$P_{n+3}=(\alpha+\gamma)P_{n+2}-\alpha\gamma P_{n+1}+w\,x\,P_n$ with $P_0=1$, $P_1=\gamma$,
$P_2=\gamma^2$ are PF and $P_n\ll P_{n+1}$; the underlying transition preserves ordered PF
triples if and only if $\alpha,\gamma,w\ge0$. For $0\le w\le v\le u$ and $u>0$, the rows of
$$
R_{n+4}=2R_{n+3}+\bigl((u+v-w)x-1\bigr)R_{n+2}+(2w-v)\,x\,R_{n+1}-w\,x\,R_n
$$
started from an admissible state of five polynomials are PF and $R_n\ll R_{n+1}$.

**Theorem (three-state matrix).** The matrix
$\begin{pmatrix}1&b&d\\0&1&1\\x&\alpha x&1\end{pmatrix}$ preserves interlacing sequences of PF
polynomials if and only if $b,\alpha,d\ge0$, $d\le b$ and $\alpha\le b$. If $a,b\ge0$, $c>0$,
$ac/2\le b$ and $\eta\le\min(a,b/c)$, the rows of the associated third-order recurrence
starting $1$, $c$, $c^2+(a-\eta)x$ have only negative roots, and consecutive rows interlace.

## Use

To prove that a recurrence has PF rows with consecutive interlacing, realize it as a transition
on a short state of polynomials that preserves ordered PF vectors. For entries that are
multiplications by polynomials, the test is
[Brändén's criterion](rr:matrix-interlacing); for three-term recurrences see
[Favard recurrences](rr:favard).

## Proof

For polynomial entries, the criterion of [@Branden2015, Thm. 7.8.5] applies to the
$2\times2$ submatrices. For operator entries, sufficiency follows from the cone lemmas of
[Wagner](rr:interlacing): if $h\ll f_i$ for all $i$, then $h\ll\sum_ic_if_i$ for $c_i\ge0$, and
dually, while $f\ll g$ implies $g\ll xf$. Necessity follows by applying the matrix to vectors
such as $(1,0,0)$, $(0,1,0)$, $(0,0,1)$ and $(K,0,1)$ for large $K$.

## References

[@Branden2015, Thm. 7.8.5]; [@Wagner1992].
<!-- /realrooted-catalog-content -->
-/
