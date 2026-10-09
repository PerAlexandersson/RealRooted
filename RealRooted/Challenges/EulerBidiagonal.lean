import RealRooted.CombinatorialExamples.CentralFactorial
import RealRooted.CombinatorialExamples.EulerTypeOeis
import RealRooted.CombinatorialExamples.EulerTypeRows
import RealRooted.EulerBidiagonal
import RealRooted.EulerBidiagonal.General
import RealRooted.EulerBidiagonal.PairTheorem
import RealRooted.Interlacing.PencilPreserver
import RealRooted.Interlacing.RootDeletionExpansion

/-!
# Euler bidiagonal step challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "euler-bidiagonal-interlacing"
years = [2026]

[[definitions]]
name = "RealRooted.EulerBidiagonal.step"
module = "RealRooted.EulerBidiagonal"
label = "The bidiagonal Euler step X + (θ + a)(θ + b)"

[[definitions]]
name = "RealRooted.IsNegativeSimple"
module = "RealRooted.Interlacing.PencilPreserver"
label = "Positive leading coefficient and simple negative roots"

[[theorems]]
name = "RealRooted.EulerBidiagonal.isNegativeSimple_step"
module = "RealRooted.EulerBidiagonal"
label = "The step preserves simple negative roots"

[[theorems]]
name = "RealRooted.EulerBidiagonal.splits_step_X_sub_C_mul"
module = "RealRooted.EulerBidiagonal"
label = "The step keeps (X − ρ)q real-rooted for every real ρ"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_step_of_strictInterl"
module = "RealRooted.EulerBidiagonal"
label = "The step preserves strict interlacing of negative-rooted pairs"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_rows"
module = "RealRooted.EulerBidiagonal"
label = "Consecutive rows of the step strictly interlace"

[[theorems]]
name = "RealRooted.strictInterl_map_of_negative_simple_pencil"
module = "RealRooted.Interlacing.PencilPreserver"
label = "Pencil criterion for linear maps preserving interlacing"

[[theorems]]
name = "RealRooted.strictInterl_centralFactorialRows"
module = "RealRooted.CombinatorialExamples.CentralFactorial"
label = "Consecutive central factorial rows interlace (A036969)"

[[theorems]]
name = "RealRooted.strictInterl_legendreStirlingRows"
module = "RealRooted.CombinatorialExamples.CentralFactorial"
label = "Consecutive Legendre–Stirling rows interlace (A071951)"

[[theorems]]
name = "RealRooted.EulerTypeRows.strictInterl_scaledRows"
module = "RealRooted.CombinatorialExamples.EulerTypeRows"
label = "Rows of X + κ(θ + a)(θ + b), κ > 0, strictly interlace"

[[theorems]]
name = "RealRooted.EulerTypeRows.strictInterl_A080248Rows"
module = "RealRooted.CombinatorialExamples.EulerTypeRows"
label = "Consecutive rows of A080248 interlace"

[[theorems]]
name = "RealRooted.EulerTypeRows.strictInterl_A160562Rows"
module = "RealRooted.CombinatorialExamples.EulerTypeRows"
label = "Consecutive rows of A160562 interlace"

[[theorems]]
name = "RealRooted.EulerBidiagonal.isNegativeSimple_generalStep_of_pos"
module = "RealRooted.EulerBidiagonal.General"
label = "κ(θ + a)(θ + b) + X(u + vθ) preserves simple negative roots"

[[theorems]]
name = "RealRooted.StrictInterl.root_deletion_expansion"
module = "RealRooted.Interlacing.RootDeletionExpansion"
label = "A strict interlacer is a positive combination of root deletions"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_generalStep_of_strictInterl"
module = "RealRooted.EulerBidiagonal.PairTheorem"
label = "κ(θ + a)(θ + b) + X(u + vθ) preserves strict interlacing of negative-rooted pairs"
headline = true

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_A156289"
module = "RealRooted.CombinatorialExamples.EulerTypeOeis"
label = "Consecutive rows of A156289 interlace"

[[theorems]]
name = "RealRooted.EulerBidiagonal.A166960_spec"
module = "RealRooted.CombinatorialExamples.EulerTypeOeis"
label = "Consecutive rows of A166960 interlace (likewise A166961, A166962, A166972)"
-->

<!-- realrooted-catalog-content -->
# Interlacing for the bidiagonal Euler step

Let $\theta = x\,\frac{d}{dx}$ and, for $a, b \geq 0$ with $ab > 0$,
$$
T = x + (\theta + a)(\theta + b), \qquad
[x^k]\, T p = (k + a)(k + b)\, p_k + p_{k-1}.
$$
The rows $P_0 = 1$, $P_{n+1} = T P_n$ are the triangles
$a(n,k) = a(n-1,k-1) + (k+a)(k+b)\, a(n-1,k)$. For $a = b = 1$ they are the central
factorial numbers (A036969). For $(a,b) = (1,2)$ they are the Legendre–Stirling numbers
(A071951). Replacing $(\theta + a)(\theta + b)$ by $\kappa(\theta + a)(\theta + b)$ with
$\kappa > 0$ only rescales $x$. This gives A080248 ($\kappa = 1/2$, $(a,b) = (1,2)$) and A160562
($\kappa = 4$, $a = b = 1/2$). It also gives A269945 after the factor $x$ common to all
positive-index rows is removed.

**Theorem.** Let $f \ll g$ be polynomials with positive leading coefficients and simple
negative roots, with $\deg g = \deg f + 1$ and no common root. Then $Tf \ll Tg$, again
without common roots. In particular consecutive rows strictly interlace:
$P_n \ll P_{n+1}$ for all $n$.

Real-rootedness of these rows is classical (Andrews–Gawronski–Littlejohn;
Andrews–Egge–Gawronski–Littlejohn; Mongelli). Interlacing of consecutive rows, and the
preservation of interlacing pairs, appear to be new. They were found and formalized in this
project; see issue #1324. The usual first-order step theorems (Liu–Wang, Wang–Yeh) do not
apply, because the step is second order in $\theta$. Nor does $T$ preserve real-rootedness on
all of $\mathbb{R}[x]$: its Borcea–Brändén symbol is not stable. The argument has to use the
negative real axis.

**Generalization.** For $\kappa, a, b > 0$ the step
$T = \kappa(\theta + a)(\theta + b) + x(u + v\theta)$ maps polynomials with simple negative zeros to
such polynomials, provided $u + vk > 0$ on the degrees in use and $2u \geq (a + b + 1)v$ (or the
sharper condition that the comparison defect is negative on $(-\infty, 0]$). The comparison
polynomial is now $2\kappa x q' + (\kappa(a + b + 1) + vx)q$. It also preserves strict interlacing
of
such pairs (in the regime where the step raises the degree; a shifted-cone form covers the
row recurrences where the multiplier depends on $n$), so the rows A156289, A166960, A166961,
A166962 and A166972 strictly interlace.

## Proof idea

Put $c = a + b + 1$ and compare $Tq$ with $(2\theta + c)\, q$. At every zero $\sigma$ of
$2xq' + cq$,
$$
q(\sigma)\, (Tq)(\sigma) = \sigma^2 \bigl(q q'' - q'^2\bigr)(\sigma)
  + \Bigl(ab - \tfrac{c^2}{4} + \sigma\Bigr) q(\sigma)^2 .
$$
Laguerre's inequality makes the first term negative. Also
$ab - c^2/4 = -\bigl((a-b)^2 + 2(a+b) + 1\bigr)/4 < 0$ and $\sigma < 0$. So $Tq$ has
the opposite sign to $q$ at each $\sigma$. Counting sign changes shows that $Tq$ has simple
negative roots, interlaced by $x(2\theta + c)q$.

The identity $T(xq) = x\,Tq + x(2\theta + c)\,q$ puts both $x\,Tq$ and $T(xq)$ in the
interlacing cone of $Tq$. Hence $T((x - \rho)q)$ is real-rooted for every real $\rho$.

Finally, every member $g + tf$ of the pencil of an interlacing pair either has simple
negative roots or is $(x - \rho)q$ with $q$ negative-rooted. So $T$ keeps the whole pencil
real-rooted, and the Obreschkoff converse gives $Tf \ll Tg$.

## References

G. E. Andrews, W. Gawronski and L. L. Littlejohn, “The Legendre–Stirling numbers,”
*Discrete Mathematics* 311 (2011), 1255–1272; G. E. Andrews, E. S. Egge, W. Gawronski and
L. L. Littlejohn, “The Jacobi–Stirling numbers,” *Journal of Combinatorial Theory, Series A*
120 (2013), 288–303; P. Mongelli, “Total positivity properties of Jacobi–Stirling numbers,”
*Advances in Applied Mathematics* 48 (2012), 354–364.

The Jacobi–Stirling triangles are on the
[Jacobi–Stirling page](/RealRooted/families/jacobi-stirling-numbers/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.EulerBidiagonal`,
`RealRooted.Interlacing.PencilPreserver` and `RealRooted.CombinatorialExamples.CentralFactorial`.
-/
