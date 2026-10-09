import RealRooted.CombinatorialExamples.CentralFactorial
import RealRooted.EulerBidiagonal
import RealRooted.Interlacing.PencilPreserver

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
(A071951).

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
