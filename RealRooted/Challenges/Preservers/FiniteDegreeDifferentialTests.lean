module

import RealRooted.EvenDerivative.Basic
import RealRooted.EvenDerivative.Preserver
import RealRooted.EvenDerivative.Symbol
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone
import RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests
import RealRooted.FiniteFreeAdditive.FiniteDegreeTests
import RealRooted.Interlacing.QuadraticDifferentialOrbit
import RealRooted.Interlacing.QuadraticPFPreservers
import RealRooted.Interlacing.SecondOrderClassification
import RealRooted.Interlacing.SecondOrderNecessity

/-!
# Differential operators preserving Pólya frequency polynomials

<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "finite-degree-differential-tests"
formalized = "2026-11-01"
references = [
  "BorceaBranden2009I",
]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "The degree-N test h(D) X^N"

[[definitions]]
name = "RealRooted.evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Basic"
label = "The operator Δ_c f = ∑ cₖ xᵏ f^{(2k)}"

[[definitions]]
name = "RealRooted.secondOrderRayOperator"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "The operator (a + bX) + (c + dX) D + f X D²"

[[theorems]]
name = "RealRooted.PreservesPFUpTo.iff_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "h(D) preserves PF polynomials of degree at most N exactly when h(D) X^N is PF"
headline = true

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.iff_differentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "Ordered PF images through degree N are detected by the two degree-N tests"

[[theorems]]
name = "RealRooted.forall_differential_images_iff_isPFPolynomial_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone"
label = "All-degree ordered PF preservation by (h, k) is equivalent to k being PF and k ≪ h"

[[theorems]]
name = "RealRooted.EvenDerivative.isPFPolynomial_tfae"
module = "RealRooted.EvenDerivative.Preserver"
label = "Δ_c preserves PF through degree N iff Δ_c(xᴺ) is real-rooted iff p_N is real-rooted"

[[theorems]]
name = "RealRooted.splits_evenDerivativeTest_of_splits_symbol"
module = "RealRooted.EvenDerivative.Symbol"
label = "Finitely supported c with a real-rooted signed symbol: p_N is real-rooted for every N"

[[theorems]]
name = "RealRooted.secondOrderRayPreserving_iff_three_branch_at_index"
module = "RealRooted.Interlacing.SecondOrderNecessity"
label = "(a + bX) + (c + dX) D + f X D² preserves PF polynomials exactly when c ≤ τ_m"

[[theorems]]
name = "RealRooted.not_secondOrderRayPreserving_of_discrim_neg"
module = "RealRooted.Interlacing.SecondOrderClassification"
label = "A negative discriminant d² − 4bf rules out PF preservation"

[[theorems]]
name = "RealRooted.IsPFPolynomial.rhoGammaOperator_of_two_le"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "X D² + ρ X D + X + γ preserves PF polynomials for ρ ≥ 2 and γ ≥ 0"

[[theorems]]
name = "RealRooted.IsQuadraticDifferentialOrbit.exists_forall_exists_nonreal_root"
module = "RealRooted.Interlacing.QuadraticDifferentialOrbit"
label = "For 5ρ² < 8 the orbit of 1 under X D² + ρ X D + X + γ has nonreal roots eventually"
-->

<!-- realrooted-catalog-content -->
# Differential operators preserving Pólya frequency polynomials

A constant-coefficient operator $h(D)$ preserves Pólya frequency polynomials of degree at most
$N$ exactly when the single polynomial $h(D)\,x^N$ is Pólya frequency. Similar finite tests
hold for pairs of operators and for even-derivative operators, and an explicit bound decides
which second-order operators with linear coefficients preserve Pólya frequency polynomials.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. Interlacing uses the [zero-aware convention](rr:about). For
$h=\sum_jh_jx^j$ and $D=d/dx$ let $h(D)=\sum_jh_jD^j$ and $T_N(h)=h(D)\,x^N$.

**Theorem (scalar test).** $h(D)$ maps every PF polynomial of degree at most $N$ to a PF
polynomial if and only if $T_N(h)$ is PF.

**Theorem (ordered tests).** For real polynomials $h,k$, the images $h(D)p$ and $k(D)p$ are PF
with $h(D)p\ll k(D)p$ for every PF $p$ of degree at most $N$ if and only if $T_N(h)$ and
$T_N(k)$ are PF with $T_N(h)\ll T_N(k)$. If $h\ne0$ is PF, this holds for every $N$ if and only
if $k$ is PF and $k\ll h$.

**Theorem (even derivatives).** Let $c_0=1$, $c_k\ge0$, $\Delta_cf=\sum_kc_kx^kf^{(2k)}$ and
$p_N(z)=\sum_{k\le N/2}(-1)^kc_k\,N(N-1)\dotsm(N-2k+1)\,z^{N-2k}$. Then $\Delta_c$ preserves PF
polynomials of degree at most $N$ if and only if $\Delta_c(x^N)$ is real-rooted, if and only if
$p_N$ is real-rooted. If only finitely many $c_k$ are nonzero and $\sum_k(-1)^kc_kw^{2k}$ is
real-rooted, this holds for every $N$. For $c=(1,1,1,0,\dotsc)$ it holds for $N\le4$ but not
for $N=5$.

**Theorem (second-order operators).** Let
$L=(a+bx)+(c+dx)D+f\,xD^2$ with $a,c,d\ge0$, $b,f>0$ and $\delta=d^2-4bf$. If $\delta<0$, then
$L$ does not preserve PF polynomials. If $\delta>0$, choose $m\ge1$ with
$\delta m(m-1)\le a^2\le\delta m(m+1)$; then $L$ preserves PF polynomials if and only if
$c\le\tau_m$, where
$$
\tau_m=\begin{cases}
a\bigl(d+\sqrt{\delta+4bf/m}\bigr)/(2b) & \text{if }a^2>m^2\delta+4bfm,\\
f+\dfrac{ad}{2b}+\dfrac{m\delta}{4b}+\dfrac{a^2}{4bm} &
\text{if }\lvert m^2\delta-a^2\rvert\le4bfm,\\
\bigl(ad+\sqrt{\delta(a^2+4bfm)}\bigr)/(2b) & \text{otherwise.}
\end{cases}
$$

**Corollary (orbits).** The operator $p\mapsto xp''+\rho\,xp'+xp+\gamma p$ preserves PF
polynomials for $\rho\ge2$ and $\gamma\ge0$. If $\rho,\gamma\ge0$ and $5\rho^2<8$, the
polynomials $P_0=1$, $P_{n+1}=xP_n''+\rho\,xP_n'+xP_n+\gamma P_n$ have a nonreal root for all
large $n$.

## Use

These tests turn the real-rootedness of a whole family $P_{n+1}=LP_n$ into a check on one
polynomial or a few parameters. They are finite-degree versions of the
[Borcea–Brändén classification](rr:borcea-branden-classification) for operators of this form,
and the convolution identity $T_N(h)\boxplus_Np=h(D)p$ links them to
[finite free convolutions](rr:finite-free-convolutions).

## Proof

For $\deg p\le N$, $h(D)p$ is the finite free additive convolution of $T_N(h)$ with $p$, which
preserves PF polynomials. Substituting $x=-z^2$ gives $\Delta_c(x^N)(-z^2)=(-1)^Nz^Np_N(z)$; the
step to all PF inputs uses real stability of the polarization of $p_N$ and the
Grace–Walsh–Szegő theorem [@BorceaBranden2009I, Thm. 2.3 and Prop. 2.4]. For second-order
operators, $L(x^m)$ has a quadratic factor with discriminant
$(a+dm)^2-4bm\bigl(c+f(m-1)\bigr)$, and $\tau_m$ is the optimal bound on $c$.

## References

[@BorceaBranden2009I, Thm. 2.3 and Prop. 2.4].
<!-- /realrooted-catalog-content -->
-/
