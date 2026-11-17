module

import RealRooted.LaguerreInequalities
import RealRooted.LaguerreInequalities.Forms
import RealRooted.LaguerreInequalities.Rows
import RealRooted.LaguerreInequalities.SignAlternation
import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin
import RealRooted.Wronskian.OdePropagation
import RealRooted.Wronskian.PolarLaguerre
import RealRooted.Wronskian.OdeRootBound

/-!
# Laguerre inequalities and differential equations

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "laguerre-inequalities"
formalized = "2026-11-09"
authors = ["Sonin", "Krasikov"]
years = [1880, 2014]

[[definitions]]
name = "RealRooted.laguerreForm"
module = "RealRooted.Wronskian.PolarLaguerre"
label = "First Laguerre form L₁ f = f′² − f f′′"

[[definitions]]
name = "RealRooted.secondLaguerreForm"
module = "RealRooted.LaguerreInequalities.Forms"
label = "Second Laguerre form L₂ f = (3 f′′² − 4 f′ f′′′ + f f⁽⁴⁾) / 12"

[[definitions]]
name = "Polynomial.Sonin.envelope"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Sonin envelope Δ y² + (2a y′ + b y)²"

[[theorems]]
name = "RealRooted.splits_iff_splits_derivative_and_forms_nonneg"
module = "RealRooted.LaguerreInequalities"
label = "f is real-rooted iff f′ is real-rooted and both Laguerre forms are nonnegative"
headline = true
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.exists_splits_derivative_laguerreForm_nonneg_not_splits"
module = "RealRooted.LaguerreInequalities"
label = "The second inequality cannot be dropped: X⁴ − 1"

[[theorems]]
name = "RealRooted.splits_of_eval_mul_derivative_neg"
module = "RealRooted.LaguerreInequalities.SignAlternation"
label = "Sign alternation at the roots of G forces F to be real-rooted"

[[theorems]]
name = "RealRooted.BrandenLeite.splits_affineNegativePowerRow_of_inequalities"
module = "RealRooted.LaguerreInequalities.Rows"
label = "The two Laguerre inequalities force every row of (Q − tz)^(−κ) to be real-rooted"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.three_mul_sq_eval_derivative_derivative_sub_four_mul_nonneg"
module = "RealRooted.Wronskian.OdeRootBound"
label = "Laguerre's inequality at a root: 3 p′′² − 4 p′ p′′′ ≥ 0"

[[theorems]]
name = "RealRooted.not_isRoot_of_ode_discriminant_eval_pos"
module = "RealRooted.Wronskian.OdeRootBound"
label = "A real-rooted solution of A p′′ + B p′ + C p = 0 has no root where δ > 0"

[[theorems]]
name = "RealRooted.splits_simple_roots_neg_strictInterl_of_ode"
module = "RealRooted.Wronskian.OdePropagation"
label = "Recurrences with an ODE: real-rooted rows with simple negative roots that interlace"
tags = ["realrooted-original"]

[[theorems]]
name = "Polynomial.Sonin.eval_ne_zero_of_mem_Ioc"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Sonin: no roots on an interval from a sign condition at its left end"

[[theorems]]
name = "Polynomial.Sonin.eval_ne_zero_of_tendsto_atBot"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Sonin: no roots on a left half-line"
-->

<!-- realrooted-catalog-content -->
# Laguerre inequalities and differential equations

A real polynomial is real-rooted if and only if its derivative is real-rooted and two Laguerre
forms are nonnegative. Laguerre's inequality also locates roots of polynomials that satisfy a
second-order differential equation, and with Sonin's function it excludes roots from intervals.
Both give real roots and interlacing for families defined by differential recurrences.

## Results

For a real polynomial $f$ let
$$
L_1(f)=(f')^2-ff'',\qquad
L_2(f)=\frac{3(f'')^2-4f'f'''+ff^{(4)}}{12},
$$
the coefficients of $y^2$ and $y^4$ in $f(t+iy)f(t-iy)$.

**Theorem (derivative descent).** A real polynomial $f$ is real-rooted if and only if $f'$ is
real-rooted and $L_1(f)\ge0$ and $L_2(f)\ge0$ on $\mathbb R$. The second inequality is needed:
for $f=t^4-1$, $f'$ is real-rooted and $L_1(f)\ge0$, but $L_2(f)(0)=-2$.

**Lemma (sign alternation).** Let $G$ be real-rooted and $\deg F=\deg G+1$, with leading
coefficients of the same sign. If $F(\rho)G'(\rho)<0$ at every root $\rho$ of $G$, then $F$ is
real-rooted.

**Corollary (coefficient rows).** Let $Q$ be a real power series with $Q(0)=1$ and
$F_n^\alpha(t)=[z^n](Q(z)-tz)^{-\alpha}$. Then $\partial_tF_n^\alpha=\alpha F_{n-1}^{\alpha+1}$,
so $L_1(F_n^\alpha)$ and $L_2(F_n^\alpha)$ are quadratic expressions in the rows. If these are
nonnegative on $\mathbb R$ for all $n$ and all positive integers $\alpha$, then every row is
real-rooted.

**Theorem (root exclusion).** If $p$ is real-rooted and $p(z)=0$, then
$3p''(z)^2-4p'(z)p'''(z)\ge0$. Hence if $Ap''+Bp'+Cp=0$ and $A(z)\ne0$, then
$\delta=B^2+4A'B-4A(B'+C)$ satisfies $\delta(z)\le0$ at every root $z$ of $p$.

**Theorem (families).** Let $K_nF_{n+1}=p_nF_n+q_nF_n'$ with $K_n>0$, where each $F_n$ has
degree $d+n$, positive leading coefficient, nonnegative coefficients and positive constant term.
Let $F_0$ be real-rooted with $a_0F_0''+b_0F_0'+c_0F_0=0$, and suppose that for every $n$ and
every polynomial $g$, the operator $a_{n+1}D^2+b_{n+1}D+c_{n+1}$ maps $p_ng+q_ng'$ to a fixed
linear image $U_n$ of $a_ng''+b_ng'+c_ng$; then every $F_n$ satisfies the $n$th equation. If for
all $n$ and $x<0$, $a_n(x)\ne0$ and $q_n(x)\ge0$ implies $\delta_n(x)>0$, then every $F_n$ is
real-rooted with simple negative roots, and $F_n\ll F_{n+1}$.

**Theorem (Sonin envelopes).** Let $y\ne0$ be a polynomial solution of $ay''+by'+cy=0$, put
$\Delta=4ac-2ab'+2a'b-b^2$ and $W=2ay'+by$, and let $g,h,j$ be polynomials with $gh=aj$ and
$a(g'h-gh')=(b-a')gh$. Suppose that $a$ and $h$ do not vanish, $j>0$ and $\Delta\le0$ on
$(-\infty,L]$. If $gyW/h\to0$ at $-\infty$, then $y$ has no root in $(-\infty,L]$. On $[L,U]$,
$y$ has no root in $(L,U]$ if $gyW/h\ge0$ at $L$.

## Use

The derivative descent reduces real-rootedness to one degree lower, which suits families closed
under differentiation. The family theorem applies to recurrences whose rows satisfy an explicit
second-order equation, as many hypergeometric families do. The Sonin function
$w^2+(w')^2/Q$ for $w''+Qw=0$ is a classical tool for zeros of orthogonal polynomials.

## Proof

For the forward direction, $L_1((t-a)g)=g^2+(t-a)^2L_1(g)$ and
$L_2((t-a)g)=L_1(g)+(t-a)^2L_2(g)$, so induction on the roots gives nonnegativity. For the
converse, write $f=dF$ and $f'=dG$ with $d=\gcd(f,f')$; the forms give $F(\rho)G'(\rho)<0$ at
each root $\rho$ of $G$, and sign alternation applies. In the family theorem, $\delta_n\le0$
at a negative root $x$ of $F_n$ forces $q_n(x)<0$, and the
[Ma–Wang criterion](rr:ma-wang-liu-wang) propagates interlacing. For Sonin envelopes,
$gyW/h$ has derivative $j(W^2-\Delta y^2)/(2h^2)\ge0$, and it vanishes with positive derivative
at a root, so it is negative just left of the root, a contradiction.

## References

N. Sonin, *Math. Ann.* 16 (1880), 1–80; I. Krasikov, *LMS J. Comput. Math.* 17 (2014),
209–225, Section 2; DLMF 1.13.13–15. For rows of $(Q(z)-tB(z))^{-\alpha}$, see the
[chain polynomial page](rr:branden-leite).
<!-- /realrooted-catalog-content -->
-/
