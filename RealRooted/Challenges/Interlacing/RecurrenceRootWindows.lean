module

import RealRooted.DerivativeRecurrence.EndpointWindow
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.EndpointDerivative.Basic
import RealRooted.Interlacing.VariableDelay
import RealRooted.MaWang.EndpointClassification
import RealRooted.MaWang.EndpointMultiplicity
import RealRooted.MaWang.GrowingZeroMultiplicity
import RealRooted.ProductSequence.FixedDerivative

/-!
# Interlacing for recurrences with confined roots

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "recurrence-root-windows"
formalized = "2026-10-01"
references = [
  "LiuWang2007",
  "MaWang2008",
  "Fisk2006x",
  "Wagner1992",
]
authors = ["Liu", "Wang", "Ma", "Fisk", "Wagner"]
years = [1992, 2006, 2007, 2008]

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Rows of P_{n+1} = A_n P_n′ + B_n P_n interlace if their roots stay in a window"
headline = true

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_le"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "The same with only an upper root bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_of_or"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Moving windows that widen with n"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_endpoint_windows"
module = "RealRooted.DerivativeRecurrence.EndpointWindow"
label = "Interlacing when each new row has its roots in the next window"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Rows of P_{n+2} = a_n P_{n+1} + b_n P_n interlace in a fixed root window"

[[theorems]]
name = "RealRooted.strictInterl_endpointDerivative"
module = "RealRooted.EndpointDerivative.Basic"
label = "f ≪ (x − a)(x − b) f′ when the roots of f lie in [a, b]"

[[theorems]]
name = "RealRooted.strictInterl_derivative_endpointProduct"
module = "RealRooted.EndpointDerivative.Basic"
label = "f ≪ ((x − a)(x − b) f)′ when the roots of f lie in [a, b]"

[[theorems]]
name = "RealRooted.MaWang.endpointStep_roots_mem_Ico_iff"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "Ma–Wang step: the roots stay in [−c, 0) iff b ≤ c(a + multiplicity of −c)"

[[theorems]]
name = "RealRooted.MaWang.affineEndpointSequence_roots_mem_Ico_iff"
module = "RealRooted.MaWang.EndpointClassification"
label = "Classification of the affine Ma–Wang recurrences with confined roots"

[[theorems]]
name = "RealRooted.growingZeroStep_isPFPolynomial_iff"
module = "RealRooted.MaWang.GrowingZeroMultiplicity"
label = "(a + bx) f + x(u − vx) f′ is PF iff a + u · (multiplicity of 0 in f) ≥ 0"

[[theorems]]
name = "RealRooted.strictInterl_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Delay recurrences Q_{n+1} = Q_n + w x Q_{p(n+1)}: Q_i ≪ Q_n for p(n) ≤ i ≤ n"

[[theorems]]
name = "RealRooted.strictInterl_iterate_derivative_mul_X_sub_C_pow_succ"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "Fixed derivatives of q (x − a)ⁿ and q (x − a)ⁿ⁺¹ interlace"
-->

<!-- realrooted-catalog-content -->
# Interlacing for recurrences with confined roots

Consecutive rows of a recurrence $P_{n+1}=A_nP_n'+B_nP_n$ interlace when their roots stay in a
window on which $A_n\le0$, and sign conditions outside the window keep them there. This turns
the Liu–Wang and Ma–Wang criteria into theorems about whole sequences, including the endpoint
recurrences of Fisk and of Ma and Wang.

## Results

Let $P_n$ be real polynomials with $\deg P_n=D_0+n$ and positive leading coefficient, and let
$A_n,B_n,a_n,b_n$ be real polynomials. When $D_0=0$ we also assume $P_0\ll P_1$.

**Theorem (root window).** Let $P_{n+1}=A_nP_n'+B_nP_n$ and $L\le U$. Suppose that $P_0$ is
real-rooted with all roots in $[L,U]$, and that for every $n$

- $A_n\le0$ on $[L,U]$, and
- $A_n\ge0$ outside $[L,U]$, with $B_n>0$ on $(U,\infty)$ and $B_n<0$ on $(-\infty,L)$.

Then $P_n\ll P_{n+1}$ for all $n$. The same holds with only an upper bound $U$, and for windows
$[L_n,U_n]$ that widen with $n$. More generally, if $A_n\le0$ on sets $W_n$, it suffices that
each new row has its roots in $W_{n+1}$.

**Theorem (three-term recurrences).** Let $P_{n+2}=a_nP_{n+1}+b_nP_n$ with $P_0\ll P_1$, all
roots of $P_0$ and $P_1$ in $[L,U]$, and for all $n$: $b_n\le0$ on $[L,U]$; $a_n>0$ and
$b_n\ge0$ on $(U,\infty)$; $a_n<0$ and $b_n\ge0$ on $(-\infty,L)$. Then $P_n\ll P_{n+1}$ for
all $n$.

**Corollary (endpoint derivatives; Fisk).** [@Fisk2006x, Ch. 1] Let $a\le b$ and
$q=(x-a)(x-b)$. If $f$ has positive leading coefficient, degree at least $1$ and all roots in
$[a,b]$, then $f\ll qf'$ and $f\ll(qf)'$, and both have all roots in $[a,b]$. Iterating either
map gives an interlacing sequence.

**Theorem (endpoint steps; Ma–Wang).** [@MaWang2008, Thm. 2, Cor. 3] Let
$E(p)=(ax+b)p+x(x+c)p'$ with $a,b>0$, and let $p$ be real-rooted with positive leading
coefficient and all roots in $[-c,0)$. Then $p\ll E(p)$, and all roots of $E(p)$ lie in
$[-c,0)$ if and only if $b\le c(a+m)$, where $m$ is the multiplicity of $-c$ as a root of $p$.
For $P_{n+1}=\rho_nE_n(P_n)$ with $\rho_n>0$, $c,\lambda>0$, $0\le\mu<a$ and
$b_n=c(a+\lambda n-\mu)$, all rows keep their roots in $[-c,0)$ if and only if $\lambda=1/L$
and $\mu=r/L$ for integers $L\ge1$, $r\ge0$.

**Theorem (growing zero).** Let $u,v\ge0$ and let $f\ne0$ be a Pólya frequency polynomial with
$v\deg f<b$. Then $(a+bx)f+x(u-vx)f'$ interlaces $f$, and it is a Pólya frequency polynomial if
and only if $a+um\ge0$, where $m$ is the multiplicity of $0$ as a root of $f$.

**Theorem (delay recurrences).** Let $p\colon\mathbb N\to\mathbb N$ be weakly increasing on
$n\ge1$ with $p(n)<n$, let $w(n)\ge0$, $Q_0=1$ and $Q_{n+1}=Q_n+w(n+1)\,x\,Q_{p(n+1)}$. Then
every $Q_n$ is real-rooted with nonnegative coefficients, and $Q_i\ll Q_n$ whenever
$p(n)\le i\le n$.

**Corollary (fixed derivatives).** If $q$ is real-rooted with positive leading coefficient and
$r\le\deg q$, then $D^r\bigl(q(x-a)^n\bigr)\ll D^r\bigl(q(x-a)^{n+1}\bigr)$ for all $n$.

## Use

For first-order recurrences with nonnegative coefficients the window is $(-\infty,0]$, and the
[Liu–Wang and Ma–Wang page](rr:ma-wang-liu-wang) suffices. A bounded window is needed when
$A_n$ changes sign, as in $x(x+c)$. With $p(n)=\max(n-L,0)$ the delay theorem covers
recurrences with a fixed delay $L$.

## Proof

Each step is the Ma–Wang criterion: if the roots of $P_n$ lie in the window, then $A_n\le0$ at
these roots gives $P_n\ll P_{n+1}$. Beyond the window $P_n$ and $P_n'$ have constant signs, and
the sign conditions make $P_{n+1}$ nonzero there, so its roots stay in the window. The delay
recurrences follow [@Fisk2006x, Example 16.10] with the cone rules of
[@Wagner1992, Section 3].

## References

[@LiuWang2007]; [@MaWang2008, Thm. 2, Cor. 3]; [@Fisk2006x, Ch. 1, Example 16.10];
[@Wagner1992, Section 3].
<!-- /realrooted-catalog-content -->
-/
