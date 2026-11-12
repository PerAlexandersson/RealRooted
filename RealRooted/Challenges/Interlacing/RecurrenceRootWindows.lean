module

import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.ThreeTermRecurrence.LagFeedback
import RealRooted.ThreeTermRecurrence.ParityProduct
import RealRooted.Interlacing.Reversal
import RealRooted.Interlacing.RemainderCertificate
import RealRooted.DerivativeRecurrence.EndpointWindow

/-!
# Recurrence root windows and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "recurrence-root-windows"
formalized = "2026-10-01"
tags = []
references = [
  "LiuWang2007",
  "Branden2006",
]
authors = ["Liu", "Wang", "Brändén"]
years = [2006, 2007]

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing from a fixed root window"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_le"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with an upper root bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_of_degree"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Degree-bounded interlacing in a root window"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_div"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with a moving lower bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with a moving upper bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_of_or"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Two-sided moving windows, either condition on each side"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Three-term interlacing in a fixed root window"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_le_of_ratio"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Three-term interlacing from a ratio barrier"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_mem_Icc_of_barrier"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Three-term interlacing with a barrier"

[[theorems]]
name = "RealRooted.strictInterl_of_lagFeedback"
module = "RealRooted.ThreeTermRecurrence.LagFeedback"
label = "Pairwise interlacing for lag-feedback windows"

[[theorems]]
name = "RealRooted.splits_of_lagFeedback"
module = "RealRooted.ThreeTermRecurrence.LagFeedback"
label = "Splitting for lag-feedback recurrences"

[[theorems]]
name = "RealRooted.eq_parityProduct_of_thirdOrderRecurrence"
module = "RealRooted.ThreeTermRecurrence.ParityProduct"
label = "Parity products represented by an order-three recurrence"

[[theorems]]
name = "RealRooted.interlaces_of_parityProduct"
module = "RealRooted.ThreeTermRecurrence.ParityProduct"
label = "Interlacing of parity products"

[[theorems]]
name = "RealRooted.eq_reflect_of_secondOrderDerivativeRecurrence"
module = "RealRooted.Interlacing.Reversal"
label = "Reflection of a second-order derivative recurrence"

[[theorems]]
name = "RealRooted.eq_reflect_of_threeTerm"
module = "RealRooted.Interlacing.Reversal"
label = "Reflection of a three-term recurrence"

[[theorems]]
name = "RealRooted.interlaces_of_eq_reflect"
module = "RealRooted.Interlacing.Reversal"
label = "Interlacing transferred through reversal"

[[theorems]]
name = "RealRooted.splits_of_eq_reflect"
module = "RealRooted.Interlacing.Reversal"
label = "Splitting transferred through reversal"

[[theorems]]
name = "RealRooted.strictInterl_quadratic_of_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Interlacing from a quadratic division remainder"

[[theorems]]
name = "RealRooted.strictInterl_linear_of_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Interlacing from a linear division remainder"

[[theorems]]
name = "RealRooted.Interlaces.pow_mul_of_quadratic_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Power-factor rows from a quadratic remainder certificate"

[[theorems]]
name = "RealRooted.Interlaces.pow_mul_of_linear_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Power-factor rows from a linear remainder certificate"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_endpoint_windows"
module = "RealRooted.DerivativeRecurrence.EndpointWindow"
label = "Interlacing when each next row has its roots in the next window"
headline = true
-->

<!-- realrooted-catalog-content -->
# Recurrence root windows and interlacing

If the roots of the rows of a derivative or three-term recurrence stay in a window where the
leading multiplier is nonpositive, and sign conditions hold outside the window, then consecutive
rows interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Throughout, $P_n$ are real polynomials with $\deg P_n=D_0+n$ and positive leading coefficient,
and $A_n,B_n,a_n,b_n$ are real polynomials; inequalities such as $A_n\le0$ on a set mean
$A_n(x)\le0$ at each $x$ of the set. When $D_0=0$ we assume $P_0\ll P_1$.

**Theorem (root window).** Let $P_{n+1}=A_nP_n'+B_nP_n$ and let $L,U\in\mathbb R$. Suppose $P_0$
splits with all roots in $[L,U]$, and for all $n$:

- $A_n\le0$ on $[L,U]$;
- $A_n\ge0$ on $(-\infty,L)\cup(U,\infty)$, with $B_n>0$ on $(U,\infty)$ and $B_n<0$ on
  $(-\infty,L)$.

Then $P_n\ll P_{n+1}$ for all $n$. The same holds when there is no lower bound: all roots of $P_0$
are at most $U$, $A_n\le0$ on $(-\infty,U]$, and $A_n\ge0$, $B_n>0$ on $(U,\infty)$.

**Theorem (degree-bounded window).** In the setting of the root window theorem, the conclusion
$P_n\ll P_{n+1}$ holds if the outside conditions are replaced by
$$
B_n(x)\,(x-U)+\min(A_n(x),0)\,(D_0+n)>0\quad\text{for }x>U,
$$
and the same inequality with $U$ replaced by $L$ for $x<L$.

**Theorem (moving windows).** Let $P_{n+1}=A_nP_n'+B_nP_n$ with real numbers $L_n$ nonincreasing and
$U_n$ nondecreasing, all roots of $P_0$ in $[L_0,U_0]$, and $A_n\le0$ on $[L_n,U_n]$. Suppose
that for $x>U_{n+1}$ either $A_n(x)\ge0$ and $B_n(x)>0$, or the degree-bounded inequality at
$U_{n+1}$
holds, and that for $x<L_{n+1}$ either $A_n(x)\ge0$ and $B_n(x)<0$, or the degree-bounded
inequality at $L_{n+1}$ holds. Then $P_n\ll P_{n+1}$ for all $n$.

Two quotient forms clear denominators $q_n>0$ from all hypotheses. For a fixed $U$ and a
nonincreasing lower bound $L_n=p_n/q_n$, the outside conditions are the plain sign conditions.
For a nondecreasing upper bound $U_n=p_n/q_n$ with no lower bound, $A_n\le0$ on $(-\infty,U_n]$;
for a point $r$ we ask $A_n\ge0$ and $B_n>0$ on $U_{n+1}<x\le r$, and $A_n\le0$ together with the
degree-bounded inequality on $x>r$.

**Theorem (endpoint windows).** Let $P_{n+1}=A_nP_n'+B_nP_n$ and let $W_n\subseteq\mathbb R$ with
$A_n\le0$ on $W_n$. Suppose $P_0$ splits with all roots in $W_0$, and for every $n$: if $P_n$
splits, all its roots lie in $W_n$ and $P_n\ll P_{n+1}$, then all roots of $P_{n+1}$ lie in
$W_{n+1}$. Then $P_n\ll P_{n+1}$ for all $n$.

**Theorem (three-term recurrences).** Let $P_{n+2}=a_nP_{n+1}+b_nP_n$ with $P_0\ll P_1$, and let
all roots of $P_0$ and $P_1$ lie in $[L,U]$. Suppose that for all $n$, $b_n\le0$ on $[L,U]$,
$a_n>0$ and $b_n\ge0$ on $(U,\infty)$, and $a_n<0$ and $b_n\ge0$ on $(-\infty,L)$. Then
$P_n\ll P_{n+1}$ for all $n$.

Two variants allow $b_n<0$ beyond $U$.

- *Ratio.* Let all roots of $P_0,P_1$ be at most $U$, let $b_n\le0$ on $(-\infty,U]$, and let
  $\rho_n$ be reals with $\rho_n\,\mathrm{lc}(P_n)\le\mathrm{lc}(P_{n+1})$. If $a_n\ge0$ and
  $a_n\rho_n(x-U)+b_n>0$ on $(U,\infty)$, then $P_n\ll P_{n+1}$.
- *Barrier.* Keep the hypotheses of the three-term theorem on $[L,U]$ and $(-\infty,L)$, and
  replace those on $(U,\infty)$ by a function $\rho>0$ on $(U,\infty)$ with $\rho\le a_n$,
  $\rho^2\le a_n\rho+b_n$ and $\rho P_0\le P_1$ there. Then $P_n\ll P_{n+1}$.

**Theorem (lag feedback).** Let $p\ge2$, $\alpha>0$, $c_n>0$ and
$$
P_{n+p}=\alpha P_{n+p-1}+c_n\,x\,P_n .
$$
If $P_0,\dots,P_{p-1}$ are positive constants, every $P_n$ splits. If instead
$P_0,\dots,P_{p-1}$ have nonnegative coefficients and $P_i\ll P_j$ for $i<j<p$, then
$P_{n+i}\ll P_{n+j}$ for all $n$ and $i<j<p$.

**Theorem (parity products).** Let $\beta,\mu$ be polynomials and let $s_m,t_m$ satisfy
$x_{m+2}=\beta x_{m+1}-\mu^2x_m$. Let $P_n$ satisfy
$$
P_{n+3}=(\beta+\mu)P_{n+2}-(\mu^2+\mu\beta)P_{n+1}+\mu^3P_n,
$$
with $P_0=s_0t_0$, $P_1=s_1t_0$, $P_2=s_1t_1$ and
$s_1t_1-s_2t_0=\mu\,(s_1t_0-s_0t_1)$. Then $P_{2m}=s_mt_m$ and $P_{2m+1}=s_{m+1}t_m$. If
$s_m\ll s_{m+1}$ and $t_m\ll t_{m+1}$ for all $m$, then $P_n\ll P_{n+1}$ for all $n$.

**Theorem (remainder certificate).** Let $R=ax^2+bx+c$ with $a>0$, let $p>0$, and let
$S_0=R\,(px+d)+\alpha x+\beta$. If $\alpha<0$ and $a\beta^2-b\alpha\beta+c\alpha^2<0$, then
$R\ll S_0$. If $R=ax+b$ with $a>0$ and $S_0=R\,(px+d)+\beta$, then $\beta<0$ suffices. Moreover, if
$q$ is a nonzero split polynomial and $qS=R\,(px+d)+\alpha x+\beta$, with the same conditions on
$a,p,\alpha,\beta$, then $q^mR\ll q^{m+1}S$ for all $m$; likewise for $R=ax+b$ and
$qS=R\,(px+d)+\beta$ with $\beta<0$.

**Theorem (reversal).** Let $P_n=\operatorname{reflect}_{D_0+n}R_n$, that is,
$P_n=x^{D_0+n}R_n(1/x)$.

- If $R_n$ splits for all $n$ and $\deg R_n\le D_0+n$, then every $P_n$ splits.
- If $\deg R_n=D_0+n$, each $R_n$ has nonnegative coefficients, $P_n$ has degree $D_0+n$ and
  positive leading coefficient, and $R_n\ll R_{n+1}$ for all $n$, then $P_n\ll P_{n+1}$.
- Suppose $\deg R_n\le D_0+n$ and $P_0=\operatorname{reflect}_{D_0}R_0$. If
  $P_{n+2}=a_nP_{n+1}+b_nP_n$ with $\deg a_n\le1$, $\deg b_n\le2$,
  $P_1=\operatorname{reflect}_{D_0+1}R_1$, and $R_{n+2}=a_n'R_{n+1}+b_n'R_n$ with
  $a_n'=\operatorname{reflect}_1a_n$ and $b_n'=\operatorname{reflect}_2b_n$, then
  $P_n=\operatorname{reflect}_{D_0+n}R_n$ for all $n$.
- Suppose $P_{n+1}=A_{2,n}P_n''+A_{1,n}P_n'+A_{0,n}P_n$ with $\deg A_{i,n}\le i+1$, and that
  $R_n$ satisfies the recurrence with coefficients $B_{2,n}=x^2\operatorname{reflect}_3A_{2,n}$,
  $B_{1,n}=-x\bigl((2(D_0+n)-2)\operatorname{reflect}_3A_{2,n}
  +\operatorname{reflect}_2A_{1,n}\bigr)$ and
  $$
  B_{0,n}=(D_0+n)(D_0+n-1)\operatorname{reflect}_3A_{2,n}+(D_0+n)\operatorname{reflect}_2A_{1,n}
  +\operatorname{reflect}_1A_{0,n}.
  $$
  If $\deg R_n\le D_0+n$ and $P_0=\operatorname{reflect}_{D_0}R_0$,
  then $P_n=\operatorname{reflect}_{D_0+n}R_n$ for all $n$.

## Use

The endpoint window theorem is the form of Ma–Wang, Theorem 2, in which endpoint signs place
the next row in its window. The tactics `rr_row_interlaces` and `rr_row_splits` select these
routes. The moving upper bound with a split point covers the root pattern of OEIS A110608.

## References

See [@LiuWang2007; @Branden2006].
<!-- /realrooted-catalog-content -->
-/
