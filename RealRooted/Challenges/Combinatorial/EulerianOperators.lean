module

import RealRooted.EulerBidiagonal
import RealRooted.EulerBidiagonal.General
import RealRooted.EulerBidiagonal.PairTheorem
import RealRooted.EulerOperator.CoupledInsertion
import RealRooted.EulerOperator.EulerMultiplier
import RealRooted.EulerOperator.OrbitPerturbation
import RealRooted.EulerOperator.OrbitPerturbationCayley
import RealRooted.EulerOperator.OrbitPerturbationFamily
import RealRooted.EulerOperator.OrbitPerturbationInterlacing
import RealRooted.EulerOperator.PowerSeries
import RealRooted.EulerianTriangles.LagTwoTriangle
import RealRooted.GeneralizedEulerian

/-!
# Eulerian operators and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "eulerian-operators"
formalized = "2026-11-01"
tags = ["realrooted-original"]
authors = ["Alexandersson"]
years = [2026]
references = [
  "Alexandersson2026Eulerian",
  "LiuWang2007",
  "MaWang2008",
]

[[definitions]]
name = "RealRooted.realEulerInsertionStep"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "The Euler step p ↦ (c + aX) p + (X - X²) p'"

[[definitions]]
name = "RealRooted.scaledEulerInsertionStep"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "The scaled Euler step p ↦ (σγ + βX) p + γ (1 - X) X p'"

[[definitions]]
name = "RealRooted.lagTwoEulerPolynomial"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "Rows of an Euler recurrence with a lag-two correction"

[[definitions]]
name = "RealRooted.centeredEulerOrbit"
module = "RealRooted.EulerOperator.OrbitPerturbation"
label = "The centered Euler orbit of the constant polynomial 1"

[[definitions]]
name = "RealRooted.EulerBidiagonal.step"
module = "RealRooted.EulerBidiagonal.Basic"
label = "The second-order step X + (θ + a)(θ + b)"

[[definitions]]
name = "RealRooted.EulerBidiagonal.generalStep"
module = "RealRooted.EulerBidiagonal.General"
label = "The second-order step κ(θ + a)(θ + b) + X(u + vθ)"

[[definitions]]
name = "RealRooted.powerSeriesEuler"
module = "RealRooted.EulerOperator.PowerSeries"
label = "The Euler operator X d/dX on formal power series"

[[theorems]]
name = "RealRooted.realEulerInsertionStep_simple_roots_strictInterl"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "An Euler step with c > 0 gives simple negative roots and interlacing"
headline = true

[[theorems]]
name = "RealRooted.coupledEuler_simple_roots_strictInterl"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "Coupled Euler families: simple negative roots and interlacing"

[[theorems]]
name = "RealRooted.coupledEuler_secondOrder"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "Second-order recurrence for Q_{n+2} in terms of Q_{n+1} and P_n"

[[theorems]]
name = "RealRooted.eulerMultiplier_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Scaled Euler steps: simple negative roots of F_n and (θ + σ) F_n, interlacing"

[[theorems]]
name = "RealRooted.lagTwoEulerPolynomial_certificate"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "A nonnegative lag-two correction preserves simple negative roots and interlacing"

[[theorems]]
name = "RealRooted.centeredEulerOrbit_add_monomial"
module = "RealRooted.EulerOperator.OrbitPerturbationInterlacing"
label = "Monomial perturbations of the centered Euler orbit interlace"

[[theorems]]
name = "RealRooted.strictInterl_of_orbitPerturbation_recurrence"
module = "RealRooted.EulerOperator.OrbitPerturbationFamily"
label = "A three-term θ-recurrence with perturbed seeds has interlacing rows"

[[theorems]]
name = "RealRooted.strictInterl_C_mul_generalizedEulerian_add"
module = "RealRooted.EulerOperator.OrbitPerturbationCayley"
label = "Perturbed generalized Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_step_of_strictInterl"
module = "RealRooted.EulerBidiagonal.Basic"
label = "The step X + (θ + a)(θ + b) preserves interlacing of negative-simple pairs"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_rows"
module = "RealRooted.EulerBidiagonal"
label = "Consecutive iterates of X + (θ + a)(θ + b) interlace"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_generalStep_of_strictInterl"
module = "RealRooted.EulerBidiagonal.PairTheorem"
label = "The step κ(θ + a)(θ + b) + X(u + vθ) preserves interlacing of negative-simple pairs"

[[theorems]]
name = "RealRooted.coeff_powerSeriesEuler_iterate"
module = "RealRooted.EulerOperator.PowerSeries"
label = "θ^k multiplies the coefficient of X^n by n^k"

[[theorems]]
name = "RealRooted.mul_iterate_derivation_eq_iterate_derivationShift_of_mul_eq"
module = "RealRooted.EulerOperator.PowerSeries"
label = "M D^k F = (D - c)^k N when D M = c M and M F = N"
-->

<!-- realrooted-catalog-content -->
# Eulerian operators and interlacing

Euler-type differential operators map polynomials with simple negative roots to polynomials
of the same kind of one higher degree, and the images interlace.

## Results

A polynomial is *negative-simple* if it has positive leading coefficient, simple roots, and
only real negative roots. For real $c$ and $a$, the *Euler step* is
$$
E_{c,a}\,p=(c+ax)\,p+(x-x^2)\,p'.
$$
For $c=1$ and $a=n-1$ this is the Eulerian operator $T_n$ of [@Alexandersson2026Eulerian]; the
theorem below holds for every $c>0$.

**Theorem (Euler step).** Let $c>0$ and let $p$ be real-rooted with simple roots, positive
leading coefficient, nonnegative coefficients, $p(0)>0$ and $\deg p<a$. Then $E_{c,a}\,p$ has
degree $\deg p+1$, positive leading coefficient, nonnegative coefficients, positive value at
$0$ and only simple negative roots. Moreover $p\ll E_{c,a}\,p$, and the two polynomials have
no common root.

**Theorem (coupled families).** Let $c>0$, and let $\lambda_n\ge0$ and $b_n>n$ be real numbers
such that $t_n=b_n+\lambda_n$ satisfies $t_{n+1}-t_n\ge1$. Put $P_0=Q_0=1$ and
$$
P_{n+1}=(c+\lambda_n+b_nx)\,P_n+(x-x^2)\,P_n',\qquad
Q_{n+1}=(c+t_nx)\,P_n+(x-x^2)\,P_n'.
$$
Then $P_n$ and $Q_n$ have degree $n$, positive leading coefficient, nonnegative coefficients
and simple negative roots, and
$$
P_n\ll P_{n+1},\qquad P_n\ll Q_{n+1},\qquad Q_n\ll Q_{n+1}.
$$

**Proposition (second-order form).** In the setting above, for all $n$,
$$
Q_{n+2}=\bigl(c+\lambda_n+(b_n+t_{n+1}-t_n)\,x\bigr)Q_{n+1}+(x-x^2)\,Q_{n+1}'
+\lambda_n\,(t_{n+1}-t_n-1)\,(x-x^2)\,P_n .
$$

**Theorem (scaled steps).** Let $\sigma>0$, let $\gamma_n>0$, and suppose
$\gamma_n(n-1)<\beta_n$ for $n\ge1$. Put $F_0=1$ and, with $\theta=x\,d/dx$,
$$
F_n=\bigl(\sigma\gamma_n+\beta_nx+\gamma_n(1-x)\theta\bigr)F_{n-1},\qquad
H_n=(\theta+\sigma)F_n .
$$
Then $F_n$ and $H_n$ have degree $n$, positive leading coefficient, nonnegative coefficients,
positive constant term and simple negative roots, and $H_n\ll H_{n+1}$ for all $n$.

**Theorem (lag-two correction).** Let $m\ge1$ and $\lambda_n\ge0$. For a polynomial $p$, let
$C_np$ be $p$ with the coefficient of $x^k$ multiplied by $(n+1-k)(k+1)$. Put $P_0=1$,
$P_1=1+x$ and
$$
P_{n+2}=\bigl(1+(1+m(n+1))\,x\bigr)P_{n+1}+m\,(x-x^2)\,P_{n+1}'+m\lambda_{n+2}\,x\,C_nP_n .
$$
Then $P_n$ has degree $n$, positive leading coefficient, nonnegative coefficients, positive
constant term and simple negative roots, and
$$
P_n\ll P_{n+1},\qquad C_nP_n\ll P_{n+1}.
$$

**Theorem (centered orbit).** Let $\alpha\ge\tfrac12$, $p_0=1$ and
$p_{n+1}=x\,p_n+\alpha\,(x^2-1)\,p_n'$. For $-1<b\le1$ and $n\ge1$, the polynomial
$p_n+bx^n$ has degree $n$, positive leading coefficient and simple roots, all real and in
$(-1,1)$, and $p_n+bx^n\ll p_{n+1}+bx^{n+1}$.

**Theorem (perturbed Eulerian rows).** Let $s\ge1$ and $c\ge\tfrac12$. Let $E_0=1$ and
$E_{n+1}=\bigl(1+(sn+1)x\bigr)E_n+s\,x(1-x)\,E_n'$. Then
$$
cE_n+(1-c)(1+x)^n\ \ll\ cE_{n+1}+(1-c)(1+x)^{n+1}\qquad\text{for all }n.
$$

**Theorem (three-term recurrence).** Let $s\ge1$ and $\kappa\ge s+4$, and write
$\theta=u\,d/du$. Let $Q_0=1$, $Q_1=1+2u$, $Q_2=1+\kappa u+\kappa u^2$ and, for $n\ge0$,
$$
(n+1)Q_{n+3}=(2n+3)(2u+1)\,Q_{n+2}+(n+1)s(u+1)\,\theta Q_{n+2}
-(n+2)(2u+1)\bigl((2u+1)Q_{n+1}+s(u+1)\,\theta Q_{n+1}\bigr).
$$
Then every $Q_n$ has simple roots, all real and in $(-1,0)$, and $Q_n\ll Q_{n+1}$.

**Theorem (second-order step).** Let $\theta=x\,d/dx$, let $a,b\ge0$ with $ab>0$, and
$$
T=x+(\theta+a)(\theta+b).
$$
If $f\ll g$ are negative-simple, $\deg g=\deg f+1$ and $f,g$ have no common root, then
$Tf\ll Tg$ and $Tf,Tg$ have no common root. Consequently the iterates $P_0=1$,
$P_{n+1}=TP_n$ satisfy $P_n\ll P_{n+1}$ without common roots, for all $n$.

More generally, let $\kappa,a,b>0$ and $u,v\in\mathbb R$, and put
$T=\kappa(\theta+a)(\theta+b)+x(u+v\theta)$, so that the case $\kappa=u=1$, $v=0$ is the
operator above. Let $f\ll g$ be negative-simple with $\deg f=d$, $\deg g=d+1$ and no common
root, and assume $u+vk>0$ for $k\le d+1$ and
$$
\kappa\Bigl(ab-\tfrac{(a+b+1)^2}{4}\Bigr)+\Bigl(u-\tfrac{(a+b+1)v}{2}\Bigr)t
-\tfrac{v^2}{4\kappa}\,t^2<0\quad\text{for all }t\le0.
$$
Then $Tf\ll Tg$ and $Tf,Tg$ have no common root.

**Theorem (Euler operator on power series).** The operator $\theta=x\,d/dx$ multiplies the
coefficient of $x^n$ by $n$, so $\theta^k$ multiplies it by $n^k$. More generally, let $D$ be a
derivation and let $M$ satisfy $DM=cM$ for a scalar $c$. If $MF=N$, then
$M\,D^kF=(D-c)^kN$ for all $k$.

## Use

Both $P_{n+1}$ and $Q_{n+1}$ are Euler steps of $P_n$, namely $E_{c+\lambda_n,b_n}P_n$ and
$E_{c,t_n}P_n$. The first two interlacings therefore follow from the Euler step theorem. The
third follows from the critical-sign criterion [@LiuWang2007; @MaWang2008] applied to the
second-order form, in which the lag term has nonnegative coefficient
$\lambda_n(t_{n+1}-t_n-1)$. The scaled step is $\gamma_n E_{\sigma,\beta_n/\gamma_n}$, and the
step $E_n\mapsto E_{n+1}$ in the perturbed Eulerian rows is $s\,E_{1/s,\,n+1/s}$. For $s=1$,
$E_n$ is the [Eulerian polynomial](rr:eulerian)
$\sum_{\pi\in S_{n+1}}x^{\operatorname{des}(\pi)}$. The power series identities turn an Euler
differential equation for a generating function into a recurrence for its coefficients.

## References

The critical-sign criterion is on the
[Ma–Wang and Liu–Wang page](rr:ma-wang-liu-wang). Related Eulerian
statements are on the [Eulerian compendium](rr:eulerian-compendium) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.EulerOperator`,
`RealRooted.EulerBidiagonal`, `RealRooted.EulerianTriangles` and
`RealRooted.GeneralizedEulerian`.
-/
