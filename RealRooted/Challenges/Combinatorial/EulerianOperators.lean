module

import RealRooted.EulerBidiagonal
import RealRooted.EulerBidiagonal.General
import RealRooted.EulerBidiagonal.PairTheorem
import RealRooted.EulerOperator.CoupledInsertion
import RealRooted.EulerOperator.EulerMultiplier
import RealRooted.EulerOperator.OrbitPerturbationCayley
import RealRooted.EulerianTriangles.LagTwoTriangle

/-!
# Eulerian operators and interlacing

<!-- realrooted-catalog
version = 1
kind = "method"
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
name = "RealRooted.EulerBidiagonal.generalStep"
module = "RealRooted.EulerBidiagonal.General"
label = "The second-order step κ(θ + a)(θ + b) + X(u + vθ)"

[[theorems]]
name = "RealRooted.realEulerInsertionStep_simple_roots_strictInterl"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "An Euler step with c > 0 keeps simple negative roots and gives an interlacing pair"
headline = true

[[theorems]]
name = "RealRooted.coupledEuler_simple_roots_strictInterl"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "Coupled Euler families: simple negative roots and interlacing"

[[theorems]]
name = "RealRooted.eulerMultiplier_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Scaled Euler steps: simple negative roots of F_n and (θ + σ) F_n, interlacing"

[[theorems]]
name = "RealRooted.lagTwoEulerPolynomial_certificate"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "A nonnegative lag-two correction preserves simple negative roots and interlacing"

[[theorems]]
name = "RealRooted.strictInterl_C_mul_generalizedEulerian_add"
module = "RealRooted.EulerOperator.OrbitPerturbationCayley"
label = "Perturbed generalized Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_rows"
module = "RealRooted.EulerBidiagonal"
label = "Consecutive iterates of X + (θ + a)(θ + b) interlace"

[[theorems]]
name = "RealRooted.EulerBidiagonal.strictInterl_generalStep_of_strictInterl"
module = "RealRooted.EulerBidiagonal.PairTheorem"
label = "The step κ(θ + a)(θ + b) + X(u + vθ) preserves interlacing of negative-simple pairs"

-->

<!-- realrooted-catalog-content -->
# Eulerian operators and interlacing

The Euler step $p\mapsto(c+ax)p+(x-x^2)p'$ generates the Eulerian polynomials. For $c>0$ it
maps a polynomial with simple negative roots to one of the same kind that it interlaces.
Variants cover coupled and scaled steps, lag-two corrections, perturbed Eulerian rows and
second-order steps.

## Results

A polynomial is *negative-simple* if it has positive leading coefficient, simple roots, and
only real negative roots. Write $\theta=x\,d/dx$. For real $c$ and $a$, the *Euler step* is
$$
E_{c,a}\,p=(c+ax)\,p+(x-x^2)\,p'.
$$

**Theorem (Euler step).** Let $c>0$ and let $p$ be real-rooted with simple roots, positive
leading coefficient, nonnegative coefficients, $p(0)>0$ and $\deg p<a$. Then $E_{c,a}\,p$ has
degree $\deg p+1$, nonnegative coefficients, positive value at $0$ and only simple negative
roots. Moreover $p\ll E_{c,a}\,p$, and the two polynomials have no common root.

**Theorem (coupled families).** Let $c>0$, and let $\lambda_n\ge0$ and $b_n>n$ be real numbers
such that $t_n=b_n+\lambda_n$ satisfies $t_{n+1}-t_n\ge1$. Put $P_0=Q_0=1$,
$P_{n+1}=E_{c+\lambda_n,b_n}P_n$ and $Q_{n+1}=E_{c,t_n}P_n$. Then $P_n$ and $Q_n$ have degree
$n$, nonnegative coefficients and simple negative roots, and $P_n\ll P_{n+1}$,
$P_n\ll Q_{n+1}$ and $Q_n\ll Q_{n+1}$.

**Theorem (variants).**

- *Scaled steps.* If $\sigma>0$, $\gamma_n>0$ and $\gamma_n(n-1)<\beta_n$ for $n\ge1$, then
  $F_0=1$, $F_n=\bigl(\sigma\gamma_n+\beta_nx+\gamma_n(1-x)\theta\bigr)F_{n-1}$ and
  $H_n=(\theta+\sigma)F_n$ have degree $n$ and simple negative roots, and $H_n\ll H_{n+1}$.
- *Lag-two correction.* Let $m\ge1$, $\lambda_n\ge0$, and let $C_np$ multiply the coefficient
  of $x^k$ in $p$ by $(n+1-k)(k+1)$. If $P_0=1$, $P_1=1+x$ and
  $P_{n+2}=\bigl(1+(1+m(n+1))\,x\bigr)P_{n+1}+m\,(x-x^2)\,P_{n+1}'+m\lambda_{n+2}\,x\,C_nP_n$,
  then $P_n$ has degree $n$ and simple negative roots, $P_n\ll P_{n+1}$ and $C_nP_n\ll P_{n+1}$.
- *Perturbed Eulerian rows.* If $s\ge1$, $c\ge\tfrac12$, $E_0=1$ and
  $E_{n+1}=\bigl(1+(sn+1)x\bigr)E_n+s\,x(1-x)\,E_n'$, then
  $cE_n+(1-c)(1+x)^n\ll cE_{n+1}+(1-c)(1+x)^{n+1}$.
- *Second-order steps.* Let $\kappa,a,b>0$, $u,v\in\mathbb R$ and
  $T=\kappa(\theta+a)(\theta+b)+x(u+v\theta)$. Let $f\ll g$ be negative-simple with
  $\deg f=d$, $\deg g=d+1$ and no common root, assume $u+vk>0$ for $k\le d+1$ and
  $$
  \kappa\Bigl(ab-\tfrac{(a+b+1)^2}{4}\Bigr)+\Bigl(u-\tfrac{(a+b+1)v}{2}\Bigr)t
  -\tfrac{v^2}{4\kappa}\,t^2<0\quad\text{for all }t\le0.
  $$
  Then $Tf\ll Tg$ without common roots. In particular, for $T=x+(\theta+a)(\theta+b)$ with
  $a,b>0$, the iterates $P_0=1$, $P_{n+1}=TP_n$ satisfy $P_n\ll P_{n+1}$.

## Use

The Eulerian polynomials are $A_{n+1}=E_{1,n}A_n$ with $A_1=1$, and the
[generalized Eulerian polynomials](rr:eulerian) are $s\,E_{1/s,\,n+1/s}$ applied row by row. The
same steps drive the descent polynomials of derangements on the
[Eulerian-type polynomials](rr:eulerian-compendium) page.

## Proof

At a root $r<0$ of $p$, $E_{c,a}\,p(r)=(r-r^2)\,p'(r)$, which alternates in sign, and the
degree condition places one more root to the left. Both $P_{n+1}$ and $Q_{n+1}$ are Euler steps
of $P_n$; the interlacing $Q_n\ll Q_{n+1}$ follows from the
[Liu–Wang criterion](rr:ma-wang-liu-wang) [@LiuWang2007; @MaWang2008] applied to a second-order
recurrence for $Q_n$ whose lag term has nonnegative coefficient.

## References

[@Alexandersson2026Eulerian]; [@LiuWang2007; @MaWang2008].
<!-- /realrooted-catalog-content -->
-/
