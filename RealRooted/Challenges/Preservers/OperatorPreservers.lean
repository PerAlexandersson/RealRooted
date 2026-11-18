module

public import RealRooted.Derivative.PowerShift
public import RealRooted.EulerOperator
public import RealRooted.EulerOperator.Polar.ProperPosition
public import RealRooted.NarayanaTransformation.Interlacing
public import RealRooted.OperatorInterlacingUpgrade.RootOrder
public import RealRooted.OperatorPreservesInterlacing
public import RealRooted.PFPolynomial.PreserverClosure
public import RealRooted.Transforms.ReverseHermite.Preservation

/-!
# Operators preserving interlacing

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "operator-preservers"
formalized = "2026-10-05"
references = [
  "Branden2004operators",
  "Branden2006",
  "Branden2011b",
]
authors = ["Brändén"]
years = [2004, 2006, 2011]

[[definitions]]
name = "RealRooted.PreservesRealRootedOrZero"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Real-rootedness preserver"

[[definitions]]
name = "RealRooted.theta"
module = "RealRooted.EulerOperator"
label = "The Euler operator θ = x d/dx"

[[theorems]]
name = "RealRooted.PreservesRealRootedOrZero.interl_or_reverse"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Brändén: real-rootedness preservers preserve interlacing up to orientation"
headline = true
symcat = "operatorPreservesInterlacing"

[[theorems]]
name = "RealRooted.strictInterl_map_of_monomialChain"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "$T(1) ≪ T(x) ≪ ⋯ ≪ T(x^D)$ gives $Tf ≪ Tg$ for $f ≪ g$ with nonnegative coefficients"

[[theorems]]
name = "RealRooted.isPFPolynomial_map_of_isNegativeSimple"
module = "RealRooted.PFPolynomial.PreserverClosure"
label = "Brändén: preserving simple negative-rooted inputs suffices for PF"

[[theorems]]
name = "RealRooted.Interl.theta"
module = "RealRooted.EulerOperator"
label = "θ preserves interlacing"

[[theorems]]
name = "RealRooted.Interl.polarTheta"
module = "RealRooted.EulerOperator.Polar.ProperPosition"
label = "N − θ preserves interlacing of PF polynomials of degree at most N"

[[theorems]]
name = "RealRooted.IsPFPolynomial.reverseHermiteTransform"
module = "RealRooted.Transforms.ReverseHermite.Preservation"
label = "The reverse-Hermite transform preserves PF polynomials"

[[theorems]]
name = "RealRooted.Interl.reverseHermiteTransform"
module = "RealRooted.Transforms.ReverseHermite.Preservation"
label = "The reverse-Hermite transform preserves interlacing"

[[theorems]]
name = "RealRooted.strictInterl_narayanaTransform"
module = "RealRooted.NarayanaTransformation.Interlacing"
label = "The Mao–Wang Narayana transform preserves interlacing"

[[theorems]]
name = "RealRooted.StrictInterl.powerDerivativeShift"
module = "RealRooted.Derivative.PowerShift"
label = "Dᵐ(D + c)xᵐ preserves interlacing for c ≠ 0"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Operators preserving interlacing

Brändén showed that every linear operator preserving real-rootedness also preserves
interlacing, up to orientation. For operators on polynomials with nonnegative coefficients, the
orientation is fixed once the images of the monomials form an interlacing chain. Euler
operators, the reverse-Hermite and Narayana transforms are examples.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. Here $f\ll g$ also holds when $f$ or $g$ is zero, as in the
[zero-aware convention](rr:about). Let $\theta=x\,d/dx$ and $D=d/dx$.

**Theorem (Brändén).** [@Branden2004operators, Thm. 8 in the arXiv version] Let $T$ be a
real-linear operator on $\mathbb R[x]$ such that $Tp$ is zero or real-rooted for every nonzero
real-rooted $p$. If $f\ll g$ are nonzero, then $Tf\ll Tg$ or $Tg\ll Tf$.

**Theorem (monomial chain).** Let $T$ be real-linear and $D\in\mathbb N$. Suppose that $T$
preserves nonnegative coefficients, maps every nonzero PF polynomial of degree at most $D$ to a
nonzero real-rooted polynomial, and $T(1)\ll T(x)\ll\dotsb\ll T(x^D)$. If $f\ll g$ have
nonnegative coefficients and $\deg g\le D$, then $Tf\ll Tg$.

**Theorem (from simple roots to PF; Brändén).** [@Branden2006, Cor. 3.5] If $Tq$ is PF for
every $q$ with positive leading coefficient and simple negative roots, then $Tp$ is PF for
every PF polynomial $p$.

**Corollary (examples).**

- If $p\ll q$, then $\theta p\ll\theta q$. If $p\ll q$ are PF of degree at most $N$, then
  $Np-xp'\ll Nq-xq'$.
- Let $B_0=1$, $B_1=x$, $B_{n+2}=x\bigl(B_{n+1}+(n+1)B_n\bigr)$, and $R(x^n)=B_n$. Then $R$
  maps PF polynomials to PF polynomials, and $p\ll q$ implies $Rp\ll Rq$ for PF $p,q$.
- The Mao–Wang [Narayana transform](rr:narayana) $N_m$ satisfies $N_mf\ll N_mg$ whenever
  $f\ll g$ have nonnegative coefficients.
- For $c\ne0$ and $m\in\mathbb N$, $T_{m,c}f=D^m\bigl((D+c)(x^mf)\bigr)$ maps real-rooted
  polynomials to real-rooted polynomials of the same degree, and $f\ll g$ implies
  $T_{m,c}f\ll T_{m,c}g$.

## Use

Brändén's theorem reduces interlacing preservation to real-rootedness preservation, which the
[Borcea–Brändén classification](rr:borcea-branden-classification) characterizes. The monomial
chain reduces it further to a finite check on monomials; this is how the Narayana transform is
handled. [Multiplier sequences](rr:multiplier-sequences) and the operators of the
[Hermite–Poulain theorem](rr:hermite-poulain) are the classical cases.

## Proof

By the [Hermite–Kakeya–Obreschkoff theorem](rr:hermite-kakeya-obreschkoff), $f$ and $g$
interlace exactly when every real combination $af+bg$ is real-rooted; applying $T$ keeps this
property, so $Tf$ and $Tg$ interlace. For the monomial chain, a closure property of quadratic
pencils $H+2bG+b^2F$ with $F\ll G\ll H$ propagates the chain to all PF inputs, one linear factor
at a time. For the transfer to PF, $(1+\varepsilon D)^dp$ has simple negative roots and tends to
$p$ as $\varepsilon\to0^+$.

## References

[@Branden2004operators, Thm. 8 in the arXiv version]; [@Branden2006, Cor. 3.5];
[@Branden2011b]. See also [operators preserving interlacing](sf:operatorPreservesInterlacing)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
