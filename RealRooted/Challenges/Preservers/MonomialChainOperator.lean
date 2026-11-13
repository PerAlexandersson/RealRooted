module

public import RealRooted.NarayanaTransformation.Interlacing
public import RealRooted.OperatorInterlacingUpgrade.ImplicitRoot
public import RealRooted.OperatorInterlacingUpgrade.RootOrder
public import RealRooted.OperatorInterlacingUpgrade.StablePencil
public import RealRooted.PFPolynomial
public import RealRooted.QuadraticInterlacingClosure

/-!
# Interlacing from a monomial chain

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monomial-chain-operator"
formalized = "2026-05-12"
authors = []
tags = []
references = [
  "Branden2011b",
]

[[definitions]]
name = "RealRooted.quadraticInterlacingPencil"
module = "RealRooted.QuadraticInterlacingClosure"
label = "Quadratic interlacing pencil"

[[definitions]]
name = "RealRooted.quadraticInterlacingTangent"
module = "RealRooted.QuadraticInterlacingClosure"
label = "Tangent of the quadratic interlacing pencil"

[[theorems]]
name = "RealRooted.strictInterl_map_of_monomialChain"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "The monomial chain gives interlacing preservation"
headline = true

[[theorems]]
name = "RealRooted.rootwiseLE_monomialChain_rootPolynomial_list_set"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "Moving one input root right moves every output root right"

[[theorems]]
name = "RealRooted.rootwiseLE_monomialChain_component_bounds"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "Output roots are bounded by the images of (x + a)^D and (x + b)^D"

[[theorems]]
name = "RealRooted.strictInterl_narayanaTransform"
module = "RealRooted.NarayanaTransformation.Interlacing"
label = "The Mao–Wang Narayana transform preserves interlacing"

[[theorems]]
name = "RealRooted.exists_hasDerivAt_finRootPolynomial_shift"
module = "RealRooted.OperatorInterlacingUpgrade.ImplicitRoot"
label = "Implicit derivative of a simple output root in one input root"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_bivariatePencil_map_of_monomialChain"
module = "RealRooted.OperatorInterlacingUpgrade.StablePencil"
label = "Monomial-chain operators preserve nonnegative stable pencils"

[[theorems]]
name = "RealRooted.quadraticParameterEvaluation_positiveRootCount_le"
module = "RealRooted.QuadraticInterlacingClosure"
label = "Descartes budget for the quadratic parameter evaluation of an interlacing chain"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.strictInterl_quadraticInterlacingTangent_pencil"
module = "RealRooted.QuadraticInterlacingClosure"
label = "The tangent of a real-rooted quadratic pencil precedes the pencil"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.strictInterl_quadraticInterlacingRight_of_tangent"
module = "RealRooted.QuadraticInterlacingClosure"
label = "The tangent precedes the right member of the quadratic closure"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Interlacing from a monomial chain

A linear operator that preserves nonnegative coefficients and real-rootedness of PF inputs, and
maps the monomials $1,x,\dotsc,x^D$ to an interlacing chain, preserves interlacing of
pairs with nonnegative coefficients and degree at most $D$. This reduces interlacing preservation
to a check on monomials.

## Results

A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real, nonpositive roots.

**Theorem (monomial chain).** Let $T$ be a real-linear operator on $\mathbb R[x]$ and
$D\in\mathbb N$. Suppose that

1. $T$ maps polynomials with nonnegative coefficients to polynomials with nonnegative
   coefficients;
2. $T$ maps every nonzero PF polynomial of degree at most $D$ to a nonzero real-rooted
   polynomial;
3. $T(1)\ll T(x)\ll\dotsb\ll T(x^D)$.

If $f\ll g$ have nonnegative coefficients and $\deg g\le D$, then $Tf\ll Tg$.

**Theorem (rootwise order).** Let $T$ satisfy (1)--(3), and in addition $\deg Tp=D$ whenever
$\deg p=D$. Let $r_1,\dotsc,r_D\le0$ be the roots of a monic polynomial $p$ of degree $D$.

- If one root $r_i$ is replaced by some $b$ with $r_i\le b\le0$, then each root of the image
  $T p$, in increasing order, does not decrease.
- If $0\le a\le b$ and all roots of $p$ lie in $[-b,-a]$, then each root of
  $T\bigl((x+b)^D\bigr)$ is at most the corresponding root of $Tp$, which is at most the
  corresponding root of $T\bigl((x+a)^D\bigr)$.

**Theorem (root derivative).** Let $T$ be linear, $p=\prod_i(x-r_i)$, and let $\rho$ be a simple
root of $Tp$. Then for each $i$ there is a function $\rho(s)$, differentiable at $0$, with
$\rho(0)=\rho$ and $\rho(s)$ a root of $T\bigl((x-r_i-s)\prod_{j\ne i}(x-r_j)\bigr)$ for
all small $s$, and
$$
\rho'(0)=\frac{T\bigl(p/(x-r_i)\bigr)(\rho)}{(Tp)'(\rho)} .
$$

**Theorem (stable pencils).** Let $T$ satisfy (1)--(3), and let $f,g\ne0$ have nonnegative
coefficients with $1\le\deg f\le D$ and $\deg Tf\ge1$. If $f(z)+w\,g(z)$ is
upper-half-plane stable, then so is $(Tf)(z)+w\,(Tg)(z)$.

**Corollary (Narayana transform).** The Mao–Wang Narayana transform $N_m$ satisfies
$N_mf\ll N_mg$ whenever $f\ll g$ have nonnegative coefficients; see the
[Narayana page](rr:narayana).

The proof rests on a closure property of quadratic pencils. Let $F\ll G\ll H$ have nonnegative
coefficients. For $b\ge0$ put
$$
Q_b=H+2bG+b^2F,\qquad A_b=G+bF,\qquad B_b=H+bG .
$$

**Theorem (quadratic closure).** If $Q_b$ is real-rooted for every $b\ge0$, then $A_a\ll Q_a$
and $A_a\ll B_a$ for every $a\ge0$. That is,
$$
G+aF\ \ll\ H+aG .
$$

If $F,G,H$ have positive leading coefficients and $r$ is a root of none of them, then the
quadratic $b\mapsto Q_b(r)$ has at most as many positive roots as the number of roots of $H$
above $r$ minus the number of roots of $F$ above $r$.

## Proof

The quadratic closure propagates the monomial chain through all PF inputs, one nonpositive linear
factor at a time. The Garloff–Wagner Krein expansion then passes from one-root deletions to every
interlacing pair.

## References

- [@Branden2011b]
<!-- /realrooted-catalog-content -->

This module exposes the fully checked monomial-chain upgrade.
-/
