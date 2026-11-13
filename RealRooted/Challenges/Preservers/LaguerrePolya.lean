module

import RealRooted.Hutchinson
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Inequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros

/-!
# Laguerre–Pólya class

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "laguerre-polya-class"
formalized = "2026-09-11"
tags = []
references = [
  "SchurPolya1914",
  "Levin1964",
  "Hutchinson1923",
]
authors = ["Pólya", "Schur"]
years = [1914]

[[definitions]]
name = "RealRooted.IsLaguerrePolya"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "Laguerre–Pólya class"

[[definitions]]
name = "RealRooted.taylorDifferentialOperator"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator"
label = "The operator φ(D) acting through the Taylor coefficients of φ"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.zero"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "The zero function is Laguerre–Pólya"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.conj"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "Laguerre–Pólya functions commute with complex conjugation"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.mul"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "The Laguerre–Pólya class is closed under products"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.const_mul_real"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "The Laguerre–Pólya class is closed under real constant multiples"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.comp_affine_real"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "The Laguerre–Pólya class is closed under real affine substitutions"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.of_forall_approx"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure"
label = "Approximation on every disc by real-rooted polynomials suffices"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.differentiable"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative"
label = "Laguerre–Pólya functions are entire"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.analyticOnNhd"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative"
label = "Laguerre–Pólya functions are analytic on the whole plane"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.isClosed_and_isDiscrete_preimage_zero"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative"
label = "The zeros of a nonzero Laguerre–Pólya function are closed and discrete"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.deriv"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative"
label = "The Laguerre–Pólya class is closed under differentiation"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.im_eq_zero_of_eq_zero"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros"
label = "A nonzero Laguerre–Pólya function has only real zeros"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.laguerre_form_nonneg"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Inequality"
label = "Laguerre's inequality for Laguerre–Pólya functions"

[[theorems]]
name = "RealRooted.IsLaguerrePolyaTypeI.toLaguerrePolya"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI"
label = "Type I functions are Laguerre–Pólya"

[[theorems]]
name = "RealRooted.isLaguerrePolya_exp"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples"
label = "The complex exponential is Laguerre–Pólya"

[[theorems]]
name = "RealRooted.isLaguerrePolya_canonicalProduct"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalProduct"
label = "Canonical products with real zeros are Laguerre–Pólya"
headline = true
-->

<!-- realrooted-catalog-content -->
# Laguerre–Pólya class

A function $\mathbb C\to\mathbb C$ is Laguerre–Pólya if it is a locally uniform limit of
real-rooted real polynomials; such a function is entire, and a nonzero one has only real zeros.
The class describes the multiplier sequences and the differential operators $\varphi(D)$ that
preserve real-rootedness.

## Results

A real polynomial is *real-rooted* if it is zero or splits over $\mathbb R$. A function
$f\colon\mathbb C\to\mathbb C$ is in the *Laguerre–Pólya class* if there are real-rooted
polynomials $p_n\in\mathbb R[x]$ with $p_n\to f$ locally uniformly on $\mathbb C$. The zero
function belongs to the class. It is of *type I* if the $p_n$ can be taken to be PF
(Pólya frequency) polynomials; every type I function is Laguerre–Pólya.

**Theorem (closure).** Let $f,g$ be Laguerre–Pólya. Then $fg$, $cf$ for $c\in\mathbb R$,
$z\mapsto f(az+b)$ for $a,b\in\mathbb R$, and $f'$ are Laguerre–Pólya. Moreover
$f(\bar z)=\overline{f(z)}$. A function $f$ is Laguerre–Pólya if for every $R,\varepsilon>0$
some real-rooted real polynomial $p$ satisfies $|f(z)-p(z)|<\varepsilon$ for $|z|\le R$.

**Theorem (zeros).** A Laguerre–Pólya function $f$ is entire. If $f\ne0$, its zero set is closed
and discrete, and every zero is real: $f(z)=0$ implies $\operatorname{Im}z=0$.

**Theorem (Laguerre's inequality).** For Laguerre–Pólya $f$ and $x\in\mathbb R$,
$$
\bigl(\operatorname{Re}f'(x)\bigr)^2-\operatorname{Re}f(x)\,\operatorname{Re}f''(x)\ \ge\ 0 .
$$

**Theorem (canonical products).** Let $c,b\in\mathbb R$, $a\ge0$, $m\in\mathbb N$, and let
$(y_k)_{k\ge0}$ be real with $\sum_ky_k^2<\infty$. Then
$$
f(z)=c\,z^me^{-az^2+bz}\prod_{k\ge0}(1-y_kz)\,e^{y_kz}
$$
is Laguerre–Pólya.

**Theorem (examples).** The function $e^z$ is Laguerre–Pólya. If $a_k>0$ and
$4a_ka_{k+2}\le a_{k+1}^2$ for all $k$, then $\sum_ka_kz^k$ is Laguerre–Pólya; this is
[Hutchinson's theorem](rr:hutchinson).

**Theorem (operator).** For $\varphi\colon\mathbb C\to\mathbb C$ and a real polynomial $g$ let
$$
\varphi(D)\,g=\sum_{k=0}^{\deg g}\operatorname{Re}\!\Bigl(\frac{\varphi^{(k)}(0)}{k!}\Bigr)g^{(k)},
\qquad D=\frac d{dx}.
$$
If $\varphi$ is Laguerre–Pólya and $g$ is real-rooted, then $\varphi(D)\,g$ is real-rooted.

**Theorem (type I and multiplier sequences).** Let $\gamma$ be a real sequence such that
$\sum_k\gamma_kz^k/k!$ has positive radius of convergence. Then $\gamma$ is a PF multiplier
sequence if and only if $\sum_k\gamma_kz^k/k!$ is of type I.

## Use

Type I functions give the Pólya–Schur description of PF multiplier sequences; see the
[multiplier sequences](rr:multiplier-sequences) page. For real-rooted
polynomials, Laguerre's inequality is on the
[Wronskian criterion](rr:wronskian-criterion) page, and the operator theorem
rests on the [Hermite–Poulain theorem](rr:hermite-poulain).

## Proof

For a real-rooted polynomial $p$, $|p(x+iy)|$ does not decrease as $|y|$ increases. This passes
to limits, so a zero $x+iy_0$ of $f$ with $y_0\ne0$ would make $f$ vanish on the segment
$\{x+iy:|y|\le|y_0|\}$, and the identity theorem would give $f=0$. The operator theorem follows
because $p_n(D)\,g$ is real-rooted by the Hermite–Poulain theorem and converges to
$\varphi(D)\,g$ when $p_n\to\varphi$.

## References

- [@SchurPolya1914]
- [@Levin1964, Ch. VIII]
- [@Hutchinson1923]
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The definition is in
`RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya`, and the closure, derivative, zero,
inequality and operator results are in the modules under
`RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya`. Hutchinson's theorem is in
`RealRooted.Hutchinson`.
-/
