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
# Laguerre–Pólya class challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "laguerre-polya-class"
formalized = "2026-09-11"
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
headline = true

[[theorems]]
name = "RealRooted.IsLaguerrePolya.im_eq_zero_of_eq_zero"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros"
label = "A nonzero Laguerre–Pólya function has only real zeros"
headline = true

[[theorems]]
name = "RealRooted.IsLaguerrePolya.laguerre_form_nonneg"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Inequality"
label = "Laguerre's inequality for Laguerre–Pólya functions"
headline = true

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
# The Laguerre–Pólya class

We call a polynomial in $\mathbb R[x]$ *real-rooted* if it is zero or all of its zeros are real
(that is, it splits over $\mathbb R$). A function $f \colon \mathbb C \to \mathbb C$ is in the
**Laguerre–Pólya class** (`IsLaguerrePolya`) if there are real-rooted polynomials
$p_n \in \mathbb R[x]$ such that $p_n \to f$ locally uniformly on $\mathbb C$. The zero function
belongs to the class, because we allow the zero polynomial.

The **type I** subclass (`IsLaguerrePolyaTypeI`) asks that the approximating polynomials be
Pólya-frequency polynomials. Every type I function is Laguerre–Pólya. Type I functions are the
exponential generating functions of the PF multiplier sequences, see the
[multiplier sequences page](/RealRooted/concepts/multiplier-sequences/).

## Closure properties

Let $f$ and $g$ be Laguerre–Pólya functions. Then each of the following is again
Laguerre–Pólya.

- The product $fg$, and the real multiples $c f$ for $c \in \mathbb R$.
- The real affine substitution $z \mapsto f(az + b)$ for $a, b \in \mathbb R$.
- The derivative $f'$.
- The locally uniform limit of any sequence $f_m$ of Laguerre–Pólya functions. It is enough to
  approximate $f$ on every closed disc $|z| \leq R$ to within every $\varepsilon > 0$ by a
  real-rooted real polynomial.

Moreover $f(\bar z) = \overline{f(z)}$ for all $z \in \mathbb C$.

## Analytic properties and zeros

Every Laguerre–Pólya function $f$ is entire (complex differentiable on all of $\mathbb C$, and
analytic). If $f \neq 0$, then its zero set is closed and discrete, and **every zero of $f$ is
real**: $f(z) = 0$ implies $\operatorname{Im} z = 0$.

**Laguerre's inequality.** For a Laguerre–Pólya function $f$ and $x \in \mathbb R$,
$$
\bigl(\operatorname{Re} f'(x)\bigr)^2 -
  \operatorname{Re} f(x)\,\operatorname{Re} f''(x) \;\geq\; 0 .
$$
For real-rooted polynomials this is on the
[Wronskian criterion page](/RealRooted/theorems/wronskian-criterion/).

## Examples

The complex exponential $e^z$ is Laguerre–Pólya (and of type I). By
[Hutchinson's theorem](/RealRooted/theorems/hutchinson/), if $a_k > 0$ and
$4 a_k a_{k+2} \leq a_{k+1}^2$ for all $k$, then $\sum_k a_k z^k$ is a Laguerre–Pólya function.

## The operator $\varphi(D)$

For $\varphi \colon \mathbb C \to \mathbb C$ and a real polynomial $g$, let
$$
\varphi(D)\, g = \sum_{k=0}^{\deg g}
  \operatorname{Re}\!\Bigl(\frac{\varphi^{(k)}(0)}{k!}\Bigr)\, g^{(k)} ,
$$
where $D$ is differentiation, as in `taylorDifferentialOperator`.

**Theorem** (Laguerre–Pólya operator theorem). If $\varphi$ is Laguerre–Pólya and $g$ is a
real-rooted real polynomial, then $\varphi(D)\, g$ is zero or real-rooted.

## Products

**Theorem.** Let $c, b \in \mathbb R$, $a \geq 0$, $m \in \mathbb N$, and let
$(y_k)_{k \geq 0}$ be real numbers with $\sum_k y_k^2 < \infty$. Then
$$
f(z) = c\, z^m e^{-a z^2 + b z} \prod_{k \geq 0} (1 - y_k z)\, e^{y_k z}
$$
is Laguerre–Pólya. The $y_k$ are the reciprocals of the nonzero zeros of $f$; a factor with
$y_k = 0$ equals $1$, so functions with finitely many zeros are included. The approximating
polynomials are
$$
c\, x^m \Bigl(1 - \frac{a x^2}{n}\Bigr)^{n} \Bigl(1 + \frac{b x}{n}\Bigr)^{n}
  \prod_{k < n} (1 - y_k x) \Bigl(1 + \frac{y_k x}{n}\Bigr)^{n} .
$$

The converse, that every Laguerre–Pólya function has this form (Laguerre and Pólya), is not
formalized; it is tracked in GitHub issue #1868.

## Proof idea

The class is closed under limits by a diagonal argument. Given a disc and $\varepsilon$, we pick
one $f_m$ uniformly $\varepsilon/2$-close to $f$ on the disc, and then a real-rooted polynomial
$\varepsilon/2$-close to $f_m$ there. Products, multiples and affine substitutions act on the
approximating polynomials. Locally uniform limits of entire functions are entire (Weierstrass),
and their derivatives converge locally uniformly. The derivative of a real-rooted polynomial is
real-rooted, which gives closure under differentiation.

For the zeros, we use that for a real-rooted $p$ the modulus $|p(x + iy)|$ does not decrease
as $|y|$ increases. This passes to the limit. If $f(x + iy_0) = 0$ with $y_0 \neq 0$, then $f$
vanishes on the whole vertical segment $\{x + iy : |y| \leq |y_0|\}$. This segment accumulates
at $x$, so the identity theorem forces $f = 0$. Laguerre's inequality is the polynomial
inequality passed to the limit.

For products, $(1 + w/n)^n \to e^w$ uniformly on compact sets, the partial products
$\prod_{k < n} (1 - y_k z) e^{y_k z}$ converge uniformly on compact sets because
$|(1 - w) e^w - 1| \leq 3 |w|^2$ for $|w| \leq 1$, and the remaining correction factor tends
to $1$ because $\sum_k y_k^2 < \infty$.

For the operator theorem, the Hermite–Poulain theorem
([page](/RealRooted/theorems/hermite-poulain/)) shows that $p_n(D)$ preserves real-rootedness.
The Taylor coefficients of $p_n$ converge to those of $\varphi$, so $p_n(D)\, g$ converges to
$\varphi(D)\, g$. Real-rootedness passes to limits of polynomials of bounded degree.

## References

See [@SchurPolya1914], [@Levin1964, Ch. VIII], and [@Hutchinson1923].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The definition is in
`RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya`, and the closure, derivative, zero,
inequality and operator results are in the modules under
`RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya`. Hutchinson's theorem is in
`RealRooted.Hutchinson`.
-/
