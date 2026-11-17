module

import RealRooted.Hutchinson
import RealRooted.Kurtz
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Inequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros

/-!
# Laguerre–Pólya class

<!-- realrooted-catalog
version = 1
kind = "method"
section = "concepts"
slug = "laguerre-polya-class"
formalized = "2026-09-11"
references = [
  "SchurPolya1914",
  "Levin1964",
  "Hutchinson1923",
  "Kurtz1992",
]
authors = ["Pólya", "Schur", "Hutchinson", "Kurtz"]
years = [1914, 1923, 1992]

[[definitions]]
name = "RealRooted.IsLaguerrePolya"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "Laguerre–Pólya class"

[[definitions]]
name = "RealRooted.taylorDifferentialOperator"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator"
label = "The operator φ(D) acting through the Taylor coefficients of φ"

[[theorems]]
name = "RealRooted.isLaguerrePolya_canonicalProduct"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalProduct"
label = "Canonical products with real zeros are Laguerre–Pólya"
headline = true

[[theorems]]
name = "RealRooted.IsLaguerrePolya.mul"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya"
label = "The Laguerre–Pólya class is closed under products"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.deriv"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative"
label = "The Laguerre–Pólya class is closed under differentiation"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.of_tendstoLocallyUniformly"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure"
label = "The Laguerre–Pólya class is closed under locally uniform limits"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.im_eq_zero_of_eq_zero"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros"
label = "A nonzero Laguerre–Pólya function has only real zeros"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.laguerre_form_nonneg"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Inequality"
label = "Laguerre's inequality for Laguerre–Pólya functions"

[[theorems]]
name = "RealRooted.IsLaguerrePolya.taylorDifferentialOperator_eq_zero_or_splits"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator"
label = "Laguerre–Pólya: φ(D) preserves real-rootedness"

[[theorems]]
name = "RealRooted.Hutchinson.isLaguerrePolya_tsum"
module = "RealRooted.Hutchinson"
label = "Hutchinson: Σ a_k zᵏ with a_k > 0 and a_{k+1}² ≥ 4 a_k a_{k+2} is Laguerre–Pólya"

[[theorems]]
name = "RealRooted.Kurtz.coefficient_criterion"
module = "RealRooted.Kurtz"
label = "Kurtz: positive coefficients with a_k² > 4 a_{k-1} a_{k+1} give a real-rooted polynomial"
-->

<!-- realrooted-catalog-content -->
# Laguerre–Pólya class

The Laguerre–Pólya class consists of the entire functions that are locally uniform limits of
real-rooted polynomials. It describes the multiplier sequences and the operators $\varphi(D)$
that preserve real-rootedness. Hutchinson and Kurtz gave coefficient conditions for membership
and for real-rootedness.

## Results

A function $f\colon\mathbb C\to\mathbb C$ is in the *Laguerre–Pólya class* if there are
real polynomials $p_n$, each zero or real-rooted, with $p_n\to f$ locally uniformly on
$\mathbb C$. It is of *type I* if the $p_n$ can be taken with nonnegative coefficients.

**Theorem (canonical products).** [@Levin1964, Ch. VIII] Let $c,b\in\mathbb R$, $a\ge0$,
$m\in\mathbb N$, and let $(y_k)_{k\ge0}$ be real with $\sum_ky_k^2<\infty$. Then
$$
f(z)=c\,z^me^{-az^2+bz}\prod_{k\ge0}(1-y_kz)\,e^{y_kz}
$$
is in the Laguerre–Pólya class.

**Theorem (closure and zeros).** The class is closed under products, differentiation and
locally uniform limits. Every Laguerre–Pólya function is entire, and a nonzero one has only
real zeros.

**Theorem (Laguerre's inequality).** For Laguerre–Pólya $f$ and $x\in\mathbb R$,
$$
\bigl(\operatorname{Re}f'(x)\bigr)^2-\operatorname{Re}f(x)\,\operatorname{Re}f''(x)\ \ge\ 0 .
$$

**Theorem (operators).** For a real polynomial $g$ let
$\varphi(D)\,g=\sum_k\operatorname{Re}\bigl(\varphi^{(k)}(0)/k!\bigr)g^{(k)}$, where $D=d/dx$.
If $\varphi$ is Laguerre–Pólya and $g$ is real-rooted, then $\varphi(D)\,g$ is zero or
real-rooted.

**Theorem (Hutchinson).** [@Hutchinson1923] If $a_k>0$ and $a_{k+1}^2\ge4a_ka_{k+2}$ for all
$k\ge0$, then $\sum_ka_kz^k$ is in the Laguerre–Pólya class.

**Theorem (Kurtz).** [@Kurtz1992] Let $\sum_{k=0}^na_kx^k$ have degree $n\ge2$, with $a_k>0$
for $0\le k\le n$ and $a_k^2>4a_{k-1}a_{k+1}$ for $0<k<n$. Then all its roots are real.

## Use

Type I functions are the exponential generating functions of PF multiplier sequences in the
[Pólya–Schur theorem](rr:multiplier-sequences). The operator theorem extends the
[Hermite–Poulain theorem](rr:hermite-poulain) from polynomial symbols to entire ones, for
example to the heat operator $e^{-aD^2}$. Kurtz's theorem is a quick sufficient test for
real-rootedness that needs only the coefficients.

## Proof

For a real-rooted polynomial $p$, $|p(x+iy)|$ does not decrease as $|y|$ increases. This passes
to limits, so a nonreal zero would force $f$ to vanish on a vertical segment, and hence
everywhere. The operator theorem follows from the Hermite–Poulain theorem applied to the
approximants. For Hutchinson's theorem, the polynomials $\sum_{k<N}a_kq^{k^2}z^k$ with $q<1$
satisfy Kurtz's strict inequalities and approximate the series on every disc.

## References

[@SchurPolya1914]; [@Levin1964, Ch. VIII]; [@Hutchinson1923]; [@Kurtz1992]. See also
[Kurtz's theorem](sf:kurtzTheorem) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
