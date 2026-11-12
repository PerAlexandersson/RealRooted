module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Derivative.FamilyClosure
public import RealRooted.Derivative.Interlacing
public import RealRooted.Derivative.RootCounting
public import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks
public import RealRooted.ObreschkoffConverse.Derivative
public import RealRooted.PolarDerivative

/-!
# Interlacing of derivatives of real-rooted polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "derivative-interlacing"
formalized = "2026-05-12"
tags = []
references = [
  "Fisk2006x",
  "Obreschkoff1963",
  "Jensen1913",
]
authors = ["Rolle", "Laguerre", "Jensen", "Obreschkoff", "Fisk"]
years = [1691, 1882, 1913, 1963, 2006]

[[theorems]]
name = "RealRooted.derivative_interlaces_of_natDegree_ne_zero"
module = "RealRooted.Derivative.Interlacing"
label = "The derivative of a nonconstant real-rooted polynomial interlaces it"
headline = true

[[theorems]]
name = "RealRooted.Interl.derivative"
module = "RealRooted.ObreschkoffConverse.Derivative"
label = "Differentiation preserves interlacing, allowing zero polynomials"

[[theorems]]
name = "RealRooted.exists_mem_Ioo_isRoot_derivative"
module = "RealRooted.Derivative.RootCounting"
label = "Rolle's theorem for polynomials"

[[theorems]]
name = "Polynomial.Splits.derivative"
module = "RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial"
label = "The derivative of a real-rooted polynomial is real-rooted"

[[theorems]]
name = "RealRooted.StrictInterl.derivative"
module = "RealRooted.ObreschkoffConverse.Derivative"
label = "Differentiation preserves interlacing when the left polynomial is nonconstant"

[[theorems]]
name = "Polynomial.exists_mem_jensenDisk_of_isRoot_derivative"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks"
label = "Jensen: non-real zeros of p' lie in Jensen disks"

[[theorems]]
name = "RealRooted.splits_polarDerivative_of_splits"
module = "RealRooted.PolarDerivative"
label = "Laguerre: polar derivatives of real-rooted polynomials are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Interlacing of derivatives of real-rooted polynomials

The derivative of a real-rooted polynomial is real-rooted and interlaces it, and
differentiation preserves interlacing.

## Results

We write $f\ll g$ if $f$ interlaces $g$; see the
[interlacing page](/RealRooted/concepts/interlacing/). Common roots are allowed unless stated.

**Theorem (Rolle).** If $a<b$ are real zeros of a real polynomial $p$, then $p'(c)=0$ for some
$c$ with $a<c<b$.

**Theorem (derivative interlacing).** Let $f$ be a real-rooted polynomial of degree $d\ge1$ with
zeros $r_1\le\dotsb\le r_d$, listed with multiplicity. Then $f'$ is real-rooted of degree $d-1$,
and its zeros $s_1\le\dotsb\le s_{d-1}$ satisfy
$$
r_1\le s_1\le r_2\le s_2\le\dotsb\le s_{d-1}\le r_d,
$$
that is, $f'\ll f$. The derivative of every real-rooted polynomial is real-rooted.

**Theorem (differentiation preserves interlacing).** Let $f,g$ be real polynomials such that
$f=0$, $g=0$ or $f\ll g$. Then $f'=0$, $g'=0$ or $f'\ll g'$. If $f\ll g$ and $f$ is nonconstant,
then $f'$ and $g'$ are nonzero and $f'\ll g'$.

**Theorem (Jensen).** [@Jensen1913] Let $p$ be a nonconstant real polynomial. Every non-real
zero $w$ of $p'$ lies in a *Jensen disk* of $p$, that is, in the closed disk whose diameter is
the segment from a non-real zero $z$ of $p$ to $\bar z$.

**Theorem (Laguerre).** Let $f$ be real-rooted of degree $n$ and let $a\in\mathbb R$. Then the
polar derivative $nf+(a-x)f'$ is real-rooted.

## Proof

For derivative interlacing, we sort the zeros of $f$. A zero of multiplicity $m$ is a zero of
$f'$ of multiplicity $m-1$, and Rolle's theorem places one further zero of $f'$ strictly between
any two consecutive distinct zeros of $f$. This gives $d-1$ zeros of $f'$, counted with
multiplicity, in the required positions, and $f'$ has no others since its degree is $d-1$.

For preservation, we use Obreschkoff's theorem [@Obreschkoff1963]: $f\ll g$ implies that every
real linear combination $\lambda f+\mu g$ is zero or real-rooted. Differentiating the
combinations shows that the same holds for $f'$ and $g'$, and the converse direction of
Obreschkoff's theorem returns interlacing. A degree count fixes the orientation.

For Jensen's theorem, if $p'(w)=0\ne p(w)$ then $\sum_k1/(w-z_k)=0$ over the zeros $z_k$ of $p$.
Pairing each zero with its conjugate, a point $w$ outside every Jensen disk makes every term
have imaginary part of sign opposite to $\operatorname{Im}w$, which is impossible. If $p$ is
real-rooted, it has no Jensen disks, so $p'$ is real-rooted.

For Laguerre's theorem, after shifting $a$ to $0$ the polar derivative is the reversal of the
derivative of the reversal of $f$, and reversal preserves real-rootedness.

## References

For derivative interlacing, see [@Fisk2006x, Ch. 1] and [@Obreschkoff1963]. Jensen's theorem is
[@Jensen1913]. The statement $f'\ll f$ is the remark after
[Wagner's lemma on symmetricfunctions.com](sf:wagnerLemma).
<!-- /realrooted-catalog-content -->

This module exposes Rolle's theorem, derivative interlacing in all positive
degrees, and the preservation of interlacing under differentiation.  The
root-list construction lives in `RealRooted.Derivative.Interlacing`; the
preservation theorem is proved in `RealRooted.ObreschkoffConverse.Derivative`.
-/
