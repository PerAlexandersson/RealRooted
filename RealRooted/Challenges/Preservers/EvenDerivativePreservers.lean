module

import RealRooted.EvenDerivative.Basic
import RealRooted.EvenDerivative.Examples
import RealRooted.EvenDerivative.Interlacing
import RealRooted.EvenDerivative.Preserver
import RealRooted.EvenDerivative.Stability
import RealRooted.EvenDerivative.Symbol

/-!
# Even-derivative preservers: the finite-degree criterion

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "even-derivative-preservers"
formalized = "2026-11-09"
tags = ["realrooted-original"]
references = [
  "BorceaBranden2009I",
]

[[definitions]]
name = "RealRooted.evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Basic"
label = "The operator T_c f = ∑ cₖ xᵏ f^{(2k)}"

[[definitions]]
name = "RealRooted.evenDerivativeTest"
module = "RealRooted.EvenDerivative.Basic"
label = "The test polynomial p_N(z) = ∑ (-1)ᵏ cₖ (N)_{2k} z^{N-2k}"

[[definitions]]
name = "RealRooted.evenDerivativeSymbol"
module = "RealRooted.EvenDerivative.Symbol"
label = "The signed symbol ∑ (-1)ᵏ cₖ w^{2k}, so that p_N is the symbol applied to uᴺ"

[[theorems]]
name = "RealRooted.evenDerivative_preservesPF_tfae"
module = "RealRooted.EvenDerivative.Preserver"
label = "PF preservation through degree N, real-rootedness of T_c(uᴺ) and of p_N are equivalent"
headline = true

[[theorems]]
name = "RealRooted.isPFPolynomial_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Preserver"
label = "If p_N is real-rooted, T_c maps PF polynomials of degree at most N to PF polynomials"

[[theorems]]
name = "RealRooted.splits_evenDerivativeOperator_prod"
module = "RealRooted.EvenDerivative.Stability"
label = "If p_n is real-rooted, T_c ∏ (u + rᵢ) is real-rooted for rᵢ ≥ 0"

[[theorems]]
name = "RealRooted.mvRealStable_evenDerivativePolarization"
module = "RealRooted.EvenDerivative.Stability"
label = "The polarization of p_n is real stable (Grace–Walsh–Szegő)"

[[theorems]]
name = "RealRooted.evenDerivativeOperator_X_pow_comp"
module = "RealRooted.EvenDerivative.Basic"
label = "Folding: T_c(uᴺ)(-z²) = (-1)ᴺ zᴺ p_N(z)"

[[theorems]]
name = "RealRooted.splits_evenDerivativeTest_of_le"
module = "RealRooted.EvenDerivative.Preserver"
label = "Lower caps: if p_N is real-rooted so is p_n for n ≤ N"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator_X_pow_succ"
module = "RealRooted.EvenDerivative.Interlacing"
label = "Consecutive monomial images T_c(uᵐ) and T_c(uᵐ⁺¹) interlace"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Interlacing"
label = "T_c preserves directed interlacing of nonnegative-coefficient pairs through degree N"
headline = true

[[theorems]]
name = "RealRooted.interl_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Interlacing"
label = "T_c preserves zero-aware directed interlacing of PF pairs through degree N"

[[theorems]]
name = "RealRooted.splits_evenDerivativeOperator_X_add_C_mul"
module = "RealRooted.EvenDerivative.Interlacing"
label = "T_c((u + a) h) is real-rooted for PF h and every real a: one root of either sign"

[[theorems]]
name = "RealRooted.splits_evenDerivativeTest_of_splits_symbol"
module = "RealRooted.EvenDerivative.Symbol"
label = "Finitely supported c with a real-rooted signed symbol: p_N is real-rooted for every N"

[[theorems]]
name = "RealRooted.evenDerivativeOperator_capTwo_X_pow_four"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …): T_c(u⁴) = x²(x² + 12x + 24)"

[[theorems]]
name = "RealRooted.evenDerivativeOperator_capTwo_X_pow_five"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …): T_c(u⁵) = x³(x² + 20x + 120)"

[[theorems]]
name = "RealRooted.isPFPolynomial_evenDerivativeOperator_capTwo_of_natDegree_le_four"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …) the operator preserves PF polynomials through degree four"

[[theorems]]
name = "RealRooted.not_splits_evenDerivativeOperator_capTwo_X_pow_five"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …) T_c(u⁵) is not real-rooted: preservation fails in degree five"

[[theorems]]
name = "RealRooted.isPFPolynomial_evenDerivativeOperator_square"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 2, 1, 0, …), f + 2x f'' + x² f^(4) preserves PF polynomials in every degree"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator_square_X_add_one_pow"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 2, 1, 0, …) the images of (u+1)³ and (u+1)⁴ interlace"
-->

<!-- realrooted-catalog-content -->
# Even-derivative preservers: the finite-degree criterion

For a coefficient sequence $c=(c_k)_{k\ge0}$ with $c_0=1$ and $c_k\ge0$, let
$$
T_cf(x)=\sum_{k\ge0}c_k\,x^k f^{(2k)}(x),
$$
so that multiplication by $x^k$ is applied after differentiation. A polynomial is *PF* if it
is zero or has a positive leading coefficient and only real nonpositive roots; this includes
constants, repeated roots and the root zero. For $N\ge0$ write $(N)_{j}=N(N-1)\cdots(N-j+1)$
and
$$
p_N(z)=\sum_{k\le N/2}(-1)^k c_k\,(N)_{2k}\,z^{N-2k}.
$$

**Theorem (finite-degree criterion).** For every $N\ge0$ the following are equivalent.

1. $T_c$ maps every PF polynomial of degree at most $N$ to a PF polynomial.
2. The single image $T_c(u^N)$ is real-rooted.
3. The polynomial $p_N$ is real-rooted.

When they hold, $T_c$ also preserves directed (weak) interlacing of PF pairs of degree at most
$N$: $f\ll g$ implies $T_cf\ll T_cg$. Moreover $T_c((u+a)h)$ is real-rooted for every PF
polynomial $h$ with $\deg h<N$ and every real $a$, so $T_c$ also maps a real-rooted input with a
single positive root to a real-rooted output. No simplicity conclusion is claimed.

## Proof

*Folding.* Since $T_c(u^N)=\sum_kc_k(N)_{2k}u^{N-k}$ we have
$T_c(u^N)(-z^2)=(-1)^Nz^Np_N(z)$. A real polynomial is real-rooted with only nonpositive roots if
and only if its composition with $-z^2$ is real-rooted, and $T_c(u^N)$ has nonnegative
coefficients, which gives (2)$\Leftrightarrow$(3). Differentiating,
$p_N^{(N-n)}=(N)_{N-n}\,p_n$, so real-rootedness of $p_N$ passes to every $p_n$, $n\le N$
(Rolle).

*Polarization.* Let $M_n(\mathbf z)=\sum_{k\le n/2}(-1)^kc_k(2k)!\,e_{n-2k}(\mathbf z)$ in $n$
variables. It is symmetric and multiaffine with diagonal $p_n$, so by Grace–Walsh–Szegő it is
real stable once $p_n$ is real-rooted ([@BorceaBranden2009I], Proposition 2.4). For
$f=\prod_{i\le n}(u+r_i)$ with $r_i\ge0$ the maps $s_i(z)=z-r_i/z$ send the upper half-plane into
itself, and
$$
(-1)^nT_cf(-z^2)=z^n\,M_n\bigl(s_1(z),\dots,s_n(z)\bigr).
$$
Thus $T_cf(-z^2)$ has no zero in the upper half-plane, so it is real-rooted, and folding shows
that $T_cf$ is real-rooted with nonpositive roots. The leading coefficient is preserved and the
coefficients stay nonnegative, so $T_cf$ is PF. This proves (3)$\Rightarrow$(1); the implication
(1)$\Rightarrow$(2) is the special case $f=u^N$.

*Interlacing.* The images of consecutive monomials interlace,
$T_c(u^m)\ll T_c(u^{m+1})$ for $m<N$. Indeed $p_{m+1}'=(m+1)p_m$, and the logarithmic derivative
of the real-rooted $p_{m+1}$ has negative imaginary part in the upper half-plane, so
$p_{m+1}+i\,p_m$ is upper-half-plane stable. After folding and rotation,
$T_c(u^{m+1})(s^2)+s\,T_c(u^m)(s^2)$ is Hurwitz stable, and the converse odd/even
Hermite–Biehler theorem gives the interlacing. The monomial-chain upgrade for linear maps that
preserve PF polynomials then yields preservation of directed interlacing, and for a PF polynomial
$h$ the combination $T_c((u+a)h)=a\,T_ch+T_c(uh)$ of the interlacing pair $T_ch\ll T_c(uh)$ is
real-rooted for every real $a$.

*Finitely supported $c$.* If $c_k=0$ for $k>M$, then $p_N=h(D)\,u^N$ with the signed symbol
$h(w)=\sum_{k\le M}(-1)^kc_kw^{2k}=C(-w^2)$, where $C(t)=\sum_kc_kt^k$. By the Hermite–Poulain
theorem, if $h$ is real-rooted then every $p_N$ is real-rooted, so $T_c$ preserves PF
polynomials and directed interlacing in all degrees.

## Examples

* $c=(1,1,1,0,0,\dots)$, that is $T_cf=f+xf''+x^2f^{(4)}$. Here
  $T_c(u^4)=x^2(x^2+12x+24)$ is real-rooted, so $T_c$ preserves PF polynomials through degree
  four, but $T_c(u^5)=x^3(x^2+20x+120)$ is not real-rooted (the quadratic has discriminant
  $-80$), so preservation fails in degree five. Both statements are formalized.
* $c=(1,2,1,0,\dots)$, that is $T_cf=f+2xf''+x^2f^{(4)}$. The signed symbol is $(1-w^2)^2$, so
  $T_c$ preserves PF polynomials and directed interlacing in every degree. The images of
  $(u+1)^3$ and $(u+1)^4$ are $x^3+15x^2+15x+1$ and $x^4+28x^3+78x^2+28x+1$, and they interlace.
  These statements are formalized.

The scope is the finite-degree criterion with its interlacing and one-extra-root consequences and
the finitely supported symbol criterion. The classification of all-degree preservers (the
Pólya–Schur type description of $C(t)=\sum c_kt^k$), the sharp output intervals, the
characterization of source intervals containing positive points, and the coefficient-convolution
constructions are not formalized here.

## What is new

The proof is new, developed for RealRooted (issue #2380), and is of independent research
interest. The classical inputs are the Grace–Walsh–Szegő polarization of real-rooted symmetric
polynomials to real stable multiaffine polynomials, the Hermite–Biehler theorem and the
Hermite–Poulain theorem; the folding, the half-plane maps $z\mapsto z-r/z$, the lower-degree
caps and the monomial-chain interlacing argument are specific to this family of operators. This
extends the matching-type operators with coefficients $b^k/k!$.

## References

See [@BorceaBranden2009I], Proposition 2.4 (polarization) and Theorem 2.3
(Grace–Walsh–Szegő).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.EvenDerivative` modules
named in the metadata.
-/
