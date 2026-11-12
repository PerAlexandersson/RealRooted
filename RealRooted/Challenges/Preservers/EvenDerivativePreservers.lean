module

import RealRooted.EvenDerivative.Basic
import RealRooted.EvenDerivative.Examples
import RealRooted.EvenDerivative.Interlacing
import RealRooted.EvenDerivative.Preserver
import RealRooted.EvenDerivative.Stability
import RealRooted.EvenDerivative.Symbol

/-!
# Even-derivative operators preserving Pólya frequency polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "even-derivative-preservers"
formalized = "2026-11-09"
authors = []
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
label = "Composition with −z²: T_c(uᴺ)(−z²) = (−1)ᴺ zᴺ p_N(z)"

[[theorems]]
name = "RealRooted.splits_evenDerivativeTest_of_le"
module = "RealRooted.EvenDerivative.Preserver"
label = "If p_N is real-rooted, then p_n is real-rooted for all n ≤ N"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator_X_pow_succ"
module = "RealRooted.EvenDerivative.Interlacing"
label = "Consecutive monomial images T_c(uᵐ) and T_c(uᵐ⁺¹) interlace"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Interlacing"
label = "T_c preserves directed interlacing of nonnegative-coefficient pairs through degree N"

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
# Even-derivative operators preserving Pólya frequency polynomials

The operator $f\mapsto\sum_kc_kx^kf^{(2k)}$ preserves PF polynomials of degree at most $N$ if and
only if a single explicit polynomial $p_N$ is real-rooted.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real, nonpositive roots. For $c=(c_k)_{k\ge0}$ with $c_0=1$ and $c_k\ge0$ let
$$
T_cf=\sum_{k\ge0}c_k\,x^kf^{(2k)},\qquad
p_N(z)=\sum_{k\le N/2}(-1)^kc_k\,(N)_{2k}\,z^{N-2k},
$$
where $(N)_j=N(N-1)\cdots(N-j+1)$. Then $T_c(u^N)=\sum_kc_k(N)_{2k}u^{N-k}$ and
$T_c(u^N)(-z^2)=(-1)^Nz^Np_N(z)$.

**Theorem (finite-degree criterion).** For every $N\ge0$ the following are equivalent.

1. $T_c$ maps every PF polynomial of degree at most $N$ to a PF polynomial.
2. $T_c(u^N)$ is real-rooted.
3. $p_N$ is real-rooted.

If $p_N$ is real-rooted, then $p_n$ is real-rooted for all $n\le N$.

**Theorem (consequences).** Suppose $p_N$ is real-rooted.

- $T_c(u^m)\ll T_c(u^{m+1})$ for $m+1\le N$.
- If $f\ll g$ have nonnegative coefficients and $\deg g\le N$, then $T_cf\ll T_cg$.
- If $h$ is PF with $\deg h<N$ and $a\in\mathbb R$, then $T_c\bigl((u+a)h\bigr)$ is real-rooted.
- If $r_1,\dots,r_n\ge0$ and $n\le N$, then $T_c\prod_{i\le n}(u+r_i)$ is real-rooted.

**Theorem (finitely supported coefficients).** Suppose $c_k=0$ for $k>M$ and the signed symbol
$h(w)=\sum_{k\le M}(-1)^kc_kw^{2k}$ is real-rooted. Then $p_N$ is real-rooted for every $N$, and
$p_N=h(D)\,u^N$ with $D=d/du$. Consequently $T_c$ preserves PF polynomials of every degree.

**Theorem (polarization).** If $p_n$ is real-rooted, its multiaffine symmetric polarization is
real stable.

**Examples.**

- For $c=(1,1,1,0,0,\dots)$, that is $T_cf=f+xf''+x^2f^{(4)}$, we have
  $T_c(u^4)=x^2(x^2+12x+24)$ and $T_c(u^5)=x^3(x^2+20x+120)$. The operator preserves PF
  polynomials of degree at most four, and $T_c(u^5)$ is not real-rooted.
- For $c=(1,2,1,0,\dots)$, that is $T_cf=f+2xf''+x^2f^{(4)}$, the operator preserves PF
  polynomials of every degree. The polynomials $x^3+15x^2+15x+1$ and
  $x^4+28x^3+78x^2+28x+1$, the images of $(u+1)^3$ and $(u+1)^4$, interlace.

## Proof

Composing $T_c(u^N)$ with $u=-z^2$ gives $(-1)^Nz^Np_N(z)$, which relates (2) and (3). The
implication from (3) to (1) uses the Grace--Walsh--Szegő polarization of $p_n$
[@BorceaBranden2009I, Prop. 2.4].

## References

[@BorceaBranden2009I, Thm. 2.3] is the Grace--Walsh--Szegő theorem.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.EvenDerivative` modules
named in the metadata.
-/
