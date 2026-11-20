module

import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.BrandenLeite.AffineNegativePower
import RealRooted.BrandenLeite.ChainPolynomial.Algebra
import RealRooted.BrandenLeite.LogarithmicFactors
import RealRooted.BrandenLeite.PFFactorNumerators
import RealRooted.BrandenLeite.PFFactorRenewal
import RealRooted.BrandenLeite.PositivePowerFactors
import RealRooted.BrandenLeite.TotalNonnegativity
import RealRooted.BrandenLeite.WeightedDerivativeKernel
import RealRooted.BrandenLeite.ZeroConstant

/-!
# Chain polynomials of totally nonnegative matrices

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "branden-leite"
formalized = "2026-09-24"
references = [
  "BrandenLeite2024x",
]
authors = ["Brändén", "Saud Maia Leite"]
years = [2024]

[[definitions]]
name = "RealRooted.BrandenLeite.chainPolynomial"
module = "RealRooted.BrandenLeite.ChainPolynomial.Algebra"
label = "Chain polynomials of a lower-triangular matrix"

[[definitions]]
name = "RealRooted.BrandenLeite.affineNegativePowerCoeff"
module = "RealRooted.BrandenLeite.AffineNegativePower"
label = "Coefficients of $(Q(u) - tB(u))^{-κ}$ as polynomials in $t$"

[[definitions]]
name = "RealRooted.BrandenLeite.affineLogCoeff"
module = "RealRooted.BrandenLeite.AffineLogarithm"
label = "Coefficients of −log(Q(u) − tB(u)) as polynomials in t"

[[theorems]]
objects = ["Chain polynomials of totally nonnegative matrices"]
property = "interlacing"
name = "RealRooted.BrandenLeite.interl_chainPolynomial_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.TotalNonnegativity"
label = "Brändén–Saud Maia Leite: chain polynomials of a unitriangular TNN matrix interlace"
headline = true

[[theorems]]
name = "RealRooted.BrandenLeite.chainPolynomial_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.TotalNonnegativity"
label = "Chain polynomials of a unitriangular TNN matrix are real-rooted"

[[theorems]]
name = "RealRooted.BrandenLeite.roots_chainPolynomial_mem_Icc_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.TotalNonnegativity"
label = "Their zeros lie in [−1, 0]"

[[theorems]]
name = "RealRooted.BrandenLeite.compositionRows_isPFPolynomial_and_interl_of_zero"
module = "RealRooted.BrandenLeite.ZeroConstant"
label = "Rows of 1/(1 − x h(z)) with h PF and h(0) = 0 are PF polynomials and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.pfFactorNumerators_pf_and_interl"
module = "RealRooted.BrandenLeite.PFFactorNumerators"
label = "Rows of g/(1 − x(gh − g(0)h(0))) with g, h PF are PF polynomials and interlace"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.renewalPolynomial_isPF_of_isPFPolynomial"
module = "RealRooted.BrandenLeite.PFFactorRenewal"
label = "Rows of 1/(1 − xR(zxᵐ)) are PF polynomials when R is"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.BrandenLeite.affineNegativePowerCoeff_factor_properties"
module = "RealRooted.BrandenLeite.PositivePowerFactors"
label = "Rows of $(Q(u) - tB(u))^{-κ}$ have negative roots, degree $⌊n/r⌋$ and interlace"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.BrandenLeite.affineLogCoeff_factor_properties"
module = "RealRooted.BrandenLeite.LogarithmicFactors"
label = "Rows of −log(Q(u) − tB(u)) have negative roots, degree ⌊n/r⌋ and interlace"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.weightedDerivativeKernel_isTotallyNonneg"
module = "RealRooted.BrandenLeite.WeightedDerivativeKernel"
label = "Weighted derivative kernels of real-rooted nonnegative polynomials are TNN"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.BrandenLeite.det_weightedDerivativeKernel_affineNegativePowerCoeff"
module = "RealRooted.BrandenLeite.AffineNegativePower"
label = "n! qₙ(t) is the determinant of an affine pencil of weighted derivative kernels"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Chain polynomials of totally nonnegative matrices

Brändén and Saud Maia Leite proved that the chain polynomials of a lower-unitriangular totally
nonnegative matrix are real-rooted with zeros in $[-1,0]$, and that consecutive ones interlace.
We extend their theorem on $1/(Q(u)-tu^r)$ to all positive powers and the logarithm of
$Q(u)-tB(u)$.

## Results

A polynomial is a *Pólya frequency (PF) polynomial* if it has nonnegative coefficients and only
real roots. For a lower-triangular matrix $A$, the *chain polynomials* are $P_0=1$ and
$$
P_{n+1}(x)=x\sum_{k\le n}A(n+1,k)\,P_k(x).
$$

**Theorem (Brändén–Saud Maia Leite).** [@BrandenLeite2024x, Thm. 3.7] Let $A$ be lower
unitriangular and totally nonnegative. Then every $P_n$ is zero or real-rooted with all zeros in
$[-1,0]$, and $P_n\ll P_{n+1}$ for all $n$.

**Theorem (rows of power series).** Let $g,h$ be Pólya frequency sequences, and let $p_n$ be the
coefficient of $z^n$ in $g(z)/\bigl(1-x\,(g(z)h(z)-g(0)h(0))\bigr)$. Then every $p_n$ is a PF
polynomial and $p_n\ll p_{n+1}$. For $g=1$ this is [@BrandenLeite2024x, Thm. 4.4]; in
particular, if $h(0)=0$, the coefficients of $1/(1-x\,h(z))$ are PF polynomials in $x$ and
consecutive ones interlace. If $R$ is a PF polynomial and $m\ge1$, the coefficients of
$1/(1-xR(zx^m))$ are PF polynomials.

**Theorem (powers and logarithms).** Let
$$
Q(u)=\prod_{i=1}^{d}(1-\alpha_iu),\qquad B(u)=c\,u^r\prod_j(1+\beta_ju),
$$
with $d\ge1$, $\alpha_i>0$, $c>0$, $r\ge1$ and $\beta_j\ge0$, and let
$q_n(t)=[u^n]\,(Q(u)-tB(u))^{-\kappa}$ for real $\kappa>0$. Then $q_n$ has degree
$\lfloor n/r\rfloor$, positive coefficients up to that degree and only negative roots, and
$q_n\ll q_{n+1}$. For $n\ge1$ the same holds for
$\ell_n(t)=[u^n]\bigl(-\log(Q(u)-tB(u))\bigr)=\lim_{\kappa\to0^+}q_n/\kappa$.

For $\kappa=1$ and $B(u)=u^r$ this is the theorem of Brändén and Saud Maia Leite on
$1/(Q(u)-tu^r)$ [@BrandenLeite2024x, Thm. 4.5].

## Use

Brändén and Saud Maia Leite apply the first theorem to chain polynomials of posets, among them
subspace lattices and $r$-cubical posets. The second gives interlacing rows for rational generating
functions built from Pólya frequency series; see also [left production
matrices](rr:left-production-matrices).

## Proof

Whitney elimination writes a unitriangular totally nonnegative matrix as the path matrix of a
planar network, which gives a recurrence assembling each $P_n$ from lower rows by nonnegative
combinations that preserve interlacing. For powers and logarithms, the *weighted derivative
kernel* of a coefficient sequence $f$ has entries $\bigl(j+\kappa(i+1-j)\bigr)f_{i+1-j}$; it is
totally nonnegative when $f$ comes from a real-rooted polynomial with nonnegative coefficients,
and $n!\,q_n(t)$ is the determinant of an affine pencil of such kernels.

## References

[@BrandenLeite2024x, Thms. 3.7, 4.4 and 4.5]
<!-- /realrooted-catalog-content -->
-/

public section
