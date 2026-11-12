module

public import RealRooted.BrandenLeite.PositivePowerFactors
public import RealRooted.BrandenLeite.LogarithmicFactors
public import RealRooted.BrandenLeite.PositivePowerStrictRows
public import RealRooted.BrandenLeite.CompositionFamilies
public import RealRooted.BrandenLeite.ConstantDiagonal
public import RealRooted.BrandenLeite.NetworkWhitney
public import RealRooted.BrandenLeite.ResolvableTotallyNonneg
public import RealRooted.BrandenLeite.Theorem37
public import RealRooted.BrandenLeite.TwoKernel
public import RealRooted.BrandenLeite.WeightedShiftTiling
public import RealRooted.BrandenLeite.ZeroConstant
import RealRooted.BrandenLeite.PFFactorNumerators
import RealRooted.BrandenLeite.PFFactorRenewal
import RealRooted.BrandenLeite.WeightedDerivativeKernel
import RealRooted.BrandenLeite.PositivePowerRow
import RealRooted.BrandenLeite.PositivePowerInterlacing
import RealRooted.BrandenLeite.PositivePowerRegularization
import RealRooted.BrandenLeite.AffineNegativePowerDegree
import RealRooted.BrandenLeite.LogarithmicInterlacing
import RealRooted.BrandenLeite.LogarithmDegree
import RealRooted.BrandenLeite.NegativePowerDeterminant
import RealRooted.BrandenLeite.NegativePowerDetPositive
import RealRooted.BrandenLeite.AffineNegativePowerRecurrence
import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.BrandenLeite.LogarithmicCoefficients
import RealRooted.BrandenLeite.RationalRodCanonical

/-!
# Real-rooted chain polynomials of totally nonnegative matrices

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-leite"
formalized = "2026-09-24"
tags = ["realrooted-original"]
references = [
  "BrandenLeite2024x",
]
authors = ["Brändén", "Saud Maia Leite"]
years = [2026]

[[definitions]]
name = "RealRooted.BrandenLeite.affineNegativePowerCoeff"
module = "RealRooted.BrandenLeite.AffineNegativePower"
label = "Coefficients of (Q(u) - tB(u))^(-κ) as polynomials in t"

[[definitions]]
name = "RealRooted.BrandenLeite.affineLogCoeff"
module = "RealRooted.BrandenLeite.AffineLogarithm"
label = "Coefficients of -log(Q(u) - tB(u)) as polynomials in t"

[[theorems]]
name = "RealRooted.BrandenLeite.affineNegativePowerCoeff_factor_properties"
module = "RealRooted.BrandenLeite.PositivePowerFactors"
label = "Positive real powers: negative roots, exact degree and consecutive interlacing"

[[theorems]]
name = "RealRooted.BrandenLeite.affineLogCoeff_factor_properties"
module = "RealRooted.BrandenLeite.LogarithmicFactors"
label = "Logarithmic rows: negative roots, exact degree and consecutive interlacing"

[[theorems]]
name = "RealRooted.BrandenLeite.affineNegativePowerCoeff_factor_simple_and_disjoint"
module = "RealRooted.BrandenLeite.PositivePowerStrictRows"
label = "For r = 1 and positive [u²]Q or [u²]B: simple roots, no common roots in consecutive rows"

[[definitions]]
name = "RealRooted.BrandenLeite.chainPolynomial"
module = "RealRooted.BrandenLeite.ChainPolynomial.Algebra"
label = "Chain polynomials"

[[definitions]]
name = "RealRooted.BrandenLeite.IsResolvable"
module = "RealRooted.BrandenLeite.Resolvable"
label = "Resolvable matrix"

[[definitions]]
name = "RealRooted.BrandenLeite.compositionRow"
module = "RealRooted.BrandenLeite.CompositionRow"
label = "Rows of 1 / (1 - x h(z))"

[[definitions]]
name = "RealRooted.BrandenLeite.twoKernelRow"
module = "RealRooted.BrandenLeite.TwoKernelAlgebra"
label = "Rows of g / (1 - x g h)"

[[theorems]]
name = "RealRooted.BrandenLeite.interl_chainPolynomial_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"
label = "Consecutive chain polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.BrandenLeite.chainPolynomial_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"
label = "Chain polynomials are real-rooted"

[[theorems]]
name = "RealRooted.BrandenLeite.roots_chainPolynomial_mem_Icc_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"
label = "Zeros of chain polynomials lie in [-1, 0]"

[[theorems]]
name = "RealRooted.BrandenLeite.chainPolynomial_hasNonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"
label = "Chain polynomials have nonnegative coefficients"

[[theorems]]
name = "RealRooted.BrandenLeite.isResolvable_iff_lowerUnitriangular_and_isTotallyNonneg"
module = "RealRooted.BrandenLeite.ResolvableTotallyNonneg"
label = "Resolvable if and only if totally nonnegative"

[[theorems]]
name = "RealRooted.BrandenLeite.chainPolynomial_isPFPolynomial_of_pos_constantDiagonal"
module = "RealRooted.BrandenLeite.ConstantDiagonal"
label = "Chain polynomials with positive constant diagonal are PF"

[[theorems]]
name = "RealRooted.BrandenLeite.compositionRows_isPFPolynomial_and_interl_of_zero"
module = "RealRooted.BrandenLeite.ZeroConstant"
label = "Rows of 1 / (1 - x h(z)) with h(0) = 0 are PF and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.twoKernelRows_pf_and_interl"
module = "RealRooted.BrandenLeite.TwoKernel"
label = "Rows of g / (1 - x g h) are PF and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.binomialCompositionRows_pf_and_interl"
module = "RealRooted.BrandenLeite.CompositionFamilies"
label = "Rows of 1 / (1 - x z (1+z)^d) are PF and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.inversePowerCompositionRows_pf_and_interl"
module = "RealRooted.BrandenLeite.CompositionFamilies"
label = "Rows of 1 / (1 - x z / (1-z)^e) are PF and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.networkMatrix_resolutionLambda_eq"
module = "RealRooted.BrandenLeite.NetworkWhitney"
label = "Every lower-unitriangular TNN matrix is a Whitney-elimination network path matrix"

[[theorems]]
name = "RealRooted.BrandenLeite.weightedShiftTilingRow_separated_isPFPolynomial"
module = "RealRooted.BrandenLeite.WeightedShiftTiling"
label = "Tiling polynomials of weighted lower shifts are PF"

[[definitions]]
name = "RealRooted.BrandenLeite.weightedDerivativeKernel"
module = "RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic"
label = "The weighted derivative kernel of a coefficient sequence"

[[definitions]]
name = "RealRooted.BrandenLeite.pfFactorNumerator"
module = "RealRooted.BrandenLeite.PFFactorNumerators"
label = "Numerators of g / (1 - x (g h - g(0) h(0)))"

[[theorems]]
name = "RealRooted.weightedDerivativeKernel_isTotallyNonneg"
module = "RealRooted.BrandenLeite.WeightedDerivativeKernel"
label = "Weighted derivative kernels of real-rooted nonnegative polynomials are TNN"

[[theorems]]
name = "RealRooted.BrandenLeite.det_weightedDerivativeKernel_affineNegativePowerCoeff"
module = "RealRooted.BrandenLeite.AffineNegativePower"
label = "Rows of a negative power are determinants of an affine pencil of weighted kernels"

[[theorems]]
name = "RealRooted.BrandenLeite.det_weightedDerivativeKernel_subst_binomialSeries_neg"
module = "RealRooted.BrandenLeite.NegativePowerDeterminant"
label = "Determinants of signed weighted kernels are coefficients of negative powers"

[[theorems]]
name = "RealRooted.BrandenLeite.det_weightedDerivativeKernel_signed_prod_linear_pos"
module = "RealRooted.BrandenLeite.NegativePowerDetPositive"
label = "Signed kernel determinants are positive for products of factors 1 - αu, α > 0"

[[theorems]]
name = "RealRooted.BrandenLeite.coeff_affineNegativePowerCoeff_recurrence"
module = "RealRooted.BrandenLeite.AffineNegativePowerRecurrence"
label = "A finite coefficient recurrence for the rows of a negative power"

[[theorems]]
name = "RealRooted.BrandenLeite.natDegree_affineNegativePowerCoeff_and_coeff_pos"
module = "RealRooted.BrandenLeite.AffineNegativePowerDegree"
label = "Rows have degree ⌊n/r⌋ and positive coefficients up to that degree"

[[theorems]]
name = "RealRooted.BrandenLeite.interlaces_affineNegativePowerCoeff_succ"
module = "RealRooted.BrandenLeite.PositivePowerInterlacing"
label = "Consecutive negative-power rows interlace when the linear coefficient of B is positive"

[[theorems]]
name = "RealRooted.BrandenLeite.interl_affineNegativePowerCoeff_prod_linear_succ"
module = "RealRooted.BrandenLeite.PositivePowerRegularization"
label = "Consecutive rows interlace for every nonzero split numerator B with B(0) = 0"

[[theorems]]
name = "RealRooted.BrandenLeite.isPFPolynomial_affineNegativePowerCoeff_prod_linear"
module = "RealRooted.BrandenLeite.PositivePowerRow"
label = "Rows with product-of-linear-factor denominators are PF polynomials"

[[theorems]]
name = "RealRooted.BrandenLeite.tendsto_coeff_affineNegativePowerCoeff_div"
module = "RealRooted.BrandenLeite.AffineLogarithm"
label = "The logarithmic row is the limit of q_n / κ as κ tends to 0 from above"

[[theorems]]
name = "RealRooted.BrandenLeite.coeff_affineLogCoeff_of_ne_zero"
module = "RealRooted.BrandenLeite.LogarithmicCoefficients"
label = "Explicit parameter coefficients of the logarithmic rows"

[[theorems]]
name = "RealRooted.BrandenLeite.natDegree_affineLogCoeff_and_coeff_pos"
module = "RealRooted.BrandenLeite.LogarithmDegree"
label = "Logarithmic rows have exact degree ⌊n/r⌋ and positive coefficients"

[[theorems]]
name = "RealRooted.BrandenLeite.affineLogCoeff_factor_pf_and_interl"
module = "RealRooted.BrandenLeite.LogarithmicInterlacing"
label = "Logarithmic rows are PF polynomials and consecutive rows interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.rationalRodRow_eq_affineNegativePowerCoeff"
module = "RealRooted.BrandenLeite.RationalRodCanonical"
label = "Rational rod rows are the exponent-one negative-power rows"

[[theorems]]
name = "RealRooted.BrandenLeite.pfFactorNumerators_pf_and_interl"
module = "RealRooted.BrandenLeite.PFFactorNumerators"
label = "Numerators of two PF factors are PF polynomials and consecutive rows interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.roots_pfFactorNumerator_mem_Icc_of_pos"
module = "RealRooted.BrandenLeite.PFFactorNumerators"
label = "With g(0), h(0) > 0 the zeros lie in [-1/(g(0) h(0)), 0]"

[[theorems]]
name = "RealRooted.BrandenLeite.pfFactorNumerator_eq_regularizedKernelRow_fin"
module = "RealRooted.BrandenLeite.PFFactorNumerators"
label = "PF-factor numerators are the regularized kernel rows of the finite Toeplitz factors"

[[theorems]]
name = "RealRooted.BrandenLeite.renewalPolynomial_eq_reciprocalShift_pfFactorNumerator"
module = "RealRooted.BrandenLeite.PFFactorRenewal"
label = "Delayed renewal rows are reciprocal shifts of PF-factor numerators in each residue class"

[[theorems]]
name = "RealRooted.renewalPolynomial_isPF_of_isPFPolynomial"
module = "RealRooted.BrandenLeite.PFFactorRenewal"
label = "Delayed renewal rows of a PF polynomial are PF"

[[theorems]]
name = "RealRooted.strictInterl_renewalPolynomial_residue_succ"
module = "RealRooted.BrandenLeite.PFFactorRenewal"
label = "For R(0) > 0, consecutive renewal rows in a residue class are nonzero and interlace"
-->

<!-- realrooted-catalog-content -->
# Real-rooted chain polynomials of totally nonnegative matrices

Chain polynomials of a lower-unitriangular totally nonnegative matrix are real-rooted with zeros
in $[-1,0]$, and consecutive ones interlace; the same holds for several families of rows of
power series.

## Results

We write $f\ll g$ if $f$ interlaces $g$: both are real-rooted, $\deg g-\deg f\in\{0,1\}$, and
their roots alternate weakly, the largest root belonging to $g$. Common roots are allowed unless
stated. We also write $f\ll g$ when $f$ or $g$ is zero. A polynomial is a *Pólya frequency (PF)
polynomial* if it has nonnegative coefficients and only real nonpositive roots.

For a lower-triangular matrix $A$, the *chain polynomials* are $P_0=1$ and
$$
P_{n+1}(x)=x\sum_{k\le n}A(n+1,k)\,P_k(x).
$$

**Theorem (Brändén–Saud Leite).** Let $A$ be lower unitriangular and totally nonnegative.
Then every $P_n$ has nonnegative coefficients, and is zero or has only real roots, all in
$[-1,0]$. Moreover $P_n\ll P_{n+1}$ for all $n$ [@BrandenLeite2024x].

**Proposition (constant diagonal).** Let $A$ be lower triangular and totally nonnegative with
$A(n,n)=\delta>0$ for all $n$. Then $P_n$ is a PF polynomial and $P_n\ll P_{n+1}$. Indeed
$P^A_n(x)=P^{A/\delta}_n(\delta x)$, so this reduces to the unitriangular case.

**Proposition (resolvable matrices).** A real lower-triangular matrix $A$ admits a resolution,
that is, nonnegative weights $\lambda_{n,k}$ and monic polynomials $p_{n,k}$ with
$p_{n,0}=P_n$, $p_{n,n}=x^n$, $x^k\mid p_{n,k}$ and
$p_{n+1,k}=p_{n+1,k+1}+\lambda_{n,k}\,p_{n,k}$ for $k\le n$, if and only if $A$ is lower
unitriangular and totally nonnegative. Then $A$ is the path matrix of a triangular network whose
weights are the Whitney elimination weights. See also the
[lower-unitriangular characterization on symmetricfunctions.com](sf:tnnLowerUnitriangularMatrix).

### Rows of power series

Let $g,h$ be Pólya frequency sequences, that is, sequences whose Toeplitz matrices are totally
nonnegative. Write $[z^n]F$ for the coefficient of $z^n$ in a power series $F$.

- If $h(0)=0$, the polynomials $\sum_k\bigl([z^n]\,h(z)^k\bigr)x^k$, the coefficients of
  $1/(1-x\,h(z))$, are PF polynomials in $x$, and consecutive ones satisfy $\ll$.
- If $g(0)>0$ and $h(0)=0$, the polynomials $\sum_k\bigl([z^n]\,g^{k+1}h^k\bigr)x^k$, the
  coefficients of $g/(1-x\,g\,h)$, are PF polynomials and consecutive ones satisfy $\ll$.
- For every $d,e\ge0$, the first statement applies to $h=z(1+z)^d$ and to $h=z/(1-z)^e$.
- For arbitrary $g,h$, let $p_n$ be the coefficient of $z^n$ in
  $g(z)/\bigl(1-x\,(g(z)h(z)-g(0)h(0))\bigr)$. Then every $p_n$ is a PF polynomial and
  $p_n\ll p_{n+1}$. If $g(0),h(0)>0$, the roots of $p_n$ lie in $[-1/(g(0)h(0)),0]$. The $p_n$
  are the rows of the regularized kernel of the finite Toeplitz matrices of $g$ and $h$.
- For a PF polynomial $R$ and $m\ge1$, let
  $\rho_n=\sum_j\bigl([z^j]R(z)^{\max(n-mj,0)}\bigr)x^j$ be the coefficient polynomials of
  $1/(1-xR(zx^m))$. Every $\rho_n$ is a PF polynomial. For $n=mq+r$ with $0\le r<m$, $\rho_n$ is the
  reciprocal $x^q p_q(1/x)$ of the numerator $p_q$ for $g=R^r$ and $h=zR^{m-r}$, hence
  $\rho_{mq+r}\ll\rho_{m(q+1)+r}$. If $R(0)>0$, all $\rho_n$ are nonzero.
- For nonnegative weights $b_n$, $w_n$, nonnegative scalars $a_1,\dots,a_s$ and $r\ge1$, let $G$
  be the sum $I+B+\dots+B^N$ for the lower shift $B$ with weights $b_n$, and let
  $K=\prod_j(I+B_j)\,S^r$, where $B_j$ is the lower shift with weights $a_jw_n$ and $S$ is the
  unweighted lower shift. Row $i$ of $\sum_q (G(KG)^q)_{i,0}\,x^q$ is a PF polynomial.

### Powers and logarithms of an affine pencil

Let
$$
Q(u)=\prod_{i=1}^{d}(1-\alpha_iu),\qquad B(u)=c\,u^r\prod_j(1+\beta_ju),
$$
with $d\ge1$, $\alpha_i>0$, $c>0$, $r\ge1$ and $\beta_j\ge0$, and put
$q_n(t)=[u^n]\,(Q(u)-tB(u))^{-\kappa}$ for real $\kappa>0$. Then $q_n$ is nonzero with degree
$\lfloor n/r\rfloor$, has positive coefficients up to that degree and only negative roots, and
$q_n\ll q_{n+1}$. Repeated factors and constant rows are allowed.

For $n\ge1$ the same holds for $\ell_n(t)=[u^n]\bigl(-\log(Q(u)-tB(u))\bigr)$, which is the limit
of $q_n/\kappa$ as $\kappa\to0^+$; here $\ell_n$ is a PF polynomial. For $k\ge1$,
$$
[t^k]\,\ell_n=\frac1k\,[u^n]\bigl(B(u)^k\,Q(u)^{-k}\bigr).
$$

For $B$ any nonzero real-rooted polynomial with nonnegative coefficients and $B(0)=0$, the rows
$q_n$ are PF polynomials and $q_n\ll q_{n+1}$.

If $r=1$, and $[u^2]Q>0$ or $[u^2]B>0$, then every $q_n$ has only simple roots and $q_n$,
$q_{n+1}$ have no common root, so the roots of consecutive rows interlace strictly. If both
coefficients vanish, roots may repeat: for $Q=1-u$ and $B=u$, every $q_n$ is a positive multiple
of $(1+t)^n$.

### Weighted derivative kernels

For a sequence $f$ and a parameter $\kappa$, the *weighted derivative kernel* is
$$
K_\kappa(f)_{ij}=\bigl(j+\kappa\,(i+1-j)\bigr)\,f_{i+1-j}\qquad(0\le j\le i+1),
$$
and zero for $j>i+1$. If $F$ is real-rooted with nonnegative coefficients and $\kappa\ge0$, then
$K_\kappa(F)$, built from the coefficients of $F$, is totally nonnegative.

Let $Q(0)=1$, $B(0)=0$ and $q_n(t)=[u^n]\,(Q(u)-tB(u))^{-\kappa}$. Then
$$
n!\,q_n(t)=\det\Bigl(K_\kappa\bigl((-1)^kQ_k\bigr)+t\,\mathrm{checkerboard}\,K_\kappa(B_k)
\Bigr)_{n\times n},
$$
where $Q_k,B_k$ are the coefficients of $u^k$ and $\mathrm{checkerboard}$ multiplies the
$(i,j)$ entry by $(-1)^{i+j}$. For $H(0)=1$, the determinant of $K_\kappa((-1)^kH_k)$ is $n!$
times the coefficient of $u^n$ in $H^{-\kappa}$. If $Q$ is a nonempty product of factors
$1-\alpha_iu$ with $\alpha_i>0$ and $\kappa>0$, these determinants are positive. The coefficients
of $q_n$ satisfy a finite recurrence in $n$ with coefficients from $Q$ and $B$.

The case $\kappa=1$ gives the coefficients of the rational function $1/(Q(u)-tB(u))$.

## Use

The rows of $1/(1-xz(1+z)^d)$ and $1/(1-xz/(1-z)^e)$ include OEIS A116088 ($d=2$), A116089
($d=3$) and A206294 ($e=3$).

## Proof

Whitney elimination produces the resolution of a totally nonnegative unitriangular matrix. The
recurrence of the resolution assembles each $P_n$ from lower rows by nonnegative combinations,
which preserve interlacing.

## References

- [@BrandenLeite2024x]
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.BrandenLeite`.
-/

public section
