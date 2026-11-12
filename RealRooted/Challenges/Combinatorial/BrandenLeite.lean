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
# Brändén–Saud Leite challenge entry point

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
label = "Coefficients of arbitrary negative real powers"

[[definitions]]
name = "RealRooted.BrandenLeite.affineLogCoeff"
module = "RealRooted.BrandenLeite.AffineLogarithm"
label = "Coefficients of the negative formal logarithm"

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
label = "Valuation-one positive-power rows have simple, disjoint roots"

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
label = "Rows of 1 / (1 - x h(z)) are PF and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.twoKernelRows_pf_and_interl"
module = "RealRooted.BrandenLeite.TwoKernel"
label = "Rows of g / (1 - x g h) are PF and interlace"

[[theorems]]
name = "RealRooted.BrandenLeite.binomialCompositionRows_pf_and_interl"
module = "RealRooted.BrandenLeite.CompositionFamilies"
label = "Rows of 1 / (1 - x z (1+z)^d)"

[[theorems]]
name = "RealRooted.BrandenLeite.inversePowerCompositionRows_pf_and_interl"
module = "RealRooted.BrandenLeite.CompositionFamilies"
label = "Rows of 1 / (1 - x z / (1-z)^e)"

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
label = "These determinants are strictly positive for products of positive linear factors"

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
label = "Interlacing of consecutive rows for every valuation of B, by regularization"

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
label = "Delayed renewal rows interlace within each residue class modulo the delay"
-->

<!-- realrooted-catalog-content -->
# Totally nonnegative matrices and chain polynomials

A lower-triangular matrix $A$ defines chain polynomials by $P_0 = 1$ and

$$P_{n+1}(x) = x \sum_{k \leq n} A(n+1,k)\, P_k(x).$$

When $A$ counts weighted chains in a poset, $P_n$ enumerates the chains by
length.

**Theorem (Brändén–Saud Leite).** [@BrandenLeite2024x] If $A$ is lower unitriangular
and totally nonnegative, then every $P_n$ has nonnegative coefficients and
only real zeros in $[-1, 0]$, and $P_n$ interlaces $P_{n+1}$.

**Provenance.** The theorem above is from [@BrandenLeite2024x]. The extensions
on this page are new results whose proofs were developed for RealRooted and are
of independent research interest: rows for arbitrary real positive powers of
affine kernels and their logarithmic limits (negative roots, exact degree
$\lfloor n/r\rfloor$, positive coefficients and consecutive interlacing), numerators
of PF polynomial factors, and delayed renewal rows within each residue class.

The matrices covered are exactly the resolvable ones: a lower-unitriangular
matrix admits a resolution by nonnegative weights and monic polynomials if and
only if it is totally nonnegative. For a lower-triangular totally nonnegative
matrix with constant diagonal $\delta>0$, every $P_n$ is a Pólya frequency
polynomial: it has nonnegative coefficients and only real nonpositive zeros.
Moreover, it is the rescaling
$P_n^A(x)=P_n^{A/\delta}(\delta x)$ of the unitriangular case. See also the
[lower-unitriangular characterization on symmetricfunctions.com](sf:tnnLowerUnitriangularMatrix).

Applied to power-series kernels built from Pólya frequency sequences, the
theorem gives PF polynomials whose consecutive rows interlace, for two row
families:

- the rows of $1/\bigl(1 - x\,h(z)\bigr)$ when $h(0) = 0$;
- the rows of $g/(1-xgh)$ when $g,h$ are Pólya frequency sequences with
  $g(0)>0$ and $h(0)=0$.

In particular, the rows of $1/\bigl(1 - xz(1+z)^d\bigr)$ and of
$1/\bigl(1 - xz/(1-z)^e\bigr)$ are PF and interlace. These include OEIS A116088
($d = 2$), A116089 ($d = 3$) and A206294 ($e = 3$).

The resolution theorem has a network form. Every lower-unitriangular totally
nonnegative matrix is the path matrix of a triangular planar network whose
nonnegative weights come from Whitney elimination.

## Positive real powers and logarithmic rows

We also formalize the following extension. Let

$$Q(u)=\prod_{i=1}^{d}(1-\alpha_i u),\qquad
B(u)=cu^r\prod_j(1+\beta_j u),$$

where $d\ge1$, $\alpha_i>0$, $c>0$, $r\ge1$, and $\beta_j\ge0$.
For every real $\kappa>0$, the rows
$q_n(t)=[u^n](Q(u)-tB(u))^{-\kappa}$ have degree $\lfloor n/r\rfloor$,
strictly positive coefficients through that degree, and only strictly negative
real roots. Consecutive rows interlace with a fixed orientation, including
when their degrees agree. Repeated factors and constant rows are allowed.

The same conclusions hold for
$\ell_n(t)=[u^n](-\log(Q(u)-tB(u)))$ when $n\ge1$.
The proof uses the coefficient limit $q_n/\kappa\to\ell_n$ as
$\kappa\to0^+$, together with degree-bounded interlacing closure.

When $r=1$ and either $[u^2]Q>0$ or $[u^2]B>0$, the positive-power rows have
only simple roots, and consecutive rows have no common root. Together with the
interlacing above, this separates the roots of consecutive rows. The
formalization states the simple-root and no-common-root conclusions separately
from the weak interlacing; it does not prove a strict-interlacing predicate.
These extra conclusions are not asserted for logarithmic rows. If both quadratic
coefficients vanish, repeated roots can occur: for $Q=1-u$ and $B=u$, every $q_n$ is a
positive multiple of $(1+t)^n$.

## Weighted derivative kernels and the determinant formula

For a coefficient sequence $f$ and a parameter $\kappa$, the weighted derivative
kernel is the lower-Hessenberg matrix
$$
K_\kappa(f)_{ij}=\bigl(j+\kappa\,(i+1-j)\bigr)\,f_{i+1-j}\qquad(0\le j\le i+1).
$$
If $F$ is a real-rooted polynomial with nonnegative coefficients and $\kappa\ge0$,
then $K_\kappa(F)$ is totally nonnegative. The proof factors each finite
section as the product of a matrix built from the interlacing pair $(F',F)$ and a
sparse derivative contraction, both totally nonnegative.

The kernels compute the rows of negative powers. For $Q(0)=1$ and $B(0)=0$, the
row $q_n(t)=[u^n](Q(u)-tB(u))^{-\kappa}$ satisfies
$$
n!\,q_n(t)=\det\bigl(K_\kappa((-1)^kQ_k)+t\cdot\mathrm{checkerboard}\,K_\kappa(B_k)\bigr)_{n\times
n},
$$
an affine pencil of two kernels, and at $t=0$ the signed kernel has determinant
$n!\,[u^n]Q(u)^{-\kappa}$. For a product of positive linear factors $Q$ the signed
determinants are strictly positive. These identities, together with a finite
recurrence for the rows, are the algebraic input for the positive-power and
logarithmic results above. Under the same hypotheses the rows have exact degree
$\lfloor n/r\rfloor$ and positive coefficients up to that degree. When the
coefficient of $u$ in $B$ is positive, consecutive positive-power rows
interlace, and a regularization argument removes this positivity assumption.
The logarithmic rows are the limits $q_n/\kappa\to\ell_n$ as $\kappa\to0^+$, and
for $n\ge1$, $k\ge1$ their coefficients are
$[t^k]\ell_n=\frac1k\,[u^n]\bigl(B(u)^k\,Q(u)^{-k}\bigr)$. The rows of a rational
rod are the case $\kappa=1$, where $Q$ is the denominator of the rational
background and $B$ is the marked factor series.

## Numerators of two PF factors and delayed renewals

Let $g,h$ be coefficient sequences and let $p_n(x)$ be the coefficient of $z^n$ in
$$
\frac{g(z)}{1-x\bigl(g(z)h(z)-g(0)h(0)\bigr)} .
$$
If $g$ and $h$ are Pólya frequency sequences, then every $p_n$ is a PF polynomial
and $p_n$ interlaces $p_{n+1}$. When $g(0),h(0)>0$, the zeros of $p_n$ lie in
$[-1/(g(0)h(0)),0]$. These rows coincide with the regularized kernel rows of the
finite Toeplitz matrices of $g$ and $h$, to which the theorem on totally
nonnegative source borders applies.

For a PF polynomial $R$ and a delay $m\ge1$, the renewal polynomial
$\sum_j\bigl([z^j]R(z)^{n-mj}\bigr)x^j$ is the coefficient polynomial of
$1/(1-xR(zx^m))$. In the residue class $n=mq+r$ with $r<m$ it is the reciprocal
shift of the PF-factor numerator with $g=R^r$ and $h=xR^{m-r}$. Hence the
renewal rows are PF, and rows $q$ and $q+1$ of each residue class interlace
(and, for $R(0)>0$, in the strict-interlacing predicate of the library).

## Proof idea

Whitney elimination factors a totally nonnegative unitriangular matrix into
nonnegative resolution data. The subdivision operator $X^n \mapsto P_n$ sends each
row of the resolution to an interlacing sequence, and interlacing is preserved
under the nonnegative combinations that assemble the chain polynomials.

## Relation to SymCat

We formalize the infinite lower-unitriangular resolvability criterion. The
[site’s labelled characterization](sf:tnnLowerUnitriangularMatrix) is stated for
a finite weighted network.

## References

See [@BrandenLeite2024x].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.BrandenLeite`.
-/

public section
