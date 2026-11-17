module

import RealRooted.ASWKarlinKernel
import RealRooted.AissenSchoenbergWhitney
import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.EdreiThoma.Converse
import RealRooted.EdreiThoma.Easy
import RealRooted.PFPolynomial
import RealRooted.PolyaFrequencyConvolution.Basic

/-!
# Pólya frequency sequences: Aissen–Schoenberg–Whitney and Edrei

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "aissen-schoenberg-whitney"
formalized = "2026-10-05"
references = [
  "AissenSchoenbergWhitney1952",
  "Edrei1953",
  "Karlin1968",
]
authors = ["Aissen", "Schoenberg", "Whitney", "Edrei", "Karlin"]
years = [1952, 1953, 1968]

[[definitions]]
name = "RealRooted.toeplitz"
module = "RealRooted.AissenSchoenbergWhitneyBase"
label = "Toeplitz matrix of a sequence"

[[definitions]]
name = "RealRooted.IsPolyaFreqSeq"
module = "RealRooted.AissenSchoenbergWhitneyBase"
label = "Pólya frequency sequence"

[[definitions]]
name = "RealRooted.EdreiThoma.canonicalProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Canonical product c X^m e^(γX) ∏(1 + αᵢX) / ∏(1 − βᵢX)"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_coeff_iff_isPFPolynomial"
module = "RealRooted.PFPolynomial"
label = "Aissen–Schoenberg–Whitney: PF coefficients iff nonnegative coefficients and real roots"
headline = true
symcat = "aissenSchoenbergWhitney"

[[theorems]]
name = "RealRooted.EdreiThoma.exists_canonicalProduct_representation"
module = "RealRooted.EdreiThoma.Converse"
label = "Edrei: a Pólya frequency sequence with a₀ = 1 has a canonical product representation"
symcat = "edreiThomaTheorem"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_canonicalProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Canonical products with nonnegative parameters are Pólya frequency series"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.natCauchyConvolution"
module = "RealRooted.PolyaFrequencyConvolution.Basic"
label = "Pólya frequency sequences are closed under convolution"

[[theorems]]
name = "RealRooted.EdreiThoma.IsPolyaFreqSeries.of_tendsto"
module = "RealRooted.EdreiThoma.Easy"
label = "Pólya frequency series are closed under coefficientwise limits"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.of_forall_pos_add_C_mul_splits"
module = "RealRooted.AissenSchoenbergWhitney"
label = "PF coefficients if p + μq is real-rooted for every μ > 0"

[[theorems]]
name = "RealRooted.aswKarlinSectorThreshold_le_abs_arg"
module = "RealRooted.ASWKarlinKernel"
label = "Karlin: zeros of a PF polynomial satisfy |arg z| ≥ mπ/(m+d−1) for every m ≥ 1"
-->

<!-- realrooted-catalog-content -->
# Pólya frequency sequences: Aissen–Schoenberg–Whitney and Edrei

A sequence is a Pólya frequency sequence if its Toeplitz matrix is totally nonnegative. Aissen,
Schoenberg and Whitney showed that the finite ones are exactly the coefficient sequences of
real-rooted polynomials with nonnegative coefficients, and Edrei classified all of them by their
generating functions.

## Results

A real sequence $(a_k)_{k\ge0}$ is a *Pólya frequency sequence* if the lower-triangular
Toeplitz matrix $(a_{i-j})_{i,j\ge0}$, with $a_{i-j}=0$ for $j>i$, is totally nonnegative. A
*PF polynomial* is a real polynomial with nonnegative coefficients that is zero or has only
real zeros.

**Theorem (Aissen–Schoenberg–Whitney).** [@AissenSchoenbergWhitney1952] The coefficient
sequence of a real polynomial $p$ is a Pólya frequency sequence if and only if $p$ is a PF
polynomial.

**Theorem (Edrei).** [@Edrei1953] Let $(a_n)$ be a Pólya frequency sequence with $a_0=1$.
There are $\gamma\ge0$ and $\alpha_i,\beta_i\ge0$ with $\sum_i(\alpha_i+\beta_i)<\infty$ such
that, for $z$ near $0$,
$$
\sum_{n\ge0}a_nz^n=e^{\gamma z}\,\frac{\prod_i(1+\alpha_iz)}{\prod_i(1-\beta_iz)}.
$$
Conversely, for $c,\gamma\ge0$, $m\in\mathbb N$ and such $\alpha,\beta$, the series
$cX^me^{\gamma X}\prod_i(1+\alpha_iX)/\prod_i(1-\beta_iX)$ has Pólya frequency coefficients
[@AissenSchoenbergWhitney1952].

**Theorem (closure).** Pólya frequency sequences are closed under Cauchy convolution, and
Pólya frequency series are closed under coefficientwise limits.

**Theorem (perturbation criterion).** If $p$ and $q$ have nonnegative coefficients and
$p+\mu q$ is real-rooted for every $\mu>0$, then the coefficients of $p$ form a Pólya frequency
sequence.

**Theorem (Karlin's sector estimate).** [@Karlin1968] Let $p$ be a polynomial of degree
$d\ge1$ with $p(0)>0$ whose coefficients form a Pólya frequency sequence. For every $m\ge1$,
each zero $z$ of $p$ satisfies $|\arg z|\ge m\pi/(m+d-1)$.

## Use

The equivalence turns real-rootedness of a polynomial with nonnegative coefficients into total
nonnegativity of its Toeplitz matrix, which can be proved with planar networks and the
[Lindström–Gessel–Viennot lemma](rr:lindstrom-gessel-viennot), as for
[left production matrices](rr:left-production-matrices). The $2\times2$ minors give
log-concavity of the coefficients.

## Proof

Letting $m\to\infty$ in Karlin's estimate puts every zero on the negative real axis, which is
the forward direction. Karlin's repeated coefficient-window matrices are totally nonnegative,
and the vector $(\operatorname{Im}z^j)_j$ of a complex zero lies in their kernel; counting the
sign variations of $(\sin j\arg z)_j$ gives the estimate. The Toeplitz matrix of a convolution
is the product of the two Toeplitz matrices, which gives the reverse direction from the linear
factors $1+\alpha X$. For Edrei's theorem the factors $1+\alpha X$, $1/(1-\beta X)$ and
$e^{\gamma X}$ are Pólya frequency, and the converse follows Edrei's determinant identities,
with Nevanlinna theory replaced by a growth argument based on Jensen's formula.

## References

[@AissenSchoenbergWhitney1952]; [@Edrei1953]; [@Karlin1968]. See also the
[Aissen–Schoenberg–Whitney theorem](sf:aissenSchoenbergWhitney) and the
[Edrei–Thoma theorem](sf:edreiThomaTheorem) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
