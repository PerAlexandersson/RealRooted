module

public import RealRooted.ASWKarlinKernel
public import RealRooted.ASWKarlinMatrix
public import RealRooted.ASWKarlinSineBounds
public import RealRooted.ASWKarlinThreshold
public import RealRooted.ASWKarlinVariation
public import RealRooted.ASWKarlinVectors
public import RealRooted.AissenSchoenbergWhitney
public import RealRooted.AissenSchoenbergWhitneyBase
public import RealRooted.NatCauchyConvolution
public import RealRooted.PFPolynomial
public import RealRooted.PolyaFrequencyConvolution.Basic

/-!
# Pólya frequency sequences and real-rooted polynomials (Aissen–Schoenberg–Whitney)

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "aissen-schoenberg-whitney"
formalized = "2026-10-05"
tags = []
references = [
  "AissenSchoenbergWhitney1952",
]
authors = ["Aissen", "Schoenberg", "Whitney"]
years = [1952]

[[definitions]]
name = "RealRooted.toeplitz"
module = "RealRooted.AissenSchoenbergWhitneyBase"
label = "Toeplitz matrix of a sequence"

[[definitions]]
name = "RealRooted.IsPolyaFreqSeq"
module = "RealRooted.AissenSchoenbergWhitneyBase"
label = "Pólya frequency sequence"

[[definitions]]
name = "RealRooted.natCauchyConvolution"
module = "RealRooted.NatCauchyConvolution"
label = "Cauchy convolution of sequences"

[[definitions]]
name = "RealRooted.aswSectorThreshold"
module = "RealRooted.ASWKarlinThreshold"
label = "Karlin's sector threshold mπ/(m+d−1)"

[[definitions]]
name = "RealRooted.aswKarlinMatrix"
module = "RealRooted.ASWKarlinMatrix"
label = "Karlin's repeated coefficient-window matrix"

[[definitions]]
name = "RealRooted.aswKarlinRootVector"
module = "RealRooted.ASWKarlinVectors"
label = "Imaginary parts of the powers of a complex root"

[[definitions]]
name = "RealRooted.aswKarlinSineVector"
module = "RealRooted.ASWKarlinVectors"
label = "Sampled sine vector of the argument of a root"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_coeff_iff_isPFPolynomial"
module = "RealRooted.PFPolynomial"
label = "Pólya frequency coefficients if and only if a PF polynomial"
headline = true
symcat = "aissenSchoenbergWhitney"

[[theorems]]
name = "RealRooted.aissenSchoenbergWhitneyForward"
module = "RealRooted.AissenSchoenbergWhitney"
label = "Pólya frequency coefficients give real nonpositive zeros"

[[theorems]]
name = "RealRooted.aissenSchoenbergWhitney_reverse"
module = "RealRooted.AissenSchoenbergWhitney"
label = "Nonnegative coefficients and real nonpositive zeros give PF coefficients"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.natCauchyConvolution"
module = "RealRooted.PolyaFrequencyConvolution.Basic"
label = "Pólya frequency sequences are closed under convolution"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.coeff_mul"
module = "RealRooted.PolyaFrequencyConvolution.Basic"
label = "Products of power series with PF coefficients have PF coefficients"

[[theorems]]
name = "RealRooted.aswKarlinSectorThreshold_le_abs_arg"
module = "RealRooted.ASWKarlinKernel"
label = "Karlin: PF zeros satisfy |arg z| ≥ mπ/(m+d−1) for every m ≥ 1"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.of_forall_pos_add_C_mul_splits"
module = "RealRooted.AissenSchoenbergWhitney"
label = "PF coefficients if p + μq splits for every μ > 0"

[[theorems]]
name = "RealRooted.tendsto_aswSectorThreshold"
module = "RealRooted.ASWKarlinThreshold"
label = "The sector threshold tends to π as the order grows"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.aswKarlinMatrix_isTotallyNonnegRect"
module = "RealRooted.ASWKarlinMatrix"
label = "Karlin window matrices of PF sequences are totally nonnegative"

[[theorems]]
name = "RealRooted.aswKarlinMatrix_mulVec_surjective"
module = "RealRooted.ASWKarlinMatrix"
label = "The Karlin window matrix is surjective when the constant coefficient is positive"

[[theorems]]
name = "RealRooted.aswKarlinMatrix_mulVec_rootVector"
module = "RealRooted.ASWKarlinKernel"
label = "The root vector of a complex zero lies in the kernel of the window matrix"

[[theorems]]
name = "RealRooted.signVariations_aswKarlinRootVector_eq_sine"
module = "RealRooted.ASWKarlinVectors"
label = "The root vector and the sampled sine vector have the same sign variations"

[[theorems]]
name = "RealRooted.signVariations_aswKarlinSineVector_le_floor_div_pi_abs"
module = "RealRooted.ASWKarlinSineBounds"
label = "A sampled sine vector has at most ⌊N|θ|/π⌋ sign variations"

[[theorems]]
name = "RealRooted.signVariations_aswKarlinSineVector_lt_of_lt_threshold"
module = "RealRooted.ASWKarlinSineBounds"
label = "Below the threshold the sine vector has fewer than m sign variations"

[[theorems]]
name = "RealRooted.aswKarlinRepeatedSineVariationLowerBound"
module = "RealRooted.ASWKarlinKernel"
label = "Karlin's repeated matrices force many sign variations on the sine vector"

[[theorems]]
name = "RealRooted.aswSectorThreshold_le_of_signVariation_bounds"
module = "RealRooted.ASWKarlinVariation"
label = "The sector inequality follows from the two sign-variation bounds"
-->

<!-- realrooted-catalog-content -->
# Pólya frequency sequences and real-rooted polynomials (Aissen–Schoenberg–Whitney)

The coefficients of a real polynomial form a Pólya frequency sequence if and only if
the polynomial has nonnegative coefficients and only real nonpositive zeros.

A real sequence $(a_k)_{k \geq 0}$ is a *Pólya frequency sequence* if its lower-triangular
Toeplitz matrix, with $(i, j)$ entry $a_{i-j}$ for $j \leq i$ and $0$ otherwise, is totally
nonnegative. A real polynomial $p$ is a *PF polynomial* if it has nonnegative coefficients and
either $p=0$ or $p$ splits over $\mathbb R$ with only nonpositive zeros.

## Results

**Theorem (Aissen–Schoenberg–Whitney).** The coefficient sequence of a real polynomial $p$ is a
Pólya frequency sequence if and only if $p$ is a PF polynomial. In particular, if the
coefficients of $p$ form a Pólya frequency sequence, then $p$ splits over $\mathbb R$ and all
its zeros are nonpositive; conversely, nonnegative coefficients, splitting and nonpositive
zeros give a Pólya frequency sequence.

**Theorem (convolution).** If $(a_k)$ and $(b_k)$ are Pólya frequency sequences, finite or
infinite, then so is their Cauchy convolution $c_n = \sum_{k=0}^n a_k b_{n-k}$. Equivalently,
if formal power series $F$ and $G$ have Pólya frequency coefficient sequences, so does $FG$.

**Theorem (perturbation criterion).** If $p$ and $q$ have nonnegative coefficients and
$p+\mu q$ splits over $\mathbb R$ for every $\mu>0$, then the coefficients of $p$ form a Pólya
frequency sequence.

**Theorem (Karlin's sector estimate).** Let $p$ be a real polynomial of degree $d\geq1$ with
$p(0)>0$ whose coefficients form a Pólya frequency sequence. For every integer $m\geq1$,
each complex zero $z$ of $p$ satisfies
$$
|\arg z|\geq \frac{m\pi}{m+d-1}.
$$
The threshold $m\pi/(m+d-1)$ tends to $\pi$ as $m\to\infty$, so every zero lies on the
negative real axis; this gives the forward direction of the equivalence.

## Proof

For the sector estimate, fix $m$ and $b\geq1$. Karlin's window matrix $K_b$ has $bm$ rows
and $b(d+m-1)+1$ columns; its row $i$ is the Toeplitz row at position
$i+\lfloor i/m\rfloor(d-1)$. It is totally nonnegative, and surjective when the constant
coefficient is positive. For a complex zero $z$, the vector $(\operatorname{Im} z^j)_j$ lies in
its kernel and has the same sign variations as the sampled sine vector $(\sin j\theta)_j$,
$\theta=\arg z$. For nonreal $z$ this gives $bm-1\leq\mathrm{var}+2$ for the sine vector,
while a sampled sine vector with $N+1$ entries has at most $\lfloor N|\theta|/\pi\rfloor$ sign
variations; letting $b\to\infty$ yields the bound. A single-block variant combines the same
kernel vector with the fact that below the threshold the sine vector has fewer than $m$ sign
variations.

For the convolution, the Toeplitz matrix of $c$ is the product of those of $a$ and $b$; each
finite truncation is the product of the truncations, since the matrices are lower triangular,
and a product of totally nonnegative matrices is totally nonnegative. For the perturbation
criterion, each $p+\mu q$ has Pólya frequency coefficients by the reverse direction, and the
Toeplitz minors of $p$ are the limits of those of $p+\mu q$ as $\mu\to0^+$.

## References

See [@AissenSchoenbergWhitney1952] and the
[Pólya-frequency overview on symmetricfunctions.com](sf:aissenSchoenbergWhitney).
<!-- /realrooted-catalog-content -->

Human statement:
sf:aissenSchoenbergWhitney

Original publication: M. Aissen, I. J. Schoenberg, and A. M. Whitney,
"On the generating functions of totally positive sequences. I",
J. Analyse Math. 2 (1952), 93--103.

This module exposes the proved Aissen--Schoenberg--Whitney equivalence, its
forward and reverse directions, and closure of Pólya frequency sequences under
convolution.  The Toeplitz/PF infrastructure remains in
`RealRooted.AissenSchoenbergWhitney`.
-/
