module

public import RealRooted.ASWKarlinKernel
import RealRooted.AissenSchoenbergWhitney
public import RealRooted.PFPolynomial
import RealRooted.PolyaFrequencyConvolution.Basic
public import RealRooted.NatCauchyConvolution

/-!
# Aissen--Schoenberg--Whitney challenge entry point

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
name = "RealRooted.Challenges.AissenSchoenbergWhitney.isPolyaFreqSeq_coeff_iff_isPFPolynomial"
label = "PF coefficients if and only if a PF polynomial"
headline = true
symcat = "aissenSchoenbergWhitney"

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.IsPolyaFreqSeq.splits_and_roots_nonpos"
label = "PF coefficients give real nonpositive zeros"

[[theorems]]
name = """RealRooted.Challenges.AissenSchoenbergWhitney.\
isPolyaFreqSeq_coeff_of_splits_of_roots_nonpos"""
label = "Real nonpositive zeros give PF coefficients"

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.IsPolyaFreqSeq.natCauchyConvolution"
label = "PF sequences are closed under convolution"

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
label = "PF coefficients if every positive perturbation p + μq splits"

[[theorems]]
name = "RealRooted.tendsto_aswSectorThreshold"
module = "RealRooted.ASWKarlinThreshold"
label = "The sector threshold tends to π as the order grows"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.aswKarlinMatrix_isTotallyNonnegRect"
module = "RealRooted.ASWKarlinMatrix"
label = "PF sequences have totally nonnegative Karlin window matrices"

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
name = """RealRooted.signVariations_aswKarlinSineVector_\
le_floor_div_pi_abs"""
module = "RealRooted.ASWKarlinSineBounds"
label = "A sampled sine vector has at most ⌊N|θ|/π⌋ sign variations"

[[theorems]]
name = """RealRooted.signVariations_aswKarlinSineVector_\
lt_of_lt_threshold"""
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
# Aissen–Schoenberg–Whitney

[@AissenSchoenbergWhitney1952]

A real sequence $(a_k)_{k \geq 0}$ is a Pólya frequency sequence if its
lower-triangular Toeplitz matrix, whose $(i, j)$ entry is $a_{i-j}$ for
$j \leq i$ and $0$ otherwise, is totally nonnegative. The coefficient sequence
of a real polynomial $p$ is a Pólya frequency sequence if and only if $p$ is a
PF polynomial: $p$ has nonnegative coefficients and is either zero or splits
over $\mathbb R$ with only nonpositive zeros. The two directions are also
listed separately.

**Theorem.** If $(a_k)$ and $(b_k)$ are Pólya frequency sequences, then so is
their Cauchy convolution $c_n = \sum_{k=0}^n a_k b_{n-k}$. The sequences may be
infinite. Equivalently, if the formal power series $F$ and $G$ have Pólya
frequency coefficient sequences, then so does $FG$.

**Karlin's sector estimate.** Let $p$ be a real polynomial of degree $d\geq1$
with $p(0)>0$ whose coefficient sequence is a Pólya frequency sequence. For
every integer $m\geq1$, each complex zero $z$ of $p$ satisfies
$$
|\arg z|\geq \frac{m\pi}{m+d-1}.
$$
Thus the zeros avoid the sector
$|\arg z|<m\pi/(m+d-1)$ around the positive real axis. The proof uses the
variation-diminishing property of the totally nonnegative coefficient-window
matrices of $p$.

## Perturbation criterion

If $p$ and $q$ have nonnegative coefficients and $p+\mu q$ splits over $\mathbb R$
for every $\mu>0$, then the coefficient sequence of $p$ is a Pólya frequency
sequence. Each $p+\mu q$ has nonnegative coefficients, so its coefficient sequence
is a Pólya frequency sequence by the reverse direction above, and the Toeplitz
minors of the sequence of $p$ are limits of those minors as $\mu\to0^+$.

## Structure of Karlin's argument

Let $p$ have degree $d\geq1$ and $p(0)>0$, with Pólya frequency coefficient
sequence $u$, and fix $m\geq1$. For $b\geq1$ blocks, Karlin's window matrix
$K_{b}$ has $bm$ rows and $b(d+m-1)+1$ columns. Its entries are entries of the
Toeplitz matrix of $u$: row $i$ is the Toeplitz row at position
$i+\lfloor i/m\rfloor(d-1)$, so each further block of $m$ rows is shifted by
$d-1$. The formalization follows these steps.

1. **Total nonnegativity.** $K_b$ is a transposed ordered submatrix of the Toeplitz
   matrix of $u$, hence totally nonnegative. Since $u_0>0$, it is also surjective
   as a map on column vectors, because a triangular pivot block has diagonal
   $u_0$.
2. **A kernel vector from a root.** If $z$ is a complex zero of $p$, the vector
   $(\operatorname{Im} z^j)_j$ lies in the kernel of $K_b$: the coefficients of $p$
   annihilate every shifted window of powers of $z$.
3. **Sign variations.** The signs of $\operatorname{Im} z^j$ agree with those of
   $\sin(j\theta)$ for $\theta=\arg z$, so the two vectors have the same number of
   sign variations. For a nonreal root, the variation count of a kernel vector of a
   totally nonnegative surjective matrix gives the lower bound
   $bm-1\leq \mathrm{var}+2$ for the sampled sine vector.
4. **Upper bound and contradiction.** A sampled sine vector with $N+1$ entries has at
   most $\lfloor N|\theta|/\pi\rfloor$ sign variations. With $N=b(d+m-1)$ this
   contradicts the lower bound for large $b$ unless
   $|\theta|\geq m\pi/(m+d-1)$; a real zero of $p$ lies on the negative axis and
   has $|\arg z|=\pi$.

The same file develops an alternative single-block route: when $|\theta|$ is below
the threshold the sampled sine vector has fewer than $m$ sign variations, and a
kernel vector with at least $m$ variations then gives the sector inequality. The
threshold $m\pi/(m+d-1)$ increases to $\pi$ as $m\to\infty$, so every zero $z$
of $p$ has $|\arg z|=\pi$, that is, lies on the negative real axis. This is how the
forward Aissen--Schoenberg--Whitney theorem follows from the sector estimate.

## Proof idea

The Toeplitz matrix of the convolution is the product of the two Toeplitz
matrices. Each finite truncation of this product is the product of the
truncations, because the matrices are lower triangular, and a product of
totally nonnegative matrices is totally nonnegative.

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

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace AissenSchoenbergWhitney

/-- Aissen--Schoenberg--Whitney: the coefficient sequence of `p` is a
Pólya-frequency sequence exactly when `p` is a PF polynomial. -/
theorem isPolyaFreqSeq_coeff_iff_isPFPolynomial {p : ℝ[X]} :
    IsPolyaFreqSeq p.coeff ↔ IsPFPolynomial p :=
  ⟨fun h => RealRooted.IsPFPolynomial.of_polyaFreqSeq h, fun h => h.to_sequence⟩

/-- Forward ASW theorem: PF coefficients imply real nonpositive roots. -/
theorem IsPolyaFreqSeq.splits_and_roots_nonpos {p : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) :
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0 :=
  RealRooted.aissenSchoenbergWhitneyForward hp

/-- Reverse ASW theorem: nonnegative coefficients and real nonpositive roots
imply PF coefficients. -/
theorem isPolyaFreqSeq_coeff_of_splits_of_roots_nonpos {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hsplits : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsPolyaFreqSeq p.coeff :=
  RealRooted.aissenSchoenbergWhitney_reverse hp hsplits hroots

/-- Pólya frequency sequences, finite or infinite, are closed under Cauchy
convolution. -/
theorem IsPolyaFreqSeq.natCauchyConvolution {a b : ℕ → ℝ} (ha : IsPolyaFreqSeq a)
    (hb : IsPolyaFreqSeq b) :
    IsPolyaFreqSeq (natCauchyConvolution a b) :=
  ha.natCauchyConvolution hb

end AissenSchoenbergWhitney
end Challenges
end RealRooted
