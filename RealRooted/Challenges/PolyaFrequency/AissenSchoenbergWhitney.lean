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

[[theorems]]
name = "RealRooted.Challenges.AissenSchoenbergWhitney.isPolyaFreqSeq_coeff_iff_isPFPolynomial"
label = "PF coefficients if and only if a PF polynomial"
headline = true

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
