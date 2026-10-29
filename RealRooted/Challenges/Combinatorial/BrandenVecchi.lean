module

import RealRooted.BrandenVecchi.ChowInfinitePF
import RealRooted.BrandenVecchi.ChowSignedWords
import RealRooted.BrandenVecchi.ChowTotallyNonneg
import RealRooted.BrandenVecchi.ChowZeroPrefix
import RealRooted.BrandenVecchi.SmirnovSpecialization

/-!
# Brändén–Vecchi challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-vecchi"
formalized = "2026-09-12"
references = [
  "BrandenVecchi2025x",
]
authors = ["Brändén", "Vecchi"]
years = [2025]

[[definitions]]
name = "RealRooted.BrandenVecchi.chowDerangement"
module = "RealRooted.BrandenVecchi.Chow"
label = "Chow derangement polynomials"

[[definitions]]
name = "RealRooted.BrandenVecchi.chowPolynomial"
module = "RealRooted.BrandenVecchi.Chow"
label = "Chow polynomials of a lower-triangular matrix"

[[definitions]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Chow polynomials of a Pólya frequency symbol"

[[definitions]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow"
module = "RealRooted.BrandenVecchi.ChowSupersymmetric"
label = "Chow polynomials of a supersymmetric symbol"

[[definitions]]
name = "RealRooted.BrandenVecchi.scaledZeroPrefix"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "A sequence shifted by a zero prefix and scaled"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_nonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow polynomials have nonnegative coefficients"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.BrandenVecchi.chowDerangement_nonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow derangement polynomials have nonnegative coefficients"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowDerangement_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow derangement polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Consecutive Chow polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_chowDerangement_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "c_n interlaces d_n"

[[theorems]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow_isPFPolynomial"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Pólya frequency symbols give PF Chow polynomials"

[[theorems]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow_interl_succ"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Consecutive Chow polynomials of a Pólya frequency symbol interlace"

[[theorems]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow_eq_finiteSignedWordEnumerator"
module = "RealRooted.BrandenVecchi.ChowSignedWords"
label = "Chow polynomials as signed-word enumerators"

[[theorems]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow_replicate_one_nil_eq_smirnov"
module = "RealRooted.BrandenVecchi.SmirnovSpecialization"
label = "Specialization to Smirnov word polynomials"

[[theorems]]
name = "RealRooted.BrandenVecchi.three_zero_prefix_constant_isPolyaFreqSeq"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "The zero-prefix symbol is still a Pólya frequency sequence"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_three_zero_prefix_six_not_splits"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "Three leading zeros: the Chow polynomial c₆ = x² + x + 1 is not real-rooted"
-->

<!-- realrooted-catalog-content -->
# Chow polynomials of totally nonnegative matrices

For a lower-triangular matrix $A$, the Chow derangement polynomials satisfy
$d_0=1$ and
$$
d_n=x\,S_{n-1}\!\left(\sum_{k<n}A(n,k)d_k\right),\qquad
S_m(q)=\frac{x^mq(1/x)-q}{x-1}.
$$
The Chow polynomials are

$$c_n = \sum_{k \leq n} A(n,k)\, d_k.$$

For the incidence data of a poset, these generalize the Chow polynomials of
matroids and posets; see the
[Chow-polynomial definition on symmetricfunctions.com](sf:chowPolynomialDefinition).

**Theorem (Brändén–Vecchi).** [@BrandenVecchi2025x] If $A$ is lower unitriangular
and totally nonnegative, then $c_n$ and $d_n$ have nonnegative coefficients
and only real zeros. Moreover $c_n$ interlaces $c_{n+1}$, and $c_n$
interlaces $d_n$.

Further results:

- **Pólya frequency symbols:** for the Toeplitz matrix of an
  Aissen–Schoenberg–Whitney–Edrei symbol
  $e^{\gamma z} \prod_i (1 + \alpha_i z) \big/ \prod_i (1 - \beta_i z)$, the Chow
  polynomials are PF polynomials and interlace consecutively, provided
  $\gamma,\alpha_i,\beta_i\ge0$ and $\sum_i(\alpha_i+\beta_i)<\infty$.
- **Signed words:** for finite supersymmetric symbols, the Chow polynomial
  equals a signed-word enumerator by descents and collisions.
  It specializes to the Smirnov word polynomials.
- **Sharpness:** a zero prefix can destroy real-rootedness. Inserting three
  leading zeros into the all-ones sequence gives a Pólya frequency sequence
  whose Chow polynomial $c_6$ is not real-rooted.

## References

See [@BrandenVecchi2025x]. The resolution machinery comes from the
[Brändén–Saud Leite page](/RealRooted/theorems/branden-leite/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.BrandenVecchi`.
-/
