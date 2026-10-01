import RealRooted.BrandenVecchi.ChowFullProjective
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
name = "RealRooted.BrandenVecchi.aswEdreiChow"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Chow polynomials of a Pólya frequency symbol"

[[definitions]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow"
module = "RealRooted.BrandenVecchi.ChowSupersymmetric"
label = "Chow polynomials of a supersymmetric symbol"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_nonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow polynomials have nonnegative coefficients"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Chow polynomials are real-rooted"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Consecutive Chow polynomials interlace"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_chowDerangement_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "c_n interlaces d_n"

[[theorems]]
name = "RealRooted.BrandenVecchi.aswEdreiFullProjectiveChow_theorem"
module = "RealRooted.BrandenVecchi.ChowFullProjective"
label = "Pólya frequency symbols give PF Chow polynomials"

[[theorems]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow_eq_finiteSignedWordEnumerator"
module = "RealRooted.BrandenVecchi.ChowSignedWords"
label = "Chow polynomials as signed-word enumerators"

[[theorems]]
name = "RealRooted.BrandenVecchi.finiteSupersymmetricChow_replicate_one_nil_eq_smirnov"
module = "RealRooted.BrandenVecchi.SmirnovSpecialization"
label = "Specialization to Smirnov word polynomials"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_three_zero_prefix_six_not_splits"
module = "RealRooted.BrandenVecchi.ChowZeroPrefix"
label = "A zero prefix of length three breaks real-rootedness"
-->

<!-- realrooted-catalog-content -->
# Chow polynomials of totally nonnegative matrices

For a lower-triangular matrix $A$, the Chow derangement polynomials $d_n$
satisfy a triangular recurrence driven by the rows of $A$. The Chow
polynomials are

$$c_n = \sum_{k \leq n} A(n,k)\, d_k.$$

For the incidence data of a poset, these generalize the Chow polynomials of
matroids and posets.

**Theorem (Brändén–Vecchi, Theorem 4.18).** If $A$ is lower unitriangular
and totally nonnegative, then $c_n$ and $d_n$ have nonnegative coefficients
and only real zeros. Moreover $c_n$ interlaces $c_{n+1}$, and $c_n$
interlaces $d_n$.

Further results:

- **Pólya frequency symbols:** for the Toeplitz matrix of an Aissen–Schoenberg–Whitney–Edrei symbol
  $e^{\gamma z} \prod_i (1 + \alpha_i z) \big/ \prod_i (1 - \beta_i z)$ (Theorem 8.4), the Chow
  polynomials are PF polynomials and interlace consecutively. This also holds in the full projective
  form, with an outer scalar, a zero prefix and a shift.
- **Signed words:** for finite supersymmetric symbols, the Chow polynomial
  equals a signed-word enumerator by descents and collisions (Theorem 8.11).
  It specializes to the Smirnov word polynomials.
- **Sharpness:** a zero prefix of length three can destroy real-rootedness,
  even though the symbol remains a Pólya frequency sequence.

## References

P. Brändén and L. Vecchi, “Chow polynomials of totally nonnegative matrices
and posets” (2025).
The resolution machinery comes from the
[Brändén–Saud Leite page](/RealRooted/theorems/branden-leite/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.BrandenVecchi`.
-/
