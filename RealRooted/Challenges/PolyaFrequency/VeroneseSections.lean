module

import RealRooted.VeroneseRecognition.Affine
public import RealRooted.VeroneseMatrix

/-!
# Veronese sections of real-rooted polynomials and recognition of product parents

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "veronese-sections"
formalized = "2026-10-05"
authors = ["Athanasiadis", "Wagner"]
tags = []
references = [
  "AthanasiadisWagner2024x",
]

[[definitions]]
name = "RealRooted.veroneseSectionPolynomial"
module = "RealRooted.VeroneseSection"
label = "Veronese section"

[[definitions]]
name = "RealRooted.sequenceDelta"
module = "RealRooted.VeroneseRecognition"
label = "Normalized difference operator on a polynomial sequence"

[[definitions]]
name = "RealRooted.veroneseProductParent"
module = "RealRooted.VeroneseRecognition"
label = "Scalar product parent with seed H"

[[definitions]]
name = "RealRooted.veroneseProductRow"
module = "RealRooted.VeroneseRecognition"
label = "Residue row of a scalar product parent"

[[definitions]]
name = "RealRooted.reconstructedVeroneseParent"
module = "RealRooted.VeroneseRecognition"
label = "Seed reconstructed from the first r differences"

[[theorems]]
name = "RealRooted.veroneseSectionPolynomial_eq_zero_or_splits"
module = "RealRooted.VeroneseMatrix"
label = "Veronese sections preserve real-rootedness"
headline = true
symcat = "veroneseSectionsRealRooted"

[[theorems]]
name = "RealRooted.iterate_sequenceDelta_eq_X_mul_iff_existsUnique_seed"
module = "RealRooted.VeroneseRecognition"
label = "Δ^r P = X P holds exactly for rows of Veronese product parents"

[[theorems]]
name = "RealRooted.iterate_sequenceDelta_eq_affine_mul_iff_existsUnique_seed"
module = "RealRooted.VeroneseRecognition.Affine"
label = "Affine recognition of Veronese product parents"

[[theorems]]
name = "RealRooted.sequenceDelta_row_eq_zero_or_splits"
module = "RealRooted.VeroneseRecognition"
label = "Recognized rows are zero or real-rooted when the seed is nonnegative and splits"

[[theorems]]
name = "RealRooted.existsUnique_affineVeroneseProductRow_of_orderTwo_recurrence"
module = "RealRooted.VeroneseRecognition.Affine"
label = "Constant second-order recurrences have a unique affine Veronese parent"
-->

<!-- realrooted-catalog-content -->
# Veronese sections of real-rooted polynomials and recognition of product parents

Veronese sections of a real-rooted polynomial with nonnegative coefficients are real-rooted
or zero, and a recurrence of a prescribed shape forces a polynomial sequence to be a Veronese
section of a product of linear factors.

The $k$th $r$-Veronese section of $p=\sum_i p_i x^i$ is $\sum_{n\geq0}p_{k+rn}x^n$: it keeps
the coefficients whose indices are congruent to $k$ modulo $r$ and re-indexes them by
$n=(i-k)/r$.

## Results

**Theorem (Veronese sections).** Let $0 \leq k < r$. If a polynomial with nonnegative
coefficients splits over $\mathbb R$, then its $k$th $r$-Veronese section is zero or splits
over $\mathbb R$.

**Recognition of product parents.** Fix $r \geq 1$ and real sequences $a_n$, $b_n$ with every
$b_n \neq 0$. For a polynomial sequence $P = (P_n)$ put
$$
(\Delta P)_n = \frac{P_{n+1} - a_n P_n}{b_n},
$$
and for a polynomial $H$, the *seed*, let
$$
Q_n(H) = H(x)\prod_{i<n}\bigl(a_i + b_i x\bigr)
$$
be the *product parent*. Its $(r-1)$st $r$-Veronese section, as a sequence in $n$, is a row
family $R_n(H)$.

**Theorem (recognition).** $\Delta^r P = x P$ if and only if there is a unique polynomial $H$
with $R_n(H) = P_n$ for all $n$. The seed is reconstructed from the differences at index zero:
its $i$th $r$-Veronese section is $(\Delta^{r-1-i} P)_0$, for $0 \leq i < r$.

**Theorem (affine recognition).** For $\beta \neq 0$, $\Delta^r P = (\alpha + \beta x) P$ if and
only if there is a unique seed $H$ with $P_n(x) = R_n(H)(\alpha + \beta x)$ for all $n$.

**Theorem (real-rootedness of recognized rows).** Suppose $a_n \geq 0$, $b_n > 0$ and
$\Delta^r P = x P$, and the reconstructed seed has nonnegative coefficients and splits over
$\mathbb R$. Then every $P_n$ is zero or splits over $\mathbb R$. The same holds for
$\Delta^r P = (\alpha + \beta x) P$ with $\beta > 0$ and the reconstructed affine seed.

**Example (second-order recurrences).** Let $B \neq 0$ and suppose
$P_{n+2} = A P_{n+1} + (Bx + c) P_n$ for all $n$. Then there is a unique seed $H$ such that
$P_n$ is the odd Veronese section ($r = 2$) of $H\,(x + A/2)^n$, evaluated at
$c + A^2/4 + Bx$.

## Proof

The Veronese-section theorem uses the Pólya frequency characterization of real-rooted
polynomials with nonnegative coefficients and total nonnegativity of an associated matrix.

## References

The Veronese-section convention and its linear-factor recurrences are those of
[@AthanasiadisWagner2024x], where a stronger fully interlacing statement appears. See also the
[Veronese sections on symmetricfunctions.com](sf:veroneseSectionsRealRooted).
<!-- /realrooted-catalog-content -->

Human statement:
sf:veroneseSectionsRealRooted

Catalog reference: the standard PF/TNN proof via Aissen--Schoenberg--Whitney.

This module exposes the checked matrix-recursion proof that Veronese sections
of real-rooted polynomials with nonnegative coefficients are real-rooted or
zero.  The cyclic matrix construction remains in `RealRooted.VeroneseMatrix`;
the recognition theorems are cited from `RealRooted.VeroneseRecognition` and
`RealRooted.VeroneseRecognition.Affine`.
-/
