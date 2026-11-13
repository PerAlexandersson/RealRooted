module

import RealRooted.VeroneseRecognition.Affine
import RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese
public import RealRooted.VeroneseMatrix

/-!
# Veronese sections

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
name = "Polynomial.veroneseNorm"
module = "RealRooted.Mathlib.Algebra.Polynomial.Veronese"
label = "Explicit section-matrix determinant in the coefficient variable"

[[definitions]]
name = "LinearRecurrence.veronese"
module = "RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese"
label = "Common recurrence for all Veronese sections of a polynomial sequence"

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

[[theorems]]
name = "LinearRecurrence.exists_veroneseSection"
module = "RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese"
label = "Sections of an order-d recurrence share a recurrence of order rd"

[[theorems]]
name = "LinearRecurrence.veronese_recurrence_of_eventually"
module = "RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese"
label = "Eventual recurrences pass to every Veronese section"

[[theorems]]
name = "RealRooted.isSolution_and_eq_zero_or_splits_veroneseSectionPolynomial"
module = "RealRooted.VeroneseSection"
label = "Nonnegative real-rooted solutions give real-rooted section solutions"
-->

<!-- realrooted-catalog-content -->
# Veronese sections

Veronese sections of a real-rooted polynomial with nonnegative coefficients are real-rooted or
zero. A difference equation recognizes the polynomial sequences that are Veronese sections of
products of linear factors, so their rows are real-rooted, and Veronese sections of
constant-coefficient recurrences again satisfy a constant-coefficient recurrence.

## Results

The $k$th $r$-Veronese section of $p=\sum_i p_i x^i$ is $\sum_{n\geq0}p_{k+rn}x^n$: it keeps
the coefficients whose indices are congruent to $k$ modulo $r$ and re-indexes them by
$n=(i-k)/r$.

**Theorem (Veronese sections).** Let $0 \leq k < r$. If a polynomial with nonnegative
coefficients splits over $\mathbb R$, then its $k$th $r$-Veronese section is zero or splits
over $\mathbb R$.

Fix $r \geq 1$ and real sequences $a_n$, $b_n$ with every $b_n \neq 0$. For a polynomial
sequence $P = (P_n)$ put $(\Delta P)_n = (P_{n+1} - a_n P_n)/b_n$. For a polynomial $H$, the
*seed*, the *product parent* is $Q_n(H) = H(x)\prod_{i<n}(a_i + b_i x)$, and $R_n(H)$ denotes
its $(r-1)$st $r$-Veronese section.

**Theorem (recognition).** $\Delta^r P = x P$ if and only if there is a unique polynomial $H$
with $R_n(H) = P_n$ for all $n$; the $i$th $r$-Veronese section of $H$ is
$(\Delta^{r-1-i} P)_0$ for $0 \leq i < r$. For $\beta \neq 0$, $\Delta^r P = (\alpha + \beta x) P$
if and only if there is a unique seed $H$ with $P_n(x) = R_n(H)(\alpha + \beta x)$ for all $n$.
If $a_n \geq 0$, $b_n > 0$, and the seed has nonnegative coefficients and splits over
$\mathbb R$, then every $P_n$ is zero or splits over $\mathbb R$, in the affine case for
$\beta>0$.

For example, if $B \neq 0$ and $P_{n+2} = A P_{n+1} + (Bx + c) P_n$ for all $n$, then there is a
unique seed $H$ such that $P_n$ is the odd Veronese section ($r = 2$) of $H\,(x + A/2)^n$,
evaluated at $c + A^2/4 + Bx$.

**Theorem (sections of recurrences).** Let $A$ be a commutative ring, $r \geq 1$, and let
$P(x,t)$ be monic in $t$ of degree $d$ with coefficients in $A[x]$. Put $y=x^r$ and let
$D(y,t)$ be the determinant of multiplication by $P(x,t)$ on $A[y,t]$ in the basis
$1,x,\dotsc,x^{r-1}$. If a sequence of polynomials in $A[x]$ satisfies the recurrence with
characteristic polynomial $P$, then every residue section of every solution satisfies the
recurrence with characteristic polynomial $D$, which is monic in $t$ of degree $rd$ when $A$
is nontrivial. If the source recurrence first determines row $N \geq d$, the section
recurrence first determines row $N+(r-1)d$. Over $\mathbb R$, if every source row has
nonnegative coefficients and splits, then every section row is zero or splits.

For binomial rows with $r=2$, Fibonacci tiling rows with $r=3$, and Delannoy triangle rows
with $r=2$, the section recurrences have orders two, six and four.

## Proof

Real-rootedness of Veronese sections follows from the Pólya frequency characterization of
real-rooted polynomials with nonnegative coefficients and total nonnegativity of an associated
matrix. For recurrences, the adjugate of the section multiplication matrix writes $D$ as a
multiple of $P$, so the shift operator $D$ annihilates every source solution, and taking a
section gives the section recurrence.

## References

[@AthanasiadisWagner2024x], where the Veronese-section convention and its linear-factor
recurrences appear together with a stronger interlacing statement. See also
[Veronese sections](sf:veroneseSectionsRealRooted) on symmetricfunctions.com.
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
