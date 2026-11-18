module

import RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese
import RealRooted.VeroneseMatrix
import RealRooted.VeroneseRecognition
import RealRooted.VeroneseRecognition.Affine
import RealRooted.VeroneseSection

/-!
# Veronese sections

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "veronese-sections"
formalized = "2026-10-05"
references = [
  "AissenSchoenbergWhitney1952",
  "AthanasiadisWagner2024x",
]
authors = ["Aissen", "Schoenberg", "Whitney", "Athanasiadis", "Wagner"]
years = [1952, 2024]

[[definitions]]
name = "RealRooted.veroneseSectionPolynomial"
module = "RealRooted.VeroneseSection"
label = "Veronese section"

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
label = "Product parent H(x) ∏ (aᵢ + bᵢ x) with seed H"

[[definitions]]
name = "RealRooted.veroneseProductRow"
module = "RealRooted.VeroneseRecognition"
label = "Last Veronese section of a product parent"

[[theorems]]
name = "RealRooted.veroneseSectionPolynomial_eq_zero_or_splits"
module = "RealRooted.VeroneseMatrix"
label = "Veronese sections of real-rooted polynomials with nonnegative coefficients are real-rooted"
headline = true
symcat = "veroneseSectionsRealRooted"

[[theorems]]
name = "RealRooted.iterate_sequenceDelta_eq_X_mul_iff_existsUnique_seed"
module = "RealRooted.VeroneseRecognition"
label = "Δ^r P = X P holds exactly for the rows of a product parent"

[[theorems]]
name = "RealRooted.iterate_sequenceDelta_eq_affine_mul_iff_existsUnique_seed"
module = "RealRooted.VeroneseRecognition.Affine"
label = "Δ^r P = (α + βX) P holds exactly for affine substitutions of such rows"

[[theorems]]
name = "RealRooted.sequenceDelta_row_eq_zero_or_splits"
module = "RealRooted.VeroneseRecognition"
label = "Recognized rows are zero or real-rooted when the seed is nonnegative and splits"

[[theorems]]
name = "RealRooted.existsUnique_affineVeroneseProductRow_of_orderTwo_recurrence"
module = "RealRooted.VeroneseRecognition.Affine"
label = "P(n+2) = A P(n+1) + (Bx + c) P(n) has a unique affine Veronese parent"

[[theorems]]
name = "LinearRecurrence.exists_veroneseSection"
module = "RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese"
label = "Sections of an order-d recurrence share a recurrence of order rd"

[[theorems]]
name = "RealRooted.isSolution_and_eq_zero_or_splits_veroneseSectionPolynomial"
module = "RealRooted.VeroneseSection"
label = "Sections of nonnegative real-rooted recurrence rows are real-rooted section solutions"
-->

<!-- realrooted-catalog-content -->
# Veronese sections

Taking every $r$th coefficient of a real-rooted polynomial with nonnegative coefficients gives a
real-rooted polynomial. A difference equation recognizes the sequences that arise as sections of
products of linear factors, and sections of recurrence rows again satisfy a recurrence, so both
give real-rooted families.

## Results

The $k$th $r$-*Veronese section* of $p=\sum_ip_ix^i$, for $0\le k<r$, is
$\sum_{n\ge0}p_{k+rn}x^n$.

**Theorem (Veronese sections).** If $p$ has nonnegative coefficients and is real-rooted, then
each of its Veronese sections is zero or real-rooted.

Fix $r\ge1$ and real sequences $a_n$, $b_n$ with $b_n\ne0$. For a polynomial sequence
$P=(P_n)$ put $(\Delta P)_n=(P_{n+1}-a_nP_n)/b_n$. For a polynomial $H$, the *seed*, let
$R_n(H)$ be the $(r-1)$st $r$-Veronese section of $H(x)\prod_{i<n}(a_i+b_ix)$.

**Theorem (recognition).** $\Delta^rP=xP$ if and only if $P_n=R_n(H)$ for all $n$, for a unique
seed $H$, whose sections are read off from $(\Delta^jP)_0$. For $\beta\ne0$,
$\Delta^rP=(\alpha+\beta x)P$ if and only if $P_n(x)=R_n(H)(\alpha+\beta x)$ for a unique $H$. If
$a_n\ge0$, $b_n>0$ and $H$ has nonnegative coefficients and is real-rooted, then every $P_n$ is
zero or real-rooted, in the affine case for $\beta>0$.

**Corollary (second-order recurrences).** If $B\ne0$ and $P_{n+2}=AP_{n+1}+(Bx+c)P_n$, then
$P_n$ is the odd section ($r=2$) of $H(x)\,(x+A/2)^n$ evaluated at $c+A^2/4+Bx$, for a unique
seed $H$.

**Theorem (sections of recurrences).** If a sequence of polynomials satisfies a linear
recurrence of order $d$ whose coefficients are polynomials in $x$ independent of $n$, then all
its $r$-Veronese sections satisfy one common recurrence of order $rd$, whose characteristic
polynomial is a norm of the original one. If every row has nonnegative coefficients and is
real-rooted, so is every section row.

## Use

Veronese sections turn a real-rooted family into new ones, such as the even and odd parts of
binomial or Delannoy rows. Athanasiadis and Wagner show that sections also preserve
interlacing, in the stronger form of fully interlacing matrices [@AthanasiadisWagner2024x,
Thm. 5.3].

## Proof

By the [Aissen–Schoenberg–Whitney theorem](rr:aissen-schoenberg-whitney), $p$ is real-rooted
with nonnegative coefficients exactly when its coefficient sequence is a Pólya frequency
sequence, and the Toeplitz matrix of a section is a submatrix of the Toeplitz matrix of $p$.
For recurrences, the adjugate of the multiplication matrix on $1,x,\dots,x^{r-1}$ writes the
norm as a multiple of the characteristic polynomial, so it annihilates every solution.

## References

[@AissenSchoenbergWhitney1952]; [@AthanasiadisWagner2024x, Thm. 5.3]. See also
[Veronese sections](sf:veroneseSectionsRealRooted) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
