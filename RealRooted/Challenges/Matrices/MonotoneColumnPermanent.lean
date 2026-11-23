module

import RealRooted.FerrersHit.Roots
import RealRooted.Permanent.Basic
import RealRooted.Permanent.Ferrers
import RealRooted.Permanent.MonotoneColumn

/-!
# Monotone column permanent theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "monotone-column-permanent"
formalized = "2026-10-13"
references = [
  "HaglundOnoWagner1999",
  "BrandenHaglundVisontaiWagner2011",
]
authors = ["Haglund", "Ono", "Wagner", "Brändén", "Visontai"]
years = [1999, 2011]

[[definitions]]
name = "Matrix.HasWeaklyDecreasingColumns"
module = "RealRooted.Permanent.Basic"
label = "Weakly decreasing matrix columns"

[[definitions]]
name = "Matrix.HasWeaklyIncreasingColumns"
module = "RealRooted.Permanent.Basic"
label = "Weakly increasing matrix columns"

[[definitions]]
name = "RealRooted.Permanent.columnPermanent"
module = "RealRooted.Permanent.Basic"
label = "Multivariate column permanent"

[[definitions]]
name = "RealRooted.Permanent.diagonalPermanent"
module = "RealRooted.Permanent.Basic"
label = "Univariate diagonal permanent"

[[definitions]]
name = "Matrix.IsFerrers"
module = "RealRooted.Permanent.Ferrers"
label = "Ferrers matrix"

[[definitions]]
name = "RealRooted.Permanent.ferrersPermanent"
module = "RealRooted.Permanent.Ferrers"
label = "Two-alphabet Ferrers permanent"

[[theorems]]
name = "RealRooted.Permanent.ferrersPermanent_eq_recurrenceRhs"
module = "RealRooted.Permanent.Ferrers"
label = "Ferrers deletion recurrence"

[[theorems]]
name = "RealRooted.Permanent.ferrersPermanent_mvRealStable"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Ferrers permanents are real stable"

[[theorems]]
objects = ["Monotone column permanents"]
property = "real-stable"
name = "RealRooted.Permanent.columnPermanent_mvRealStable_of_decreasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = '$\operatorname{per}(z_j + a_{ij})$ is real stable when the columns of $(a_{ij})$ decrease'
headline = true

[[theorems]]
name = "RealRooted.Permanent.columnPermanent_mvRealStable_of_increasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Increasing-column permanent is real stable"

[[theorems]]
name = "RealRooted.Permanent.diagonalPermanent_ne_zero_and_splits_of_decreasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Decreasing-column univariate permanent is real-rooted"

[[theorems]]
objects = ["Monotone column permanents"]
name = "RealRooted.Permanent.diagonalPermanent_ne_zero_and_splits_of_increasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Monotone column permanent theorem: per(zJ + A) is real-rooted for monotone columns"

[[theorems]]
name = "RealRooted.Permanent.diagonalPermanent_coeff_card"
module = "RealRooted.Permanent.Basic"
label = "The leading coefficient of per(zJ + A) is n!"
[[definitions]]
name = "RealRooted.FerrersHit.hitPolynomial"
module = "RealRooted.FerrersHit.Basic"
label = "Standard rook-to-hit transform"

[[theorems]]
objects = ["Hit polynomials of Ferrers boards"]
property = "real-rooted"
name = "RealRooted.FerrersHit.hitPolynomial_ne_zero_and_splits"
module = "RealRooted.FerrersHit.Roots"
label = "Ferrers hit polynomials are nonzero and real-rooted"
-->

<!-- realrooted-catalog-content -->
# Monotone column permanent theorem

If the columns of a real $n\times n$ matrix $A$ are monotone, then $\operatorname{per}(zJ+A)$ is
real-rooted, where $J$ is the all-ones matrix. Haglund, Ono and Wagner conjectured this, and
Brändén, Haglund, Visontai and Wagner proved the stronger multivariate statement.

## Results

The columns of $A=(a_{ij})$ are *weakly decreasing* if $a_{kj}\le a_{ij}$ for $i\le k$, and
*weakly increasing* if $a_{ij}\le a_{kj}$ for $i\le k$.

**Theorem (Brändén–Haglund–Visontai–Wagner).** [@BrandenHaglundVisontaiWagner2011] If the
columns of $A$ are weakly decreasing or weakly increasing, then
$\operatorname{per}(z_j+a_{ij})$ is real stable. Consequently $\operatorname{per}(zJ+A)$ is
real-rooted, with leading coefficient $n!$.

**Proposition (Ferrers matrices).** A *Ferrers matrix* is a zero-one matrix with weakly
decreasing columns and weakly increasing rows. For such $A$ the two-alphabet permanent
$\operatorname{per}\bigl(a_{ij}y_j+(1-a_{ij})x_i\bigr)$ is real stable, and it satisfies a
deletion recurrence in terms of smaller Ferrers matrices.

## Use

For a zero-one matrix the permanent $\operatorname{per}(zJ+A)$ is a rook-type polynomial.
The height-based rook-to-hit transform is also formalized directly: if
$0\le h_1\le\cdots\le h_n\le n$, we define $r_k$ by
$\sum_k r_k(x)_{n-k}=\prod_i(x+h_i-i+1)$ and set
$H(t)=\sum_k r_k(n-k)!(t-1)^k$. Then $H$ is nonzero and real-rooted
[@HaglundOnoWagner1999, Thm. 1]. This algebraic definition does not require a
rook-placement counting model.

The hit-polynomial proof uses the Brändén E transform of the factorial product,
integer level crossings, and endpoint multiplicity. It is independent of the
permanent counting identities. The E image has all its roots in $[-1,0]$;
bounded reversal and a shift yield $H$.

## Proof

Decreasing columns reduce to zero-one columns, which sort into a Ferrers matrix, and the
increasing case follows by reversing the rows. Real stability of the Ferrers permanents follows
by induction from the deletion recurrence. A specialization of the $x_i$ and a fractional
substitution give the multivariate theorem.

## References

[@HaglundOnoWagner1999]; [@BrandenHaglundVisontaiWagner2011].
<!-- /realrooted-catalog-content -->
-/
