module

import RealRooted.Permanent.Basic
import RealRooted.Permanent.MonotoneColumn

/-!
# Monotone column permanent theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monotone-column-permanent"
formalized = "2026-10-13"
tags = []
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
name = "RealRooted.Permanent.columnPermanent_mvRealStable_of_decreasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Decreasing-column permanent is real stable"
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
name = "RealRooted.Permanent.diagonalPermanent_ne_zero_and_splits_of_increasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Monotone column permanent theorem"

[[theorems]]
name = "RealRooted.Permanent.diagonalPermanent_coeff_card"
module = "RealRooted.Permanent.Basic"
label = "The leading coefficient of per(zJ + A) is n!"
-->

<!-- realrooted-catalog-content -->
# Monotone column permanent theorem

If the columns of a real matrix $A$ are monotone, then $\operatorname{per}(zJ+A)$ is real-rooted
with leading coefficient $n!$, and the multivariate column permanent is real stable.

## Results

Let $A=(a_{ij})$ be a real $n\times n$ matrix and $J_n$ the all-ones matrix. The columns of $A$
are *weakly decreasing* if $a_{kj}\le a_{ij}$ for $i\le k$, and *weakly increasing* if
$a_{ij}\le a_{kj}$ for $i\le k$. The *column permanent* of $A$ is
$$
\operatorname{per}(z_j+a_{ij})
=\operatorname{per}\bigl(J_n\operatorname{diag}(z_1,\dots,z_n)+A\bigr).
$$

**Theorem (monotone column permanent).** If the columns of $A$ are weakly decreasing or weakly
increasing, then $\operatorname{per}(z_j+a_{ij})$ is real stable: it has no zero with every $z_j$
in the open upper half-plane. Consequently $\operatorname{per}(zJ_n+A)$ is nonzero and splits over
$\mathbb R$. Its coefficient of $z^n$ is $n!$ for every $A$.

The decreasing case is [@BrandenHaglundVisontaiWagner2011]; the increasing case is the
convention of the conjecture of Haglund, Ono and Wagner [@HaglundOnoWagner1999], to which the
decreasing case reduces by reversing the rows.

**Proposition (Ferrers matrices).** A *Ferrers matrix* is a zero-one matrix with weakly
decreasing columns and weakly increasing rows. For such $A$ the two-alphabet permanent
$$
\operatorname{per}\bigl(a_{ij}y_j+(1-a_{ij})x_i\bigr)
$$
is real stable. If $A$ is a Ferrers matrix of size $n+1$ with $a_{n+1,n+1}=0$, this polynomial
satisfies a deletion recurrence in terms of the polynomials of smaller Ferrers matrices.

## Proof

Decreasing columns reduce to zero-one columns, which sort into a Ferrers matrix. Real stability
of the Ferrers permanents follows by induction using the deletion recurrence. A specialization
of the $x_i$ and a fractional substitution give the multivariate theorem.

## References

See [@HaglundOnoWagner1999; @BrandenHaglundVisontaiWagner2011].
<!-- /realrooted-catalog-content -->
-/
