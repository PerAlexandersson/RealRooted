import RealRooted.Permanent.MonotoneColumn

/-!
# Monotone column permanent theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monotone-column-permanent"
formalized = "2026-10-13"
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
headline = true

[[theorems]]
name = "RealRooted.Permanent.diagonalPermanent_ne_zero_and_splits_of_decreasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Decreasing-column univariate permanent is real-rooted"

[[theorems]]
name = "RealRooted.Permanent.diagonalPermanent_ne_zero_and_splits_of_increasingColumns"
module = "RealRooted.Permanent.MonotoneColumn"
label = "Monotone column permanent theorem"
headline = true
-->

<!-- realrooted-catalog-content -->
# Monotone column permanent theorem

Let $A=(a_{ij})$ be a real $n\times n$ matrix. We say that its columns are
weakly decreasing if $a_{ij}\geq a_{i+1,j}$ whenever both entries exist. The
definition `HasWeaklyIncreasingColumns` reverses this inequality.

The multivariate column permanent is
$$
\operatorname{per}(z_j+a_{ij})
=\operatorname{per}(J_n\operatorname{diag}(z_1,\dotsc,z_n)+A),
$$
where $J_n$ is the all-ones matrix. The theorem
`columnPermanent_mvRealStable_of_decreasingColumns` proves that this polynomial
is real stable: it does not vanish when every $z_j$ lies in the open upper
half-plane.

Reversing the rows preserves the permanent and changes decreasing columns into
increasing columns. Thus
`columnPermanent_mvRealStable_of_increasingColumns` gives the convention used
in the original Haglund–Ono–Wagner conjecture.

Setting every $z_j$ equal to one variable $z$ gives
$$
\operatorname{per}(zJ_n+A).
$$
The theorem
`diagonalPermanent_ne_zero_and_splits_of_increasingColumns` proves that this
polynomial is nonzero and splits over the reals. Its leading coefficient is
$n!$.

For the proof, we first reduce decreasing columns to decreasing zero-one
columns. We then sort the columns into a Ferrers matrix and use a deletion
recurrence for the two-alphabet polynomial
$$
\operatorname{per}\bigl(a_{ij}y_j+(1-a_{ij})x_i\bigr).
$$
The five finite Ferrers identities used in this formalization were proved by
Aristotle. Stability of the recurrence, specialization of the $x_i$, and a
fractional substitution yield the multivariate theorem.

## References

J. Haglund, K. Ono, and D. G. Wagner,
[“Theorems and conjectures involving rook polynomials with only real
zeros,”](https://doi.org/10.1007/978-1-4613-0305-3_13) in *Topics in Number
Theory*, Mathematics and Its Applications 467 (1999), 207–221,
[doi:10.1007/978-1-4613-0305-3_13](https://doi.org/10.1007/978-1-4613-0305-3_13).

P. Brändén, J. Haglund, M. Visontai, and D. G. Wagner,
[“Proof of the monotone column permanent
conjecture,”](https://arxiv.org/abs/1010.2565) in *Notions of Positivity and
the Geometry of Polynomials*, Trends in Mathematics (2011), 63–78,
[doi:10.1007/978-3-0348-0142-3_5](https://doi.org/10.1007/978-3-0348-0142-3_5),
[arXiv:1010.2565](https://arxiv.org/abs/1010.2565).
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.MonotoneColumnPermanent

end RealRooted.Challenges.MonotoneColumnPermanent
