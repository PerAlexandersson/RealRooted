import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
import RealRooted.SymmetricDecomposition.FPolynomialSequence

/-!
# The `f`-polynomial transform of derivative recurrences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "f-transform-recurrences"
formalized = "2026-10-11"
references = [
  "BrandenSolus2019",
]

[[theorems]]
name = "RealRooted.fPolynomial_derivative"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "The derivative rule for the f-polynomial transform"

[[theorems]]
name = "RealRooted.fPolynomial_derivativeRecurrence_step"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "One transformed derivative-recurrence step"

[[theorems]]
name = "RealRooted.eq_fPolynomial_of_derivRec"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "A transformed recurrence identifies every row"

[[theorems]]
name = "RealRooted.natDegree_le_of_derivRec"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "Quadratic-linear derivative recurrences have at most linear degree growth"

[[theorems]]
name = "RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "A constant initial row gives the transformed recurrence identity"

[[theorems]]
name = "RealRooted.splits_fPolynomial"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-polynomial transform preserves splitting"
headline = true

[[theorems]]
name = "RealRooted.roots_fPolynomial_natDegree_eq_map"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The roots move by r ↦ r / (1 - r)"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_natDegree_of_roots_lt_one"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "Interlacing is preserved for roots below one"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_natDegree_of_one_lt_roots"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "Interlacing is preserved for roots above one"

[[theorems]]
name = "RealRooted.splits_of_eq_fPolynomial"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "Splitting transfers through the f-polynomial transform"

[[theorems]]
name = "RealRooted.StrictInterl.of_mul_X_sub_C_left_of_roots_gt"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "Peeling a left linear factor from strict interlacing"

[[theorems]]
name = "RealRooted.StrictInterl.of_mul_X_sub_C_right_of_roots_ge"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "Adding a right linear factor to strict interlacing"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_pad_of_mul_X_add_one"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "Padding an f-transform by powers of X + 1"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_sequence"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "Half-growth sequences transfer consecutive strict interlacing"
-->

<!-- realrooted-catalog-content -->
# The f-polynomial transform of derivative recurrences

For a polynomial $h$ of degree at most $d$, we use the
**f-polynomial transform**

$$
fPolynomial\ d\ h = \sum_{k=0}^{d} h_k X^k (X+1)^{d-k},
$$

where $h_k$ is the coefficient of $X^k$ in $h$. We write $f_j(c)$ for
`fPolynomial j c` when the degree bound is small. The derivative identity gives
the basic reason that this transform is useful: it converts a derivative
recurrence into another derivative recurrence.

We suppose that

$$
Q(n+1)=a(n)Q'(n)+b(n)Q(n),
$$

with $\deg a(n)\leq 2$ and $\deg b(n)\leq 1$. If the degrees of the rows of
$Q$ are bounded by their indices, then the transformed rows
$P(n)=fPolynomial\ n\ (Q(n))$ satisfy

$$
P(n+1)=(X+1)f_2(a(n))P'(n)
       +\bigl(f_1(b(n))-n f_2(a(n))\bigr)P(n).
$$

The one-step identity and induction theorem record this calculation in Lean.
The degree lemma supplies the required bound from a constant initial row, so
the recurrence identity can be applied directly to the usual recursively
defined sequence.

The transform also transfers the root properties needed in applications. It is
the substitution $X \mapsto X/(X+1)$ homogenized to degree $d$, so a root $r$ of
$h$ becomes the root $r/(1-r)$, and the degree drops when $r = 1$. Hence
$fPolynomial\ d\ h$ splits whenever $h$ splits, with no sign condition on
the coefficients, and split rows $Q(n)$ give split rows $P(n)$. When $h$ has no
root at $1$, the roots of $fPolynomial\ (\deg h)\ h$ are exactly the images
$r/(1-r)$. This map is increasing on $(-\infty, 1)$ and on $(1, \infty)$, so
strict interlacing transfers whenever all roots of both polynomials lie on one
side of $1$. For a
sequence with half-growth degrees $\deg Q(j)=(j+1)/2$, nonnegative
coefficients, split nonzero rows, and
consecutive strict interlacing, the padding and peeling lemmas give

$$
P(n) \mathrel{\ll} P(n+1) \qquad (n\geq 1).
$$

Here the peeling lemmas remove or add a factor $X-C(r)$ under the indicated
root inequalities, while the padding lemma restores the common powers of
$X+1$ required by the degree box. Thus real-rootedness and, in the half-growth
case, interlacing pass from $Q$ to its $f$-transform.

The alternating-runs polynomials in OEIS sequences [A008970](https://oeis.org/A008970),
[A059427](https://oeis.org/A059427), and [A186370](https://oeis.org/A186370)
give a common example. Their rows are f-transforms of peak polynomials, and
the peak rows have the half-growth degree pattern. The `rr_row_splits` tactic
has an `fTransform` route built on this recurrence and the splitting-transfer
theorem.

## References

See [@BrandenSolus2019] and the
[symmetric-decomposition overview on symmetricfunctions.com](sf:symmetricIDecomposition).
For the alternating-runs families and their references, see OEIS
[A008970](https://oeis.org/A008970), [A059427](https://oeis.org/A059427), and
[A186370](https://oeis.org/A186370).
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.FPolynomialRecurrences

end RealRooted.Challenges.FPolynomialRecurrences
