import RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial

/-!
# Zig-zag Eulerian polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "zigzag-eulerian"
formalized = "2026-10-23"
authors = ["Alexandersson"]
years = [2026]

[[definitions]]
name = "RealRooted.ZigzagEulerian.recursiveWordCount"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Recurrence"
label = "Word counts defined by the first-maximum recurrence"

[[definitions]]
name = "RealRooted.ZigzagEulerian.recursiveCoefficient"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial"
label = "Numerator coefficients by triangular inversion"

[[definitions]]
name = "RealRooted.ZigzagEulerian.polynomial"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial"
label = "Recurrence-defined zig-zag Eulerian polynomial"

[[definitions]]
name = "RealRooted.ZigzagEulerian.IsUpDown"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions"
label = "Alternating permutations"

[[definitions]]
name = "RealRooted.ZigzagEulerian.swapCount"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions"
label = "Swap statistic"

[[definitions]]
name = "RealRooted.ZigzagEulerian.zigzagEulerianPolynomial"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions"
label = "Zig-zag Eulerian polynomial"

[[theorems]]
name = "RealRooted.ZigzagEulerian.polynomial_roots"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial"
label = "Simple negative roots of the recurrence-defined family"
headline = true

[[theorems]]
name = "RealRooted.ZigzagEulerian.polynomial_eq_zigzagEulerianPolynomial"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial"
label = "The recurrence-defined polynomial equals the swap enumerator"

[[theorems]]
name = "RealRooted.ZigzagEulerian.zigzagEulerianPolynomial_roots"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted"
label = "Simple negative roots of zig-zag Eulerian polynomials"

[[theorems]]
name = "RealRooted.ZigzagEulerian.weakUpDownWordCount_recurrence"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.WordRecurrence"
label = "First-maximum recurrence for weak alternating words"
-->

<!-- realrooted-catalog-content -->
# Zig-zag Eulerian polynomials

Let $H_n(t)$ count permutations $\pi_1<\pi_2>\pi_3<\dotsb$ by swaps.
A swap is a value $i$ for which $\pi^{-1}(i)+1<\pi^{-1}(i+1)$.
The initial polynomials are $H_1=H_2=1$, $H_3=1+t$, and
$H_4=1+3t+t^2$.

**Theorem.** For every $n\geq 1$, $H_n$ has degree $\max(n-2,0)$,
splits over the real numbers, and has distinct strictly negative roots.

The same family has a definition by recurrences alone. Put $w_{0,k}=1$ and
$w_{n,0}=0$ for $n>0$, and define, for $n>0$,

$$
2w_{n,k+1}=2w_{n,k}
 +\sum_{p=0}^{n-1}w_{p,k}w_{n-1-p,k+1}
 +\mathbf{1}_{n=1}+\mathbf{1}_{n\geq2}w_{n-2,k+1}.
$$

The final summand is omitted when $n=1$. This recursion decreases length first,
then alphabet size. Recover coefficients by

$$
a_{n,j}=w_{n,j+1}-\sum_{i=0}^{j-1}a_{n,i}\binom{n+j-i}{n},
\qquad H_n(t)=\sum_{j=0}^{n}a_{n,j}t^j\quad(n\geq1).
$$

The equality with the swap enumerator, including the vanishing of coefficients
above degree $\max(n-2,0)$, is proved. The empty row is defined separately as $H_0=1$.

The proof identifies a centered polynomial through weak alternating words,
bounds its complex roots in a fixed disk, and applies a differential-operator
transfer followed by a fractional linear substitution. The combinatorial
identification, analytic bound and transfer are all proved in this library.

## References

J. I. Coons and S. Sullivant, *The h*-Polynomial of the Order Polytope of the
Zig-Zag Poset*, Electronic Journal of Combinatorics 30(2) (2023), P2.44,
[doi:10.37236/11526](https://doi.org/10.37236/11526).

T. K. Petersen and Y. Zhuang, *Zig-zag Eulerian polynomials*,
[arXiv:2403.07181](https://arxiv.org/abs/2403.07181).
<!-- /realrooted-catalog-content -->
-/
