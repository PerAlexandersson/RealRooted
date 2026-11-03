module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial

/-!
# Zig-zag Eulerian polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "zigzag-eulerian"
formalized = "2026-10-23"
references = ["Alexandersson2026Eulerian"]
tags = ["realrooted-original"]
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

[[definitions]]
name = "RealRooted.CenteredEulerian.polynomial"
module = "RealRooted.CenteredEulerian.Basis"
label = "Centered polynomial p_n(c)"

[[definitions]]
name = "RealRooted.CenteredEulerian.ColumnBound"
module = "RealRooted.CenteredEulerian.RootCriterion"
label = "Weighted column bound (B.1)"

[[theorems]]
name = "RealRooted.ZigzagEulerian.polynomial_roots"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial"
label = "Simple negative roots of the recurrence-defined family"

[[theorems]]
name = "RealRooted.ZigzagEulerian.polynomial_eq_zigzagEulerianPolynomial"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial"
label = "The recurrence-defined polynomial equals the swap enumerator"
tags = []

[[theorems]]
name = "RealRooted.ZigzagEulerian.zigzagEulerianPolynomial_roots"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted"
label = "Simple negative roots of zig-zag Eulerian polynomials"
headline = true

[[theorems]]
name = "RealRooted.ZigzagEulerian.weakUpDownWordCount_recurrence"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.WordRecurrence"
label = "First-maximum recurrence for weak alternating words"
tags = []

[[theorems]]
name = "RealRooted.CenteredEulerian.polynomial_root_normSq_lt"
module = "RealRooted.CenteredEulerian.ColumnBound"
label = "Complex zeros of the centered polynomials satisfy |c|² < 13/3"
headline = true

[[theorems]]
name = "RealRooted.CenteredEulerian.root_bound_of_columnBound"
module = "RealRooted.CenteredEulerian.RootCriterion"
label = "The weighted column bound implies the root disk"

[[theorems]]
name = "RealRooted.CenteredEulerian.columnBound"
module = "RealRooted.CenteredEulerian.ColumnBound"
label = "The weighted column bound holds"

[[theorems]]
name = "RealRooted.CenteredEulerian.rMat_decomp"
module = "RealRooted.CenteredEulerian.ChangeBasis"
label = "Exact change-of-basis formula (B.6)"

[[theorems]]
name = "RealRooted.CenteredEulerian.riccati_unique"
module = "RealRooted.CenteredEulerian.Riccati"
label = "The Riccati equation determines the centered generating function"

[[theorems]]
name = "RealRooted.CenteredEulerian.riccati_mobius"
module = "RealRooted.CenteredEulerian.Riccati"
label = "A Möbius map sends Riccati solutions for c to c + 2"

[[theorems]]
name = "RealRooted.CenteredEulerian.hasSum_eulerG"
module = "RealRooted.CenteredEulerian.EulerAnalytic"
label = "Analytic expansion of cot(π/4 − z/2)"
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

## The centered disk bound

The analytic input is a bound on the complex zeros of the centered
polynomials. For $n \geq 0$ let $p_n(c)$ be the coefficients of the formal
series
$$
\sum_{n\geq 0} p_n(c)\, s^n = \sqrt{1-s^2}\,
  (\sec + \tan)\bigl(c \arcsin s\bigr),
$$
so that $p_n(c) = \sum_k e_k\, \alpha_{n,k}\, c^k$ with
$e_k = [z^k](\sec z + \tan z)$ and $\alpha_{n,k} = [s^n]\sqrt{1-s^2}\,
(\arcsin s)^k$.

**Theorem.** For $n \geq 2$, every complex zero $c$ of $p_n$ satisfies
$|c|^2 < 13/3$.

This disk is the analytic input to the transfer step described above. The
proof follows the zig-zag argument of [@Alexandersson2026Eulerian], Appendices A and B, and
has three ingredients, proved as formal power series identities or explicit
real estimates.

1. *A Riccati equation.* For real $c$, the series
   $G_c(s) = \sqrt{1-s^2}\,(\sec+\tan)(c \arcsin s)$ satisfies
   $(1-s^2)G' + sG = \tfrac{c}{2}\,(G^2 + 1 - s^2)$, and this equation with
   $G(0)=1$ determines $G_c$ uniquely. The map
   $G \mapsto (1-s^2)(G+s)/(1-s^2-sG)$ sends solutions for $c$ to solutions
   for $c+2$, which identifies the whole odd family $G_{2k+1}$ starting from
   $G_1 = 1+s$.
2. *An exact change of basis.* Multiplication by $c^2$ acts on the basis
   $p_2, p_3, \dots$ by a matrix $R$. Its entries are written exactly (formula
   (B.6)) in terms of the series of $\arcsin$ and of $(s/\arcsin s)^2$, and of
   the Euler ratios $e_k/e_{k+2}$. The latter are controlled through the
   partial fraction expansion of $\cot(\pi/4 - z/2)$, which gives the Taylor
   coefficients of the Euler numbers analytically.
3. *A weighted column-sum criterion.* With weights $\omega_0=\omega_1=1$ and
   $\omega_j=2$ for $j\geq 2$, the estimates above show
   $\sum_i \omega_i |R_{ij}| < \tfrac{13}{3}\,\omega_j$ for all $j$. If
   $p_n(c)=0$, then $c^2$ is an eigenvalue of a truncation of $R$ (after
   restricting to one parity class), so $|c|^2 < 13/3$.

The supporting analysis occupies the modules under
`RealRooted.CenteredEulerian`.

## References

J. I. Coons and S. Sullivant, *The h*-Polynomial of the Order Polytope of the
Zig-Zag Poset*, Electronic Journal of Combinatorics 30(2) (2023), P2.44,
[doi:10.37236/11526](https://doi.org/10.37236/11526).

T. K. Petersen and Y. Zhuang, *Zig-zag Eulerian polynomials*,
[arXiv:2403.07181](https://arxiv.org/abs/2403.07181), Conjecture 6.1(a).
Their polynomial $Z_n(t)$ equals $tH_n(t)$ in the normalization used here.
<!-- /realrooted-catalog-content -->
-/
