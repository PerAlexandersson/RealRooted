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
label = "Weighted column bound for multiplication by c² on the centered basis"

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
objects = ["Zig-zag Eulerian polynomials"]
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
label = "Exact entries of the matrix of multiplication by c² on the centered basis"

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

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagOperator_natDegree"
module = "RealRooted.IntervalDifferential.Degree"
label = "The zigzag operator raises the degree of a nonzero polynomial by one"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagLinearFactor_roots"
module = "RealRooted.IntervalDifferential.LinearInsertion"
label = "Inserting a real factor inserts a simple root into each gap"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzag_quadratic_certificate"
module = "RealRooted.IntervalDifferential.Certificates"
label = "Polynomial identity behind the insertion of a conjugate pair"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagQuadraticFactor_roots"
module = "RealRooted.IntervalDifferential.QuadraticInsertion"
label = "Inserting a conjugate pair in the disk of squared radius 13/3 keeps simple interval roots"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagTransform_cubic_roots_of_disk"
module = "RealRooted.IntervalDifferential.CubicDisk"
label = "The cubic seed has three simple transformed roots in (−1, 1)"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagTransform_quartic_roots_of_disk"
module = "RealRooted.IntervalDifferential.QuarticBounds"
label = "The even quartic seed has four simple transformed roots in (−1, 1)"

[[theorems]]
name = "RealRooted.IntervalDifferential.splits_roots_nodup_neg_of_mobius_eval"
module = "RealRooted.IntervalDifferential.MobiusRoots"
label = "The map (z − 1)/(z + 1) carries simple roots in (−1, 1) to simple negative roots"

[[theorems]]
name = "RealRooted.IntervalDifferential.zigzagTransform_parity_roots_of_disk"
module = "RealRooted.IntervalDifferential.UniversalTransfer"
label = "A parity polynomial with all roots in the disk transforms to simple roots in (−1, 1)"

[[definitions]]
name = "RealRooted.IntervalDifferential.zigzagOperator"
module = "RealRooted.IntervalDifferential.Basic"
label = "The centered zigzag differential operator"

[[definitions]]
name = "RealRooted.IntervalDifferential.zigzagTransform"
module = "RealRooted.IntervalDifferential.Basic"
label = "The centered zigzag transform Q(L)1"
-->

<!-- realrooted-catalog-content -->
# Zig-zag Eulerian polynomials

The zig-zag Eulerian polynomials count alternating permutations by swaps. They have only
distinct negative roots, which settles a conjecture of Petersen and Zhuang; the key input is a
disk bound for the zeros of a centered family.

## Results

Let $H_n(t)=\sum_\pi t^{\operatorname{sw}(\pi)}$ over the permutations $\pi$ of $[n]$ with
$\pi_1<\pi_2>\pi_3<\dotsb$, where a *swap* of $\pi$ is a value $i$ with
$\pi^{-1}(i)+1<\pi^{-1}(i+1)$ and $\operatorname{sw}(\pi)$ is the number of swaps. Then
$H_0=H_1=H_2=1$, $H_3=1+t$ and $H_4=1+3t+t^2$.

**Theorem.** For every $n\ge1$, $H_n$ has degree $\max(n-2,0)$, splits over $\mathbb R$, and
has distinct strictly negative roots.

This settles Conjecture 6.1(a) of Petersen and Zhuang: their $Z_n(t)=tH_n(t)$ is real-rooted.

**Proposition (recurrence).** Let $w_{n,k}$ be the number of words $u_1\le u_2\ge u_3\le\dotsb$
of length $n$ over the alphabet $[k]$. Then $w_{0,k}=1$, $w_{n,0}=0$ for $n>0$ and, for $n>0$,
$$
2w_{n,k+1}=2w_{n,k}
 +\sum_{p=0}^{n-1}w_{p,k}w_{n-1-p,k+1}
 +\mathbf{1}_{n=1}+\mathbf{1}_{n\geq2}w_{n-2,k+1}.
$$
For $n\ge1$ the coefficients of $H_n$ are recovered by
$$
a_{n,j}=w_{n,j+1}-\sum_{i=0}^{j-1}a_{n,i}\binom{n+j-i}{n},
\qquad H_n(t)=\sum_{j=0}^{n}a_{n,j}t^j ,
$$
and $a_{n,j}=0$ for $j>\max(n-2,0)$.

**Theorem (disk bound).** Let $p_n(c)$ be the coefficients of
$$
\sum_{n\geq 0} p_n(c)\, s^n = \sqrt{1-s^2}\,(\sec + \tan)\bigl(c \arcsin s\bigr),
$$
so that $p_n(c) = \sum_k e_k\, \alpha_{n,k}\, c^k$ with $e_k = [z^k](\sec z + \tan z)$ and
$\alpha_{n,k} = [s^n]\sqrt{1-s^2}\,(\arcsin s)^k$. For $n \geq 2$, every complex zero $c$ of
$p_n$ satisfies $|c|^2 < 13/3$.

Let $L F = (x^2-1)\,F' + 3x\,F$, and call a polynomial *interval-simple* if it splits over
$\mathbb R$ with only simple roots, all in $(-1,1)$. For nonzero $F$, $\deg LF=\deg F+1$, with
the leading coefficient multiplied by $\deg F+3$. If $F\ne0$ is interval-simple and $-3<a<3$,
then $(L-a)F$ is interval-simple; if $F$ is interval-simple of degree at least $4$ and
$a^2+b^2\le 13/3$, then $\bigl((L-a)^2+b^2\bigr)F$ is interval-simple. Consequently, if
$Q\ne0$ has degree at least $3$, $Q(-x)=\pm Q(x)$ and all complex roots of $Q$ satisfy
$|c|^2\le 13/3$, then $Q(L)\,1$ is interval-simple. Finally, if $G$ is interval-simple and
$H\ne0$ has $\deg H\le\deg G$ and vanishes at $(z-1)/(z+1)$ for every root $z$ of $G$, then $H$
has the degree of $G$ and only simple negative roots.

## Proof

Weak alternating words identify a centered polynomial built from $p_n$ with the swap
enumerator. The disk bound follows [@Alexandersson2026Eulerian, App. A–B]: a Riccati equation
for the generating function, an exact matrix for multiplication by $c^2$ on the centered basis,
and a weighted column-sum estimate for that matrix. The operator $L$ then inserts one real or
conjugate-pair factor of $Q$ at a time, starting from cubic or even quartic seeds, which gives
roots in $(-1,1)$. The map $z\mapsto(z-1)/(z+1)$ sends $(-1,1)$ to the negative real axis.

## References

- T. K. Petersen and Y. Zhuang, *Zig-zag Eulerian polynomials*,
  [arXiv:2403.07181](https://arxiv.org/abs/2403.07181), Conjecture 6.1(a).
- [@Alexandersson2026Eulerian, App. A–B].
- J. I. Coons and S. Sullivant, *The h*-Polynomial of the Order Polytope of the Zig-Zag Poset*,
  Electronic Journal of Combinatorics 30(2) (2023), P2.44,
  [doi:10.37236/11526](https://doi.org/10.37236/11526).
<!-- /realrooted-catalog-content -->
-/
