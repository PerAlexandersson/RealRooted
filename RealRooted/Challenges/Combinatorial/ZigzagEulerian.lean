module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.RecurrencePolynomial

/-!
# Zig-zag Eulerian polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "zigzag-eulerian"
formalized = "2026-10-23"
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

## The centered differential operator

The root-location transfer uses the differential operator
$$
L F = (x^2-1)\,F' + 3x\,F
$$
on $\mathbb R[x]$. For a real polynomial $Q$, its transform is $Q(L)\,1$, obtained by
substituting the operator $L$ into $Q$ and applying the result to the constant
polynomial $1$. The operator raises the degree of a nonzero polynomial by exactly
one, with leading coefficient multiplied by $\deg F + 3$, so the transform of $Q$
has the same degree as $Q$.

Call a polynomial *interval-simple* if it splits over $\mathbb R$ and has only
simple roots, all in $(-1,1)$. The transform of a product is built one factor at a
time, and each step preserves interval-simplicity.

- A real factor $x-a$ with $-3<a<3$ becomes the operator $L-a$. If $F$ is nonzero
  and interval-simple, then $(L-a)F$ is interval-simple: it has one simple root
  between each pair of consecutive roots of $F$ and one on each side of the
  extreme roots, by a sign comparison at the roots of $F$.
- A conjugate pair $(x-a)^2+b^2$ with $a^2+b^2\le 13/3$ becomes
  $(L-a)^2+b^2$. If $F$ is interval-simple of degree at least four, then so is the
  result. The sign at the roots of $(L-a)F$ comes from a
  polynomial identity (the quadratic certificate), root-sum inequalities for the
  split polynomial $F$ proved by Cauchy--Schwarz, and the disk bound.
- The seeds start the induction. The cubic $x^3+kx$ transforms to
  $3x\,(20x^2+k-11)$ and the even quartic $x^4+kx^2+p$ to
  $360x^4+(12k-312)x^2+(33-3k+p)$. When all complex roots lie in the disk
  $|c|^2\le 13/3$, these have three, respectively four, simple roots in $(-1,1)$.

**Theorem.** Let $Q$ be a nonzero real polynomial of degree at least $3$ with
$Q(-x)=\pm Q(x)$, all of whose complex roots $c$ satisfy $|c|^2\le 13/3$. Then the
transform $Q(L)\,1$ splits over $\mathbb R$ and has only simple roots, all in
$(-1,1)$. The proof peels off an even quartic divisor of the parity polynomial
(or the cubic shape when the degree is three) to obtain a seed, then inserts the
remaining real and conjugate-pair factors as above.

The Möbius map $z\mapsto(z-1)/(z+1)$ sends $(-1,1)$ onto the negative real axis.
If $G$ has simple roots in $(-1,1)$ and a nonzero polynomial $H$ of no larger degree
vanishes at the image of every root of $G$, then $H$ has the same degree as $G$
and simple negative roots. This is the substitution that turns the interval
statement into the negativity of the roots of $H_n$.

## References

J. I. Coons and S. Sullivant, *The h*-Polynomial of the Order Polytope of the
Zig-Zag Poset*, Electronic Journal of Combinatorics 30(2) (2023), P2.44,
[doi:10.37236/11526](https://doi.org/10.37236/11526).

T. K. Petersen and Y. Zhuang, *Zig-zag Eulerian polynomials*,
[arXiv:2403.07181](https://arxiv.org/abs/2403.07181), Conjecture 6.1(a).
Their polynomial $Z_n(t)$ equals $tH_n(t)$ in the normalization used here.
<!-- /realrooted-catalog-content -->
-/
