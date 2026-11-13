module

public import RealRooted.CombinatorialExamples.Hoggatt
public import RealRooted.Applications.OEIS.A056939

/-!
# Hoggatt polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "hoggatt"
formalized = "2026-11-13"
authors = ["Fang", "Zhang", "Zhao", "Dilks"]
years = [2015, 2025]

[[definitions]]
name = "RealRooted.Hoggatt.polynomial"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The binomial-product polynomial F(n,m)"

[[definitions]]
name = "RealRooted.Hoggatt.normalized"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "Normalized Hoggatt polynomials H_n^[m]"

[[theorems]]
objects = ["Hoggatt polynomials"]
property = "interlacing"
name = "RealRooted.Hoggatt.normalized_interlaces_and_isCoprime"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "For every m ≥ 2, consecutive Hoggatt rows strictly interlace"
headline = true

[[theorems]]
name = "RealRooted.Hoggatt.polynomial_pred_interlaces"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "F(n−1,m) strictly interlaces F(n,m) for n ≥ m ≥ 2"

[[theorems]]
name = "RealRooted.Hoggatt.derivative_binomialHadamard"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The Hadamard derivative identity G'(n+1,m+1) = (n+1) F(n,m+1)"

[[theorems]]
name = "RealRooted.Hoggatt.derivative_hadamard_one"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The derivative identity at m = 2"

[[theorems]]
objects = ["Hoggatt polynomials"]
name = "RealRooted.Hoggatt.normalized_splits"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "Every Hoggatt polynomial is real-rooted, for all m ≥ 1"

[[theorems]]
name = "RealRooted.Hoggatt.normalized_one"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The m = 1 family consists of powers of X + 1"

[[theorems]]
name = "RealRooted.Hoggatt.hasSimpleRoots_polynomial"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "The binomial-product polynomials have simple roots for m ≥ 2"

[[theorems]]
objects = ["Baxter descent polynomials"]
property = "interlacing"
name = "RealRooted.Hoggatt.baxter_interlaces"
module = "RealRooted.CombinatorialExamples.Hoggatt"
label = "Baxter polynomials are a strict Sturm sequence"

[[theorems]]
name = "RealRooted.Hoggatt.normalized_three_eq_baxter"
module = "RealRooted.Applications.OEIS.A056939"
label = "For m = 3, the Hoggatt polynomials are the Baxter descent polynomials (A056939)"

[[theorems]]
name = "RealRooted.Applications.OEIS.A056939.polynomial_isCoprime_succ"
module = "RealRooted.Applications.OEIS.A056939"
label = "Consecutive Baxter descent polynomials are coprime"
-->

<!-- realrooted-catalog-content -->
# Hoggatt polynomials

The Hoggatt polynomials interpolate between the binomial polynomials, the Narayana polynomials
and the descent polynomials of Baxter permutations. For each $m\ge2$ they form a Sturm sequence
with simple negative roots.

## Results

For $N\ge0$ and $m\ge1$ let
$$
F_{N,m}(t)=\sum_{k\ge0}\Bigl(\prod_{i=0}^{m-1}\binom{N}{k+i}\Bigr)t^k ,
$$
and for $n\ge1$ define the *Hoggatt polynomial* $H_n^{[m]}(t)=F_{n+m-2,m}(t)/F_{n+m-2,m}(0)$,
which has degree $n-1$ and constant term $1$. By MacMahon's formula, the coefficient of $t^k$
counts plane partitions in a $k\times(n-1-k)\times m$ box. For $m=1$ we get $(1+t)^{n-1}$, for
$m=2$ the Narayana polynomials $\sum_k\frac1n\binom nk\binom n{k+1}t^k$, and for $m=3$ the
descent polynomials of Baxter permutations of length $n$, which are the rows of
[OEIS A056939](https://oeis.org/A056939).

**Theorem (Fang–Zhang–Zhao).** [@FangZhangZhao2025x] Let $m\ge2$. For every $n\ge1$, the roots
of $H_n^{[m]}$ are simple and negative, $H_n^{[m]}\ll H_{n+1}^{[m]}$, and the two polynomials
have no common root.

**Corollary (Dilks).** For every $m\ge1$ and $n\ge1$, $H_n^{[m]}$ is real-rooted.

In particular, consecutive Baxter descent polynomials strictly interlace.

## Proof

Write $*$ for the coefficientwise (Hadamard) product. Comparing coefficients gives
$$
\frac{d}{dt}\bigl(F_{N+1,1}*F_{N,m}\bigr)=(N+1)\,F_{N,m+1}.
$$
Induction on $m$, with the [Garloff–Wagner theorem](rr:hadamard-products) for Hadamard products
and [derivative interlacing](rr:derivative-interlacing), gives real roots and weak interlacing.
For strictness, the same identity together with simplicity of the roots of Hadamard products
rules out common roots of Hadamard products with consecutive binomial powers, and positivity of
the Wronskian gives Markov's strict form of the derivative step.

## References

- [@FangZhangZhao2025x, Theorems 1–2 and §2].
- K. Dilks, *Involutions on Baxter Objects, and q-Gamma Nonnegativity*,
  Ph.D. thesis, University of Minnesota, 2015, Theorem 3.8.
<!-- /realrooted-catalog-content -->
-/
