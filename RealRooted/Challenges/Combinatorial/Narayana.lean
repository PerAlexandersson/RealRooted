module

public import RealRooted.CombinatorialExamples.Avoid132Descents
public import RealRooted.CombinatorialExamples.DyckNarayana
public import RealRooted.LowerTriangularMatrix
public import RealRooted.MaoWangMatrixProduct
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.Mathlib.Combinatorics.Enumerative.DyckStatistics
public import RealRooted.NarayanaInterpolation
public import RealRooted.NarayanaTransformation.Basis
public import RealRooted.NarayanaTransformation.Coefficients
public import RealRooted.NarayanaTransformation.Endpoints
public import RealRooted.NarayanaTransformation.Falling
public import RealRooted.NarayanaTransformation.Rising
public import RealRooted.NarayanaTransformation.RootGeometry

/-!
# Narayana polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "narayana"
formalized = "2026-07-18"
tags = []
references = [
  "MaoWang2026x",
  "Brenti1989",
  "DominiciJohnstonJordaan2013x",
  "Zeng2026x",
]
authors = ["Mao", "Wang", "Dominici", "Johnston", "Jordaan", "Brenti", "Zeng"]
years = [1989, 2013, 2026]

[[definitions]]
name = "RealRooted.narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Coefficients"
label = "Generalized Narayana polynomials"

[[definitions]]
name = "RealRooted.narayanaTransform"
module = "RealRooted.NarayanaTransformation.Coefficients"
label = "Narayana transform"

[[definitions]]
name = "RealRooted.HasOnlyNonposRoots"
module = "RealRooted.NarayanaTransformation.RootGeometry"
label = "Zero, or real-rooted with nonpositive zeros"

[[definitions]]
name = "Polynomial.basisTransform"
module = "RealRooted.Mathlib.Algebra.Polynomial.BasisTransform"
label = "The linear map sending x^n to B_n"

[[definitions]]
name = "RealRooted.fallingFactorialPolynomial"
module = "RealRooted.NarayanaTransformation.Basis"
label = "Falling factorials"

[[definitions]]
name = "RealRooted.risingFactorialPolynomial"
module = "RealRooted.NarayanaTransformation.Basis"
label = "Generalized rising factorials"

[[definitions]]
name = "RealRooted.LowerTriangularMatrix.RowGeneratingFunctionsPF"
module = "RealRooted.LowerTriangularMatrix"
label = "Every row-generating polynomial is Pólya-frequency"

[[definitions]]
name = "RealRooted.LowerTriangularMatrix.MaoWangAdmissibleMatrix"
module = "RealRooted.MaoWangMatrixProduct"
label = "The Mao–Wang one-step factors"

[[theorems]]
name = "RealRooted.splits_narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are real-rooted"

[[theorems]]
name = "RealRooted.narayanaPolynomialRootLocation"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are Pólya-frequency"

[[theorems]]
name = "RealRooted.IsPFPolynomial.narayanaTransform"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "The Narayana transform preserves Pólya-frequency polynomials"
headline = true
symcat = "thm:narayanaTransformationMaoWang"

[[theorems]]
name = "RealRooted.HasOnlyNonposRoots.of_basisTransform_fallingFactorial"
module = "RealRooted.NarayanaTransformation.Falling"
label = "Brenti: nonpositive zeros in the falling-factorial basis pull back"
symcat = "thm:brentiFallingFactorialBasis"

[[theorems]]
name = "RealRooted.IsPFPolynomial.basisTransform_touchard"
module = "RealRooted.NarayanaTransformation.Basis"
label = "The Touchard transform preserves Pólya-frequency polynomials"

[[theorems]]
name = "RealRooted.IsPFPolynomial.basisTransform_risingFactorial"
module = "RealRooted.NarayanaTransformation.Rising"
label = "Rising-factorial transforms preserve Pólya-frequency polynomials"

[[theorems]]
name = "RealRooted.LowerTriangularMatrix.RowGeneratingFunctionsPF.mul_listProduct"
module = "RealRooted.MaoWangMatrixProduct"
label = "Mao–Wang: products with admissible factors keep Pólya-frequency rows"

[[theorems]]
name = "RealRooted.LowerTriangularMatrix.RowGeneratingFunctionsPF.mul_pow"
module = "RealRooted.MaoWangMatrixProduct"
label = "Mao–Wang: powers of an admissible factor keep Pólya-frequency rows"

[[theorems]]
name = "DyckWord.card_semilength_peakCount"
module = "RealRooted.Mathlib.Combinatorics.Enumerative.DyckStatistics"
label = "Dyck paths of semilength n with k peaks are Narayana-counted, except n = 1, k = 0"

[[theorems]]
name = "DyckWord.peakGeneratingPolynomial_eq_narayanaPolynomial"
module = "RealRooted.CombinatorialExamples.DyckNarayana"
label = "The peak polynomial of Dyck paths is x N_{n,1}(x)"

[[theorems]]
name = "RealRooted.Avoid132.descentGeneratingPolynomial_succ_eq_narayanaPolynomial"
module = "RealRooted.CombinatorialExamples.Avoid132Descents"
label = "132-avoiding permutations counted by descents give N_{n,1}(x)"

[[theorems]]
name = "RealRooted.Avoid132.strictInterl_descentGeneratingPolynomial_succ"
module = "RealRooted.CombinatorialExamples.Avoid132Descents"
label = "Descent polynomials of 132-avoiders are real-rooted and interlace"

[[definitions]]
name = "RealRooted.narayanaInterpolation"
module = "RealRooted.NarayanaInterpolation"
label = "Continuous Narayana interpolation between type B and shifted type A"

[[theorems]]
name = "RealRooted.narayanaInterpolation_eq_sum_gamma"
module = "RealRooted.NarayanaInterpolation"
label = "γ-expansion of the continuous Narayana interpolation"

[[theorems]]
name = "RealRooted.narayanaInterpolation_isPF"
module = "RealRooted.NarayanaInterpolation"
label = "The continuous Narayana interpolation is Pólya-frequency for θ > −1"

[[theorems]]
name = "RealRooted.narayanaInterpolation_roots_neg"
module = "RealRooted.NarayanaInterpolation"
label = "The zeros of the continuous Narayana interpolation are real and negative"
-->

<!-- realrooted-catalog-content -->
# Generalized Narayana polynomials and basis transforms

The generalized Narayana polynomials are Pólya-frequency, and the Narayana transform
$x^n\mapsto N_{n,m}(x)$ preserves Pólya-frequency polynomials.

## Results

A real polynomial is *Pólya-frequency* (PF) if its coefficients are nonnegative
and it is zero or real-rooted with all zeros $\le0$.  For $m,n\ge0$ the generalized Narayana
polynomial is
$$
N_{n,m}(x) =
\sum_{k=0}^{n} \frac{\binom{n}{k}\binom{n+m}{k}}{\binom{m+k}{k}}\, x^k .
$$
For $m=1$ the coefficients are Narayana numbers; for example $N_{2,1}(x)=1+3x+x^2$.

**Theorem (Narayana transform).** For all $m,n\ge0$, $N_{n,m}$ is real-rooted and
Pólya-frequency. If $p$ is Pólya-frequency, so is its Narayana transform, the image of $p$
under the linear map $x^n\mapsto N_{n,m}(x)$.

**Proposition (Dyck paths and 132-avoiders).** For $n\ge0$, the generating polynomial of Dyck
paths of semilength $n+1$ by peaks is $x\,N_{n,1}(x)$, and that of the 132-avoiding
permutations of $n+1$ letters by descents is $N_{n,1}(x)$. The number of Dyck paths of semilength
$n$ with $k$ peaks is the Narayana number for $(n,k)\ne(1,0)$. The descent polynomials of the
132-avoiders of $n+2$ and $n+3$ letters satisfy $f\ll g$.

### Basis transforms

For polynomials $B_0,B_1,\dots$ the basis transform $T_B$ is the linear map with
$T_B(x^n)=B_n(x)$. A polynomial has *only nonpositive zeros* if it is $0$ or real-rooted with all
zeros $\le0$. Put
$$
\langle x\rangle_k = x(x-1)\dotsm(x-k+1), \qquad
(x \mid \mu)_k = x(x+\mu)\dotsm(x+(k-1)\mu),
$$
and let $T_n$ be the Touchard polynomials, $T_0=1$ and $T_{n+1}=xT_n+xT_n'$.

**Theorem (Brenti).** [@Brenti1989, Thm. 2.4.2] If $\sum_k a_k\langle x\rangle_k$ has only
nonpositive zeros, then so does $\sum_k a_kx^k$.

**Theorem.** The Touchard transform $x^n\mapsto T_n(x)$ maps Pólya-frequency polynomials to
Pólya-frequency polynomials. So does the transform $x^n\mapsto(x\mid\mu)_n$ for every
$\mu>0$.

### Matrix products

For a lower-triangular array $M=(M(n,k))_{n,k\ge0}$ the row polynomials are
$M_n(x)=\sum_{k\le n}M(n,k)x^k$; we say $M$ has *Pólya-frequency rows* if every $M_n$ is
Pólya-frequency. A matrix is a *Mao–Wang factor* if its row $n$ lists the coefficients of
$B_n$, where $(B_n)$ is one of $(ax+d)^n$ with $a>0$, $d\ge0$; $T_n(x)$; $(x\mid\mu)_n$ with
$\mu>0$; or $N_{n,m}(x)$ with $m\ge0$.

**Theorem (Mao–Wang).** [@MaoWang2026x, Thm. 1.3] Let $M$ be lower-triangular with
Pólya-frequency rows and let $B_1,\dots,B_r$ be Mao–Wang factors. Then $MB_1\dotsm B_r$ has
Pólya-frequency rows. In particular $MB^r$ has Pólya-frequency rows for every factor $B$ and
$r\ge0$.

### Continuous interpolation

For real $\theta>-1$ put
$$
N_\theta(n, k) = \binom{n}{k} \frac{(\theta + 1)_n}{(\theta + 1)_k\,(\theta + 1)_{n-k}},
\qquad
P_n^{(\theta)}(t) = \sum_{k=0}^{n} N_\theta(n, k)\, t^k ,
$$
where $(a)_n=a(a+1)\dotsm(a+n-1)$. For $\theta=0$ these are the type B Narayana polynomials
$\sum_k\binom nk^2t^k$; for $\theta=1$ they are the shifted type A Narayana polynomials.

**Theorem.** For every real $\theta>-1$ and $n\ge0$,
$$
P_n^{(\theta)}(t) = \sum_{j \le n/2} \frac{n!}{j!\,(n - 2j)!\,(\theta + 1)_j}\,
  t^j (1 + t)^{n - 2j},
$$
so $P_n^{(\theta)}$ is $\gamma$-positive. Moreover $P_n^{(\theta)}$ is Pólya-frequency, and its
zeros are real and negative.

## Proof

The root statement is a Schur–Szegő composition: $P_n^{(\theta)}$ is a positive multiple of the
composition of the Jensen polynomial of $1/(\theta+1)_k$ with its reversal, and that Jensen
polynomial is Pólya-frequency because $1/(\theta+1)_k$ is a multiplier sequence. The source
[@Zeng2026x] proves real-rootedness for $\theta\ge0$ through Jacobi polynomials.

## References

The coefficient normalization is from [@MaoWang2026x] and the root-location input from
[@DominiciJohnstonJordaan2013x]. The Brenti theorem is Lemma 3.2 of [@MaoWang2026x]. The
continuous interpolation is [@Zeng2026x, (1.1)–(1.3) and Cor. 3.5]. See also the
[Narayana real-rootedness examples on symmetricfunctions.com](sf:ex:narayanaSturm),
[Brenti's falling-factorial theorem](sf:thm:brentiFallingFactorialBasis), and the
[Mao–Wang row-generating functions](sf:rowGeneratingFunction).
<!-- /realrooted-catalog-content -->
-/
