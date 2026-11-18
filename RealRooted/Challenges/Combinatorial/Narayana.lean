module

import RealRooted.BinaryRunTransformation.Coefficients
import RealRooted.BinaryRunTransformation.Continuation
import RealRooted.BinaryRunTransformation.Interlacing
import RealRooted.BinaryRunTransformation.MultiplierMotzkin
import RealRooted.CombinatorialExamples.Avoid132Descents
import RealRooted.CombinatorialExamples.DyckNarayana
import RealRooted.MaoWangMatrixProduct
import RealRooted.NarayanaInterpolation
import RealRooted.NarayanaTransformation.Coefficients
import RealRooted.NarayanaTransformation.ContinuousNarayanaGamma
import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.NarayanaTransformation.Falling
import RealRooted.NarayanaTransformation.Recurrences.Interlacing

/-!
# Narayana polynomials

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "families"
slug = "narayana"
formalized = "2026-07-18"
references = [
  "Brenti1989",
  "DominiciJohnstonJordaan2013x",
  "MaoWang2026x",
  "Zeng2026x",
]
authors = ["Brenti", "Dominici", "Johnston", "Jordaan", "Mao", "Wang", "Zeng"]
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
name = "RealRooted.narayanaInterpolation"
module = "RealRooted.NarayanaInterpolation"
label = "Continuous Narayana interpolation between type B and shifted type A"

[[definitions]]
name = "RealRooted.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run transformation"
tags = ["realrooted-original"]

[[theorems]]
objects = ["Narayana polynomials"]
name = "RealRooted.splits_narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are real-rooted"
headline = true

[[theorems]]
objects = ["Narayana polynomials"]
property = "interlacing"
name = "RealRooted.strictInterl_narayanaPolynomial_succ"
module = "RealRooted.NarayanaTransformation.Recurrences.Interlacing"
label = "Consecutive generalized Narayana polynomials of positive degree interlace"

[[theorems]]
name = "DyckWord.peakGeneratingPolynomial_eq_narayanaPolynomial"
module = "RealRooted.CombinatorialExamples.DyckNarayana"
label = "The peak polynomial of Dyck paths is $x N_{n,1}(x)$"

[[theorems]]
name = "RealRooted.Avoid132.descentGeneratingPolynomial_succ_eq_narayanaPolynomial"
module = "RealRooted.CombinatorialExamples.Avoid132Descents"
label = "132-avoiding permutations counted by descents give $N_{n,1}(x)$"

[[theorems]]
objects = ["Descent polynomials of 132-avoiding permutations"]
property = "interlacing"
name = "RealRooted.Avoid132.strictInterl_descentGeneratingPolynomial_succ"
module = "RealRooted.CombinatorialExamples.Avoid132Descents"
label = "Descent polynomials of 132-avoiders are real-rooted and interlace"

[[theorems]]
name = "RealRooted.IsPFPolynomial.narayanaTransform"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Mao–Wang: the Narayana transform preserves Pólya frequency polynomials"
symcat = "thm:narayanaTransformationMaoWang"

[[theorems]]
name = "RealRooted.LowerTriangularMatrix.RowGeneratingFunctionsPF.mul_listProduct"
module = "RealRooted.MaoWangMatrixProduct"
label = "Mao–Wang: products with admissible factors keep Pólya frequency rows"

[[theorems]]
name = "RealRooted.HasOnlyNonposRoots.of_basisTransform_fallingFactorial"
module = "RealRooted.NarayanaTransformation.Falling"
label = "Brenti: nonpositive zeros in the falling-factorial basis pull back"
symcat = "thm:brentiFallingFactorialBasis"

[[theorems]]
objects = ["Continuous Narayana interpolation polynomials"]
property = "pf"
name = "RealRooted.narayanaInterpolation_isPF"
module = "RealRooted.NarayanaInterpolation"
label = "The continuous Narayana interpolation is Pólya frequency for θ > −1"

[[theorems]]
objects = ["Continuous Narayana interpolation polynomials"]
property = "interlacing"
name = "RealRooted.strictInterl_narayanaInterpolation_succ"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "Consecutive continuous Narayana interpolations interlace"

[[theorems]]
name = "RealRooted.narayanaInterpolation_eq_sum_gamma"
module = "RealRooted.NarayanaInterpolation"
label = "γ-expansion of the continuous Narayana interpolation"

[[theorems]]
objects = ["Gamma polynomials of the continuous Narayana interpolation"]
property = "interlacing"
name = "RealRooted.strictInterl_continuousNarayanaGamma_succ"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "Consecutive γ-polynomials of the interpolation interlace"

[[theorems]]
name = "RealRooted.IsPFPolynomial.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Continuation"
label = "$J_n$ maps PF polynomials of degree at most $n$ to PF polynomials"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.strictInterl_binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Interlacing"
label = "$J_n$ preserves interlacing on inputs of degree at most $(n+1)/2$"
tags = ["realrooted-original"]

[[theorems]]
objects = ["Motzkin ascent polynomials"]
property = "interlacing"
name = "RealRooted.motzkinAscentRow_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Motzkin ascent polynomials form a Sturm chain"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Narayana polynomials

The Narayana numbers count Dyck paths by peaks, and their generating polynomials are
real-rooted. We prove this for the generalized Narayana polynomials $N_{n,m}$, together with the
theorem of Mao and Wang that the Narayana transform $x^n\mapsto N_{n,m}$ preserves Pólya
frequency polynomials, and the same properties for a continuous interpolation.

## Results

A real polynomial is *Pólya frequency* (PF) if its coefficients are nonnegative and it is zero
or real-rooted with all zeros $\le0$. For $m,n\ge0$ let
$$
N_{n,m}(x)=\sum_{k=0}^n\frac{\binom nk\binom{n+m}k}{\binom{m+k}k}\,x^k .
$$
For $m=1$ the coefficients are the Narayana numbers; for example $N_{2,1}=1+3x+x^2$.

**Theorem (Narayana polynomials).** [@DominiciJohnstonJordaan2013x] For all $m,n\ge0$,
$N_{n,m}$ is real-rooted, hence PF, and $N_{n,m}\ll N_{n+1,m}$ for $n\ge1$.

**Corollary (Dyck paths and 132-avoiders).** The generating polynomial of Dyck paths of
semilength $n+1$ by peaks is $x\,N_{n,1}(x)$, and that of the 132-avoiding permutations of $n+1$
letters by descents is $N_{n,1}(x)$. Consecutive descent polynomials of 132-avoiders interlace.

**Theorem (Mao–Wang).** [@MaoWang2026x, Thm. 1.3] If $p$ is PF, so is its Narayana transform,
the image of $p$ under the linear map $x^n\mapsto N_{n,m}(x)$. More generally, if a
lower-triangular array has PF row polynomials, so does its product with any finite sequence of
arrays whose rows are the coefficients of $(ax+d)^n$ ($a>0$, $d\ge0$), Touchard polynomials,
generalized rising factorials or $N_{n,m}$.

**Theorem (Brenti).** [@Brenti1989, Thm. 2.4.2] If $\sum_ka_k\,x(x-1)\cdots(x-k+1)$ has only
real nonpositive zeros, then so does $\sum_ka_kx^k$.

For real $\theta>-1$ the *continuous Narayana interpolation* is
$$
P_n^{(\theta)}(t)=\sum_{k=0}^n\binom nk\frac{(\theta+1)_n}{(\theta+1)_k\,(\theta+1)_{n-k}}\,t^k
=\sum_{j\le n/2}\frac{n!}{j!\,(n-2j)!\,(\theta+1)_j}\,t^j(1+t)^{n-2j},
$$
with $(a)_n=a(a+1)\cdots(a+n-1)$. For $\theta=0$ it is the type B Narayana polynomial
$\sum_k\binom nk^2t^k$, and for $\theta=1$ the shifted type A Narayana polynomial.

**Theorem (continuous interpolation).** For $\theta>-1$, $P_n^{(\theta)}$ is PF
and $\gamma$-positive, and both $P_n^{(\theta)}$ and its $\gamma$-polynomial interlace their
successors.

**Theorem (binary-run transformation).** Let $J_n$ be the linear map with $J_n(1)=1$ and
$J_n(x^m)=\binom nm^{-1}\sum_k\binom{m-1}{k-1}\binom{n+1-m}kx^k$ for $1\le m\le n$. If $p$ is PF
with $\deg p\le n$, then $J_np$ is PF. If $f\ll g$ have nonnegative coefficients and
$\deg g\le\lfloor(n+1)/2\rfloor$, then $J_nf\ll J_ng$. The Motzkin ascent polynomials
([OEIS A114580](https://oeis.org/A114580)) are images under $J_n$ and form a Sturm chain.

## Use

The Narayana polynomial $N_{n,1}$ is the $h$-polynomial of the $n$-dimensional associahedron.
Composed with a diagonal multiplier sequence, the preservation theorem for $J_n$ gives the
Mao–Wang theorem.

## Proof

The interpolation $P_n^{(\theta)}$ is a positive multiple of the Schur–Szegő composition of the
Jensen polynomial of the multiplier sequence $1/(\theta+1)_k$ with its reversal. For the
binary-run transformation, we scale the input by a parameter: at parameter zero the image is a
Schur–Szegő composition with a path-matching polynomial, and the stability method of
[@BorceaBranden2009I] keeps every critical value away from zero as the parameter grows.

## References

[@Brenti1989, Thm. 2.4.2]; [@DominiciJohnstonJordaan2013x]; [@MaoWang2026x, Thm. 1.3];
[@Zeng2026x, (1.1)–(1.3) and Cor. 3.5]; [@BorceaBranden2009I]. See also
[Narayana real-rootedness examples](sf:ex:narayanaSturm) and
[row-generating functions](sf:rowGeneratingFunction) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
