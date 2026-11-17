module

import RealRooted.CommonInterleaver.RootSelection
import RealRooted.CommonInterleaver.RootSelectionTree
import RealRooted.FiniteFreeAdditive
import RealRooted.FiniteFreeAdditive.Preservation
import RealRooted.FiniteFreeAdditive.RootWindow
import RealRooted.FiniteFreeMultiplicative
import RealRooted.FiniteFreeRootCount
import RealRooted.MultivariateStability.ExpectedCharpoly
import RealRooted.MultivariateStability.MSSBound
import RealRooted.MultivariateStability.MixedCharacteristic
import RealRooted.NarayanaTransformation.Rectangular.Preservation
import RealRooted.RectangularConvolution

/-!
# Finite free convolutions and interlacing families

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "finite-free-convolutions"
formalized = "2026-09-11"
references = [
  "MarcusSpielmanSrivastava2015I",
  "MarcusSpielmanSrivastava2015II",
  "MarcusSpielmanSrivastava2022",
  "GribinskiMarcus2022",
  "LeakeRyder2018x",
]
authors = ["Marcus", "Spielman", "Srivastava", "Gribinski", "Leake", "Ryder"]
years = [2015, 2018, 2022]

[[definitions]]
name = "RealRooted.finiteFreeAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive"
label = "Finite free additive convolution"

[[definitions]]
name = "RealRooted.finiteFreeMultiplicativeConvolution"
module = "RealRooted.FiniteFreeMultiplicative"
label = "Finite free multiplicative convolution"

[[definitions]]
name = "RealRooted.rectangularAdditiveConvolution"
module = "RealRooted.RectangularConvolution"
label = "Rectangular additive convolution"

[[definitions]]
name = "RealRooted.MixedCharacteristic.mixedCharacteristic"
module = "RealRooted.MultivariateStability.MixedCharacteristic"
label = "Mixed characteristic polynomial"

[[theorems]]
name = "RealRooted.splits_finiteFreeAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive.Preservation"
label = "Marcus–Spielman–Srivastava: ⊞_d preserves real-rootedness"
headline = true

[[theorems]]
name = "RealRooted.splits_finiteFreeMultiplicativeConvolution"
module = "RealRooted.FiniteFreeRootCount"
label = "Marcus–Spielman–Srivastava: ⊠_d preserves real-rootedness"

[[theorems]]
name = "RealRooted.IsRealRootedIn.finiteFreeAdditiveConvolution_Icc"
module = "RealRooted.FiniteFreeAdditive.RootWindow"
label = "Roots in [A, B] and [a, b] give roots of p ⊞_d q in [A + a, B + b]"

[[theorems]]
name = "RealRooted.HasOnlyNonnegRoots.rectangularAdditiveConvolution"
module = "RealRooted.NarayanaTransformation.Rectangular.Preservation"
label = "Gribinski–Marcus: the rectangular convolution preserves nonnegative roots"

[[theorems]]
objects = ["Mixed characteristic polynomials"]
name = "RealRooted.MixedCharacteristic.isRealRooted_mixedCharacteristic"
module = "RealRooted.MultivariateStability.MixedCharacteristic"
label = "Marcus–Spielman–Srivastava: mixed characteristic polynomials are real-rooted"

[[theorems]]
name = "RealRooted.MixedCharacteristic.expectedCharpoly_eq_mixedCharacteristic"
module = "RealRooted.MultivariateStability.ExpectedCharpoly"
label = "Expected characteristic polynomials of random rank-one sums are mixed characteristic"

[[theorems]]
name = "RealRooted.MixedCharacteristic.mixedCharacteristic_roots_le_one_add_sqrt_sq"
module = "RealRooted.MultivariateStability.MSSBound"
label = "Marcus–Spielman–Srivastava: if Σ Aᵢ = I and tr Aᵢ ≤ ε, the roots are at most (1 + √ε)²"

[[theorems]]
name = "RealRooted.exists_mem_largestRoot_le_sum"
module = "RealRooted.CommonInterleaver.RootSelection"
label = "With a common interlacer, some member has largest root at most that of the sum"

[[theorems]]
name = "RealRooted.RootSelectionTree.Valid.exists_leaf_largestRoot_le"
module = "RealRooted.CommonInterleaver.RootSelectionTree"
label = "Interlacing families: some leaf has largest root at most that of the root polynomial"
-->

<!-- realrooted-catalog-content -->
# Finite free convolutions and interlacing families

The finite free convolutions of Marcus, Spielman and Srivastava preserve real-rootedness and are
finite analogues of the free convolutions of random matrix theory. Together with interlacing
families and the real-rootedness of mixed characteristic polynomials, they give the solution of
the Kadison–Singer problem and bipartite Ramanujan graphs of every degree.

## Results

Write $p(x)=\sum_{i=0}^{d}a_ix^{d-i}$ and $q(x)=\sum_{j=0}^{d}b_jx^{d-j}$. The *finite free
additive* and *multiplicative convolutions* are
$$
(p\boxplus_dq)(x)=\sum_{k=0}^{d}x^{d-k}\sum_{i+j=k}\frac{(d-i)!\,(d-j)!}{d!\,(d-k)!}\,a_ib_j,
\qquad
(p\boxtimes_dq)(x)=\sum_{k=0}^{d}(-1)^k\binom dk^{-1}a_kb_k\,x^{d-k}.
$$
The *rectangular additive convolution* $p\boxplus_{m,n}q$, in degree $n$, multiplies each term
of $\boxplus_n$ by $\frac{(n+m-i)!\,(n+m-j)!}{(n+m)!\,(n+m-k)!}$. For real $n\times n$ matrices
$A_1,\dots,A_m$, the *mixed characteristic polynomial* is
$$
\mu[A](x)=\prod_{i=1}^m(1-\partial_{z_i})\det\Bigl(xI+\sum_iz_iA_i\Bigr)\Big|_{z=0}.
$$

**Theorem (Marcus–Spielman–Srivastava).** [@MarcusSpielmanSrivastava2022] If $p,q$ are
real-rooted of degree at most $d$, then $p\boxplus_dq$ is real-rooted, and so is $p\boxtimes_dq$
when $q$ has only nonnegative roots. If the roots of $p$ lie in $[A,B]$ and those of $q$ in
$[a,b]$, then the roots of $p\boxplus_dq$ lie in $[A+a,B+b]$ [@LeakeRyder2018x, Prop. 1.1].

**Theorem (Gribinski–Marcus).** [@GribinskiMarcus2022] If $p,q$ have degree $n$, positive
leading coefficients and only nonnegative roots, then $p\boxplus_{m,n}q$ is zero or real-rooted
with only nonnegative roots.

**Theorem (mixed characteristic polynomials).** [@MarcusSpielmanSrivastava2015II] If the $A_i$
are positive semidefinite, then $\mu[A]$ is real-rooted. If $\sum_iA_i=I$ and
$\operatorname{tr}A_i\le\varepsilon$ for all $i$, then every root of $\mu[A]$ is at most
$(1+\sqrt\varepsilon)^2$. The expected characteristic polynomial of a sum of independent random
rank-one matrices $v_iv_i^{\mathsf T}$ is the mixed characteristic polynomial of the matrices
$\mathbb E\,v_iv_i^{\mathsf T}$.

**Theorem (interlacing families).** [@MarcusSpielmanSrivastava2015I] Let $f_1,\dots,f_k$ have
degree $d$ and positive leading coefficients, and suppose some $h$ of degree $d-1$ satisfies
$h\ll f_i$ for every $i$. Then some $f_i$ has largest root at most the largest root of
$f_1+\dots+f_k$. Consequently, in a finite tree whose leaves carry such polynomials, the node
polynomials are the sums over their children, and the children of each node have a common
interlacer, some leaf has largest root at most the largest root of the polynomial at the root.

## Use

An interlacing family turns a bound on the expected characteristic polynomial into a bound for
one outcome. With the root bound for $\mu[A]$ this proves Weaver's conjecture and hence the
Kadison–Singer problem. The root bound $2\sqrt{\Delta-1}$ of the
[Heilmann–Lieb theorem](rr:heilmann-lieb) plays the same role for Ramanujan graphs. The
rectangular convolution gives a proof of the [Narayana transformation theorem](rr:narayana).

## Proof

The additive theorem follows from the Lieb–Sokal lemma, since the convolution is a differential
operator in $q$ applied to $p$. The signed reciprocal $x^dp(-1/x)$ turns the
[Schur–Szegő composition](rr:hadamard-products) into $\boxtimes_d$. Real-rootedness of
$\mu[A]$ follows from [real stability](rr:real-stability): $\det(xI+\sum_iz_iA_i)$ is real
stable and each $1-\partial_{z_i}$ preserves real stability. The root bound follows the barrier
argument of Marcus, Spielman and Srivastava, with the Helton–Vinnikov step replaced by an
elementary Pick-function lemma.

## References

[@MarcusSpielmanSrivastava2015I; @MarcusSpielmanSrivastava2015II;
@MarcusSpielmanSrivastava2022]; [@GribinskiMarcus2022]; [@LeakeRyder2018x, Prop. 1.1].
<!-- /realrooted-catalog-content -->
-/
