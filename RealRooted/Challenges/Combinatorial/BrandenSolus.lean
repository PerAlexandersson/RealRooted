module

public import RealRooted.CombinatorialExamples.DerangementStatistic
public import RealRooted.SymmetricDecomposition
public import RealRooted.SymmetricDecomposition.Definitions
public import RealRooted.SymmetricDecomposition.DerangementTransform
public import RealRooted.SymmetricDecomposition.FPolynomial
public import RealRooted.SymmetricDecomposition.Theorem26

/-!
# Interlacing and real roots under symmetric decompositions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-solus"
formalized = "2026-10-02"
tags = []
references = [
  "BrandenSolus2019",
]
authors = ["Brändén", "Solus"]
years = [2019]

[[definitions]]
name = "RealRooted.IsIdDecomposition"
module = "RealRooted.SymmetricDecomposition.Definitions"
label = "Symmetric I_d-decomposition"

[[theorems]]
name = "RealRooted.BrandenSolus.strictInterl_iff_of_isIdDecomposition"
module = "RealRooted.SymmetricDecomposition.Theorem26"
label = "Five interlacing conditions on p = a + xb are equivalent"
headline = true

[[definitions]]
name = "RealRooted.DerangementTransform.transform"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "Derangement transform x^j ↦ d_j"

[[theorems]]
name = "RealRooted.DerangementTransform.transform_magicExpansion_isPF"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "The derangement image of a nonnegative magic-basis combination is zero or real-rooted"

[[theorems]]
name = "RealRooted.DerangementTransform.transform_magicExpansion_strictInterl"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "For d ≥ 2 and a positive coordinate, the image lies between A_d and d_d"

[[theorems]]
name = "RealRooted.DerangementStatistic.derangementExcGenPoly_eq_polynomial"
module = "RealRooted.CombinatorialExamples.DerangementStatistic"
label = "Derangements counted by excedances give the derangement polynomials d_n"

[[theorems]]
name = "RealRooted.DerangementStatistic.derangementExcGenPoly_isRealRooted"
module = "RealRooted.CombinatorialExamples.DerangementStatistic"
label = "The excedance polynomial of derangements is real-rooted for n ≥ 2"
-->

<!-- realrooted-catalog-content -->
# Interlacing and real roots under symmetric decompositions

For a polynomial with a symmetric $I_d$-decomposition $p=a+xb$, five interlacing conditions on
$a$, $b$, $p$ are equivalent. The derangement transform of nonnegative combinations of
$x^k(1+x)^{d-k}$ is real-rooted and lies between two Eulerian-type polynomials.

## Results

Put $I_d(p)=x^dp(1/x)$ and $R_d(p)(x)=(-1)^dp(-1-x)$. An *$I_d$-decomposition* of $p$ is a pair
$(a,b)$ with $p=a+xb$, $\deg a\le d$, $\deg b\le d-1$, $I_d(a)=a$ and $I_{d-1}(b)=b$.

**Theorem (equivalences).** Let $\deg p\le d$, and let $(a,b)$ be an $I_d$-decomposition of $p$
with $a,b\ne0$ and nonnegative coefficients. Put $f=\sum_kp_k\,x^k(1+x)^{d-k}$. Then the
following are equivalent:
$$
b\ll a,\qquad a\ll p,\qquad b\ll p,\qquad I_d(p)\ll p,\qquad R_d(f)\ll f .
$$

**Derangement polynomials.** Let $d_n(x)=\sum_\sigma x^{\operatorname{exc}\sigma}$, summed over the
derangements $\sigma$ of $n$ letters, where $\operatorname{exc}\sigma$ counts the $i$ with
$i<\sigma(i)$. For $n\ge2$, $d_n$ is nonzero and real-rooted.

**Theorem (derangement transform).** Let $D$ be the linear map with $D(x^j)=d_j$, let $d\ge0$ and
let $c_0,\dots,c_d\ge0$. Then $D\bigl(\sum_kc_kx^k(1+x)^{d-k}\bigr)$ has nonnegative coefficients
and is zero or real-rooted with nonpositive roots. If $d\ge2$ and some $c_k>0$, it is nonzero
and
$$
D\bigl((1+x)^d\bigr)\ \ll\ D\Bigl(\sum_kc_kx^k(1+x)^{d-k}\Bigr)\ \ll\ d_d
$$
[@BrandenSolus2019, Cor. 3.7].

## Use

The equivalences reduce interlacing of $p$ with its symmetric pieces to interlacing of the
simpler pair $b\ll a$. See also the
[symmetric-decomposition overview on symmetricfunctions.com](sf:symmetricIDecomposition).

## Proof

The derangement transform is the Chow-derangement transform of the Pascal matrix, whose
resolving rows are the polynomials $x^k(1+x)^{d-k}$; the theorem is a case of the Brändén–Vecchi
Chow-resolution theorem.

## References

- [@BrandenSolus2019]
<!-- /realrooted-catalog-content -->

Human statement:
sf:symmetricIDecomposition

Original publication: P. Branden and L. Solus, "Symmetric decompositions and
real-rootedness", International Mathematics Research Notices 2021 (2019),
7764--7798.

This module exposes the completed nondegenerate `StrictInterl` form of the
Branden--Solus symmetric-decomposition theorem.  The decomposition API and
boundary-case proof remain in `RealRooted.SymmetricDecomposition`.
-/
