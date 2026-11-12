module

import RealRooted.Applications.BinderVecchi.UniformChow
import RealRooted.Applications.BinderVecchi.UniformMatroid

/-!
# Uniform-matroid refined Hodge–Poincaré challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "uniform-matroid-hodge-poincare"
formalized = "2026-10-09"
tags = []
references = [
  "BinderVecchi2026x",
  "Athanasiadis2025EulerianTransformation",
  "BrandenJochemko2022",
  "BrandenSolus2019",
]
authors = ["Binder", "Vecchi", "Athanasiadis", "Brändén", "Jochemko", "Solus"]
years = [2021, 2022, 2025, 2026]

[[definitions]]
name = "RealRooted.BinderVecchi.refinedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Refined Hodge–Poincaré polynomial of a uniform matroid"

[[definitions]]
name = "RealRooted.BinderVecchi.modifiedAugmentedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Modified augmented refined Hodge–Poincaré polynomial"

[[definitions]]
name = "RealRooted.EulerianTransform.transform"
module = "RealRooted.SymmetricDecomposition.EulerianTransform"
label = "Eulerian transformation 1 ↦ 1, x^n ↦ x A_n(x)"

[[theorems]]
name = "RealRooted.BinderVecchi.isRealRooted_refinedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Binder–Vecchi: refined Hodge–Poincaré polynomials of U_{r,n} are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.BinderVecchi.isRealRooted_modifiedAugmentedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Binder–Vecchi: the modified augmented family is real-rooted"

[[theorems]]
name = "RealRooted.UniformChow.isRealRooted_chowUniform"
module = "RealRooted.Applications.BinderVecchi.UniformChow"
label = "The Chow polynomial of U_{r,n} is real-rooted (the case i = 0)"

[[theorems]]
name = "RealRooted.UniformChow.isRealRooted_augChowUniform"
module = "RealRooted.Applications.BinderVecchi.UniformChow"
label = "The augmented Chow polynomial of U_{r,n} is real-rooted"

[[theorems]]
name = "RealRooted.EulerianTransform.transform_magicExpansion_isPF"
module = "RealRooted.SymmetricDecomposition.EulerianTransform"
label = "Athanasiadis: the Eulerian transformation is real-rooted on the magic cone"

[[theorems]]
name = "RealRooted.EulerianTransform.transform_magicExpansion_interl"
module = "RealRooted.SymmetricDecomposition.EulerianTransform"
label = "The Eulerian transform of a magic-cone polynomial lies between its two endpoints"
-->

<!-- realrooted-catalog-content -->
# Refined Hodge–Poincaré polynomials of uniform matroids

The refined Hodge–Poincaré polynomial of the uniform matroid $U_{r,n}$ and its modified augmented
variant are real-rooted.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated.
For $r\ge1$ and $1\le i\le n-r$ put
$$
W_{j,i}(r,n) = \binom nj \sum_{\ell=1}^{n-r-i+1}\binom{n-j-\ell}{r-j-1}\binom{n-r-\ell}{i-1}.
$$
Let $d_j$ be the derangement polynomials, $A_0=1$, and $A_s(x)=\sum_{\sigma\in\mathfrak S_s}
x^{\operatorname{des}\sigma}$ for $s\ge1$. Binder and Vecchi [@BinderVecchi2026x] give the
refined Hodge–Poincaré polynomial of $U_{r,n}$ and its modified augmented variant as
$$
\underline H^i_{r,n}(x) = \sum_{j<r} W_{j,i}(r,n)\, d_j(x)\, x^{r-1-j},\qquad
\widetilde H^i_{r,n}(x) = \sum_{s<r} W_{s,i}(r,n)\, A_s(x)\, x^{r-s}.
$$
The theorems below concern these explicit formulas.

**Theorem (Binder–Vecchi, Thms. 1.4 and 1.6).** [@BinderVecchi2026x, Thms. 1.4 and 1.6]
For $r\ge1$ and $1\le i\le n-r$, the polynomials $\underline H^i_{r,n}$ and
$\widetilde H^i_{r,n}$ are nonzero and real-rooted.

**Theorem (case $i=0$).** For $1\le r\le n$, the Chow polynomial and the augmented Chow
polynomial of $U_{r,n}$ are nonzero and real-rooted. Here, with the Chow operator
$S_k(p)=(x^kp(1/x)-p)/(x-1)$, the Chow polynomial is $P+x\,S_{r-1}(P)$ with
$P=\sum_{k<r}\binom nk d_k$, and the augmented one is $Q+x\,S_r(Q)$ with
$Q=\mathcal A(\sum_{k<r}\binom nk x^k)$.

**Theorem (Athanasiadis).** [@Athanasiadis2025EulerianTransformation] Let $\mathcal A$ be the
Eulerian transformation, the linear map with $\mathcal A(1)=1$ and
$\mathcal A(x^n)=xA_n(x)$ for $n\ge1$. If $f=\sum_{k=0}^dc_kx^k(1+x)^{d-k}$ with all
$c_k\ge0$, then $\mathcal A f$ has nonnegative coefficients and is zero or real-rooted with
nonpositive zeros, and $\mathcal A\bigl((1+x)^d\bigr)\ll\mathcal A f\ll\mathcal A(x^d)$.

## Proof

Put $g=\sum_{j<r}W_{j,i}x^j$ and let $I_k(p)=x^kp(1/x)$ be reversal at degree $k$. Then
$\underline H=I_{r-1}(\mathcal D g)$ for the Brändén–Solus derangement transform
$\mathcal D\colon x^n\mapsto d_n$, and $\widetilde H=I_r(\mathcal A g)$ for the Eulerian
transformation $\mathcal A$ of Brändén–Jochemko. A Vandermonde-type identity shows that $g$ has
nonnegative coordinates in the magic basis $x^p(1+x)^{r-1-p}$, and both transforms send such
polynomials to real-rooted ones. For $\mathcal D$ this is Brändén–Solus, via the
Brändén–Vecchi Chow resolution of the Pascal matrix. For $\mathcal A$ it is Athanasiadis's
theorem, proved with the Brändén–Vecchi staircase row transform. The Chow cases use the same
staircase argument.

## References

[@BinderVecchi2026x; @Athanasiadis2025EulerianTransformation; @BrandenJochemko2022;
@BrandenSolus2019].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.
-/
