import RealRooted.Applications.BinderVecchi.UniformChow
import RealRooted.Applications.BinderVecchi.UniformMatroid

/-!
# Uniform-matroid refined Hodge–Poincaré challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "uniform-matroid-hodge-poincare"
authors = ["Binder", "Vecchi", "Athanasiadis", "Brändén", "Jochemko"]
years = [2022, 2025, 2026]

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

For the uniform matroid $U_{r,n}$ and $1 \le i \le n-r$, Binder and Vecchi give explicit
formulas for the refined Hodge–Poincaré polynomial
$$
\underline H^i_{r,n}(x) = \sum_{j<r} W_{j,i}(r,n)\, d_j(x)\, x^{r-1-j}
$$
and for its modified augmented variant
$$
\widetilde H^i_{r,n}(x) = \sum_{s<r} W_{s,i}(r,n)\, A_s(x)\, x^{r-s},
$$
where $d_j$ are the derangement polynomials, $A_s$ the Eulerian polynomials, and
$W_{j,i}(r,n) = \binom nj \sum_{\ell=1}^{n-r-i+1}\binom{n-j-\ell}{r-j-1}\binom{n-r-\ell}{i-1}$.

**Theorem** (Binder–Vecchi, Theorems 1.4 and 1.6). Both polynomials are real-rooted.

## Proof idea

With $g = \sum_j W_{j,i} x^j$ we have $\underline H = I_{r-1}(\mathcal D g)$ for the
Brändén–Solus derangement transform $\mathcal D$, and $I_r(\widetilde H) = \mathcal A g$ for
the Eulerian transformation $\mathcal A\colon 1 \mapsto 1,\ x^n \mapsto xA_n(x)$ of
Brändén–Jochemko. A Vandermonde-type identity shows that $g$ has nonnegative coordinates in
the magic basis $x^p(1+x)^{r-1-p}$. Both transforms send such polynomials to real-rooted ones:
for $\mathcal D$ this is Brändén–Solus (via the Brändén–Vecchi Chow resolution of the Pascal
matrix), and for $\mathcal A$ it is Athanasiadis's theorem, proved here with the Brändén–Vecchi
staircase row transform.

For $i = 0$ the two families are the Chow and augmented Chow polynomials of $U_{r,n}$; their
real-rootedness is proved from explicit formulas with the same Brändén–Vecchi staircase
argument. The identification of those formulas with the Chow-ring Hilbert series is checked by
computation but not formalized.
The singular-cohomology interpretation of the polynomials is not formalized; the theorems are
about the explicit formulas.

## References

K. Binder and L. Vecchi, “Augmented singular cohomology, uniform matroids, and
real-rootedness,” arXiv:2609.15946 (2026); C. A. Athanasiadis, “On the real-rootedness of the
Eulerian transformation,” *J. London Math. Soc.* 111 (2025), e70083; P. Brändén and
K. Jochemko, “The Eulerian transformation,” *Trans. Amer. Math. Soc.* 375 (2022), 1917–1931;
P. Brändén and L. Solus, “Symmetric decompositions and real-rootedness,” *IMRN* 2021.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.
-/
