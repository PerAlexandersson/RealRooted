module

import RealRooted.Applications.BinderVecchi.UniformChow
import RealRooted.Applications.BinderVecchi.UniformMatroid
import RealRooted.BrandenVecchi.Chow
import RealRooted.BrandenVecchi.ChowInfinitePF
import RealRooted.BrandenVecchi.ChowTotallyNonneg
import RealRooted.HosterStump.Chow
import RealRooted.HosterStump.PosetBasic
import RealRooted.HosterStump.PosetChow

/-!
# Chow polynomials of posets and matroids

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "chow-polynomials"
formalized = "2026-09-12"
references = [
  "BrandenVecchi2025x",
  "HosterStump2025x",
  {key = "BinderVecchi2026x", at = "Thms. 1.4 and 1.6"},
]
authors = ["Brändén", "Vecchi", "Hoster", "Stump", "Binder"]
years = [2025, 2026]

[[definitions]]
name = "RealRooted.BrandenVecchi.chowPolynomial"
module = "RealRooted.BrandenVecchi.Chow"
label = "Chow polynomials of a lower-triangular matrix"

[[definitions]]
name = "RealRooted.BrandenVecchi.chowDerangement"
module = "RealRooted.BrandenVecchi.Chow"
label = "Chow derangement polynomials"

[[definitions]]
name = "RealRooted.HosterStump.IsSimplicialPoset"
module = "RealRooted.HosterStump.PosetBasic"
label = "Simplicial poset: every lower interval is Boolean, every element lies below rank n"

[[definitions]]
name = "RealRooted.HosterStump.chowOfFlagH"
module = "RealRooted.HosterStump.Chow"
label = "Chow polynomial of a flag h-vector"

[[definitions]]
name = "RealRooted.BinderVecchi.refinedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Refined Hodge–Poincaré polynomial of a uniform matroid"

[[theorems]]
objects = ["Chow polynomials of totally nonnegative matrices"]
property = "interlacing"
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Brändén–Vecchi: consecutive Chow polynomials of a TNN matrix interlace"
headline = true

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Each Chow polynomial of a TNN matrix is zero or real-rooted"

[[theorems]]
objects = ["Chow derangement polynomials of totally nonnegative matrices"]
name = "RealRooted.BrandenVecchi.chowDerangement_eq_zero_or_splits_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "Each Chow derangement polynomial of a TNN matrix is zero or real-rooted"

[[theorems]]
name = "RealRooted.BrandenVecchi.chowPolynomial_interl_chowDerangement_of_isTotallyNonneg"
module = "RealRooted.BrandenVecchi.ChowTotallyNonneg"
label = "The Chow polynomial $c_n$ interlaces the Chow derangement polynomial $d_n$"

[[theorems]]
name = "RealRooted.BrandenVecchi.aissenSchoenbergWhitneyEdreiChow_isPFPolynomial"
module = "RealRooted.BrandenVecchi.ChowInfinitePF"
label = "Pólya frequency symbols give Pólya frequency Chow polynomials"

[[theorems]]
objects = ["Chow polynomials of simplicial posets"]
name = "RealRooted.HosterStump.isRealRooted_chowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "Hoster–Stump: a simplicial poset with h ≥ 0 has a real-rooted Chow polynomial"

[[theorems]]
objects = ["Augmented Chow polynomials of simplicial posets"]
name = "RealRooted.HosterStump.isRealRooted_augChowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "The augmented Chow polynomial of such a poset is real-rooted"

[[theorems]]
name = "RealRooted.HosterStump.strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH_flagH"
module = "RealRooted.HosterStump.PosetChow"
label = "For n ≥ 1, the dual Chow polynomial interlaces the augmented one"

[[theorems]]
objects = ["Refined Hodge–Poincaré polynomials of uniform matroids"]
name = "RealRooted.BinderVecchi.isRealRooted_refinedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Binder–Vecchi: refined Hodge–Poincaré polynomials of $U_{r,n}$ are real-rooted"

[[theorems]]
name = "RealRooted.BinderVecchi.isRealRooted_modifiedAugmentedHodgePoincare"
module = "RealRooted.Applications.BinderVecchi.UniformMatroid"
label = "Binder–Vecchi: the modified augmented family is real-rooted"

[[theorems]]
objects = ["Chow polynomials of uniform matroids"]
name = "RealRooted.UniformChow.isRealRooted_chowUniform"
module = "RealRooted.Applications.BinderVecchi.UniformChow"
label = "The Chow polynomial of $U_{r,n}$ is real-rooted"

[[theorems]]
objects = ["Augmented Chow polynomials of uniform matroids"]
name = "RealRooted.UniformChow.isRealRooted_augChowUniform"
module = "RealRooted.Applications.BinderVecchi.UniformChow"
label = "The augmented Chow polynomial of $U_{r,n}$ is real-rooted"
-->

<!-- realrooted-catalog-content -->
# Chow polynomials of posets and matroids

The Chow polynomial of a matroid is the Hilbert series of its Chow ring. P. Brändén and L. Vecchi
define Chow polynomials for every lower-triangular matrix and prove that they are real-rooted and
interlace when the matrix is totally nonnegative. Related theorems of Hoster–Stump and
Binder–Vecchi cover simplicial posets and uniform matroids.

## Results

We use the [zero-aware interlacing convention](rr:about). For a lower-triangular matrix $A$, the
*Chow derangement polynomials* are $d_0=1$ and
$$
d_n=x\,S_{n-1}\Bigl(\sum_{k<n}A(n,k)\,d_k\Bigr),\qquad
S_m(q)=\frac{x^mq(1/x)-q}{x-1}\quad(n\ge1),
$$
and the *Chow polynomials* are $c_n=\sum_{k\le n}A(n,k)\,d_k$. For the incidence data of a
poset these are the Chow polynomials of posets and matroids; see the
[definition on symmetricfunctions.com](sf:chowPolynomialDefinition).

**Theorem (Brändén–Vecchi).** [@BrandenVecchi2025x] Let $A$ be lower unitriangular and totally
nonnegative. Then $c_n$ and $d_n$ have nonnegative coefficients and each is zero or real-rooted,
$c_n\ll c_{n+1}$ and $c_n\ll d_n$. If $A$ is the Toeplitz matrix of a Pólya frequency series
$e^{\gamma z}\prod_i(1+\alpha_iz)/\prod_i(1-\beta_iz)$, every $c_n$ is a Pólya frequency
polynomial.

Let $P$ be a finite graded poset of rank $n$ with bottom element in which every lower interval is
Boolean and every element lies below one of rank $n$ (a *simplicial poset*), and let $\hat P$ be
$P$ with a top element added.

**Theorem (Hoster–Stump).** [@HosterStump2025x] If the $h$-vector of $P$ is nonnegative, then
the Chow polynomial, the dual Chow polynomial and the augmented Chow polynomial of $\hat P$ are
nonzero and real-rooted. For $n\ge1$ the dual Chow polynomial interlaces the augmented one.

**Theorem (Binder–Vecchi).** [@BinderVecchi2026x, Thms. 1.4 and 1.6] For the uniform matroid
$U_{r,n}$ and $1\le i\le n-r$, the refined Hodge–Poincaré polynomial $\underline H^i_{r,n}$ and
its modified augmented variant are nonzero and real-rooted. The case $i=0$ gives the Chow and
augmented Chow polynomials of $U_{r,n}$, which are real-rooted as well.

## Use

Hoster and Stump's theorem applies to Cohen–Macaulay simplicial posets and to the lattices of
flats of uniform matroids. The derangement transform of the
[Brändén–Solus theorem](rr:branden-solus) is the Chow derangement transform of the Pascal
matrix.

## Proof

Brändén and Vecchi resolve a totally nonnegative matrix by Whitney elimination, as on the
[Brändén–Saud Leite page](rr:branden-leite). Hoster and Stump write the $\gamma$-polynomials of
the three Chow polynomials through refined descent polynomials, using Stanley's formula for the
flag $h$-vector, and show that these form interlacing diagrams. Binder and Vecchi write
$\underline H^i_{r,n}$ as a reversed derangement transform and the augmented variant as a
reversed Eulerian transform of a polynomial with nonnegative coordinates in the basis
$x^p(1+x)^{r-1-p}$; both transforms are real-rooted on that cone
[@BrandenSolus2019; @Athanasiadis2025EulerianTransformation].

## References

[@BrandenVecchi2025x]; [@HosterStump2025x]; [@BinderVecchi2026x, Thms. 1.4 and 1.6];
[@BrandenSolus2019]; [@Athanasiadis2025EulerianTransformation]; R. P. Stanley, *Combinatorics
and Commutative Algebra*, 2nd ed., Birkhäuser, 1996, III.6.
<!-- /realrooted-catalog-content -->
-/
