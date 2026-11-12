module

public import RealRooted.AffineLineRestriction
public import RealRooted.BoundarySpecializationGeneral
public import RealRooted.DeterminantalStability
public import RealRooted.HomogeneousComponentStability
public import RealRooted.HomogeneousStability
public import RealRooted.Hyperbolicity
public import RealRooted.Hyperbolicity.SignFree
public import RealRooted.HyperbolicityCone
public import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
public import RealRooted.Mathlib.Combinatorics.SimpleGraph.MatrixTree
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic
public import RealRooted.Multiaffine
public import RealRooted.Multiaffine.AffineCoordinateCriterion
public import RealRooted.Multiaffine.AffineLineRestriction
public import RealRooted.Multiaffine.CoordinateWronskian
public import RealRooted.Multiaffine.Rayleigh
public import RealRooted.Multiaffine.Reciprocal
public import RealRooted.MultivariateStability
public import RealRooted.MultivariateStability.ExpectedCharpoly
public import RealRooted.MultivariateStability.Inversion
public import RealRooted.MultivariateStability.JumpSystem
public import RealRooted.MultivariateStability.Lorentzian
public import RealRooted.MultivariateStability.MSSBound
public import RealRooted.MultivariateStability.MixedCharacteristic
public import RealRooted.MultivariateStability.NegativeCorrelation
public import RealRooted.MultivariateStability.RayleighConverse
public import RealRooted.MultivariateStability.SamePhase
public import RealRooted.SamePhaseStability
public import RealRooted.SpanningTreeStability

/-!
# Real stability challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "real-stability"
formalized = "2026-10-12"
tags = []
references = [
  "ChoeOxleySokalWagner2004",
  "Branden2007",
  "BorceaBranden2008MixedDeterminants",
  "BorceaBrandenLiggett2008",
  "MarcusSpielmanSrivastava2015II",
  "BrandenHuh2020",
  "Garding1959",
]
authors = ["Gårding", "Choe", "Oxley", "Sokal", "Wagner", "Brändén", "Borcea",
  "Liggett", "Marcus", "Spielman", "Srivastava", "Huh"]
years = [1959, 2004, 2007, 2008, 2009, 2015, 2020]

[[definitions]]
name = "RealRooted.MvUpperHalfPlaneStable"
module = "RealRooted.MultivariateStability"
label = "Stable multivariate polynomial"

[[definitions]]
name = "RealRooted.MvRealStable"
module = "RealRooted.MultivariateStability"
label = "Real stable multivariate polynomial"

[[definitions]]
name = "MvPolynomial.IsMultiaffine"
module = "RealRooted.Multiaffine"
label = "Multiaffine polynomial"

[[definitions]]
name = "MvPolynomial.IsRayleigh"
module = "RealRooted.Multiaffine.Rayleigh"
label = "Rayleigh property"

[[definitions]]
name = "MvPolynomial.HyperbolicAt"
module = "RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic"
label = "Hyperbolic in a direction"

[[definitions]]
name = "RealRooted.invertVariable"
module = "RealRooted.MultivariateStability.Inversion"
label = "Inversion z^d P(−1/z) in one variable"

[[definitions]]
name = "RealRooted.mvDetPencil"
module = "RealRooted.DeterminantalStability"
label = "Determinant of a linear matrix pencil"

[[definitions]]
name = "RealRooted.MvUpperHalfPlaneStableOrZero"
module = "RealRooted.MultivariateStability"
label = "Stable or zero"

[[definitions]]
name = "MvPolynomial.coordinateWronskian"
module = "RealRooted.Multiaffine.CoordinateWronskian"
label = "Coordinate Wronskian"

[[definitions]]
name = "RealRooted.MvCommonRotationStable"
module = "RealRooted.HomogeneousStability"
label = "Common-rotation stability"

[[theorems]]
name = "RealRooted.MvPolynomial.IsMultiaffine.mvRealStable_iff_isRayleigh_and_ne_zero"
module = "RealRooted.MultivariateStability.RayleighConverse"
label = "A multiaffine polynomial is real stable iff it is Rayleigh"
headline = true

[[theorems]]
name = "RealRooted.sum_mul_sum_le_of_mvRealStable_subsetGenPoly"
module = "RealRooted.MultivariateStability.NegativeCorrelation"
label = "Strongly Rayleigh measures are negatively correlated"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStableOrZero_detPencil"
module = "RealRooted.DeterminantalStability"
label = "Determinantal pencils are stable or zero"

[[theorems]]
name = "RealRooted.MvPolynomial.IsHomogeneous.mvRealStable_iff_forall_hyperbolicAt_pos"
module = "RealRooted.Hyperbolicity"
label = "A homogeneous polynomial is real stable iff it is hyperbolic in every positive direction"

[[theorems]]
name = "RealRooted.convex_hyperbolicityCone"
module = "RealRooted.HyperbolicityCone"
label = "Gårding: hyperbolicity cones are convex"

[[theorems]]
name = "RealRooted.mvRealStable_realDetPencil_of_ne"
module = "RealRooted.DeterminantalStability"
label = "Real determinantal pencils are real stable"

[[theorems]]
name = "RealRooted.mvRealStable_spanningTreePoly"
module = "RealRooted.SpanningTreeStability"
label = "Choe–Oxley–Sokal–Wagner: spanning-tree polynomials are real stable"

[[theorems]]
name = "SimpleGraph.det_weightedLapMatrix_submatrix"
module = "RealRooted.Mathlib.Combinatorics.SimpleGraph.MatrixTree"
label = "Kirchhoff's weighted matrix-tree theorem"

[[theorems]]
name = "RealRooted.MvRealStable.ordinaryHomogenization"
module = "RealRooted.Hyperbolicity"
label = "Homogenization preserves real stability"

[[theorems]]
name = "RealRooted.MvRealStable.homogeneousComponent_totalDegree_of_hasNonnegCoeffs"
module = "RealRooted.HomogeneousComponentStability"
label = "The top homogeneous component of a real stable polynomial is real stable"

[[theorems]]
name = "RealRooted.MvRealStable.samePhaseStable"
module = "RealRooted.MultivariateStability.SamePhase"
label = "Real stable polynomials are same-phase stable"

[[theorems]]
name = "RealRooted.IsUpperHalfPlaneStable.reflect_comp_neg_X"
module = "RealRooted.MultivariateStability.Inversion"
label = "Inversion preserves stability of univariate polynomials"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.invertVariable"
module = "RealRooted.MultivariateStability.Inversion"
label = "Inversion in one variable preserves stability"

[[theorems]]
name = "RealRooted.MvRealStable.invertVariable"
module = "RealRooted.MultivariateStability.Inversion"
label = "Inversion in one variable preserves real stability"

[[theorems]]
name = "RealRooted.mvRealStable_of_forall_realAffineLineRestriction"
module = "RealRooted.AffineLineRestriction"
label = "Real stability from real-rootedness of all positive-direction line restrictions"

[[theorems]]
name = "RealRooted.MvRealStable.realAffineLineRestriction_splits_ne_zero"
module = "RealRooted.AffineLineRestriction"
label = "Line restrictions of a real stable polynomial in positive directions are real-rooted"

[[theorems]]
name = "RealRooted.MvRealStable.isJumpSystem_supportInt"
module = "RealRooted.MultivariateStability.JumpSystem"
label = "Brändén: the support of a real stable polynomial is a jump system"

[[theorems]]
name = "RealRooted.MvRealStable.isBase_supportMatroid_iff"
module = "RealRooted.MultivariateStability.JumpSystem"
label = "Brändén: supports of a homogeneous multi-affine real stable polynomial are matroid bases"

[[theorems]]
name = "RealRooted.MvRealStable.isLorentzian"
module = "RealRooted.MultivariateStability.Lorentzian"
label = "Brändén–Huh: nonnegative homogeneous real stable polynomials are Lorentzian"

[[theorems]]
name = "RealRooted.MixedCharacteristic.isRealRooted_mixedCharacteristic"
module = "RealRooted.MultivariateStability.MixedCharacteristic"
label = "Marcus–Spielman–Srivastava: mixed characteristic polynomials are real-rooted"

[[theorems]]
name = "RealRooted.MixedCharacteristic.mixedCharacteristic_roots_le_one_add_sqrt_sq"
module = "RealRooted.MultivariateStability.MSSBound"
label = "Marcus–Spielman–Srivastava: the roots of μ[A] are at most (1 + √ε)²"

[[theorems]]
name = "RealRooted.MixedCharacteristic.expectedCharpoly_eq_mixedCharacteristic"
module = "RealRooted.MultivariateStability.ExpectedCharpoly"
label = "MSS: expected characteristic polynomials are mixed characteristic"

[[theorems]]
name = "RealRooted.MvPolynomial.HyperbolicAt.of_joinedIn"
module = "RealRooted.Hyperbolicity"
label = "Hyperbolicity is constant on path components of the nonvanishing locus"

[[theorems]]
name = "RealRooted.MvRealStable.homogeneousComponent_totalDegree"
module = "RealRooted.Hyperbolicity.SignFree"
label = "The top homogeneous component of any real stable polynomial is real stable"

[[theorems]]
name = "RealRooted.MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary"
module = "RealRooted.Hyperbolicity.SignFree"
label = "Ordinary homogenization is hyperbolic in every boundary direction"

[[theorems]]
name = "RealRooted.MvRealStable.ordinaryHomogenization_of_totalDegree_le"
module = "RealRooted.Hyperbolicity"
label = "Homogenization in any degree at least the total degree preserves real stability"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.specializeAt_real_zero_or_general"
module = "RealRooted.BoundarySpecializationGeneral"
label = "Specializing a coordinate at a real value gives a stable polynomial or zero"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStableOrZero.specializeAtList_real_general"
module = "RealRooted.BoundarySpecializationGeneral"
label = "Specializing several coordinates at real values preserves stability or zero"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.specializeRight_zero_or_general"
module = "RealRooted.BoundarySpecializationGeneral"
label = "Setting a finite block of variables to zero gives a stable polynomial or zero"

[[theorems]]
name = "MvPolynomial.isRayleigh_add_X_mul_iff_of_fresh"
module = "RealRooted.Multiaffine.AffineCoordinateCriterion"
label = "Exact Rayleigh criterion for a fresh affine extension"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.signedMultiaffineReciprocal"
module = "RealRooted.Multiaffine.Reciprocal"
label = "The signed multiaffine reciprocal preserves stability"

[[theorems]]
name = "MvPolynomial.coordinateWronskian_plucker"
module = "RealRooted.Multiaffine.CoordinateWronskian"
label = "Plücker relation for coordinate Wronskians"

[[theorems]]
name = "RealRooted.MvPolynomial.IsRayleigh.laguerre_realAffineLineRestriction"
module = "RealRooted.Multiaffine.AffineLineRestriction"
label = "Laguerre's inequality for line restrictions of Rayleigh polynomials"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_iff_commonRotation_dehomogenize"
module = "RealRooted.HomogeneousStability"
label = "A homogeneous polynomial is stable iff its dehomogenization is common-rotation stable"

[[theorems]]
name = "RealRooted.mvRealStable_iff_commonRotation_dehomogenize"
module = "RealRooted.HomogeneousStability"
label = "Real-stable analogue of the common-rotation criterion"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_ordinaryHomogenization_iff"
module = "RealRooted.HomogeneousStability"
label = "Ordinary homogenization is stable iff the source is common-rotation stable"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.pderiv_none_of_top_coeff_C"
module = "RealRooted.HomogeneousStability"
label = "Differentiation in a variable with constant leading coefficient preserves stability"
-->

<!-- realrooted-catalog-content -->
# Real stability

A multiaffine real polynomial is real stable if and only if it is Rayleigh; real stability is
preserved by determinantal pencils, homogenization, specialization and inversion, and gives
hyperbolicity, matroid supports and Lorentzian polynomials.

## Results

A polynomial $P\in\mathbb C[z_1,\dotsc,z_n]$ is *stable* if $P(z)\ne0$ whenever
$\operatorname{Im}z_i>0$
for all $i$; in particular $P\ne0$. A polynomial with real coefficients is *real stable* if it is
stable as a complex polynomial. It is *multiaffine* if it has degree at most one in each variable,
and *Rayleigh* if
$$\partial_iP\,\partial_jP-P\,\partial_i\partial_jP\ge0$$
at every $x\in\mathbb R^n$ and for all $i,j$. A real polynomial $P$ is *hyperbolic* in the direction
$e\in\mathbb R^n$ if $P(e)\ne0$ and $t\mapsto P(x+te)$ is real-rooted for every $x\in\mathbb R^n$.

**Theorem (Brändén)** [@Branden2007]. A multiaffine $P\in\mathbb R[z_1,\dotsc,z_n]$ is real stable
if and only if $P\ne0$ and $P$ is Rayleigh.

**Corollary (Borcea–Brändén–Liggett)** [@BorceaBrandenLiggett2008]. Let $\mu$ be a weight function
on the subsets of $\{1,\dotsc,n\}$ whose generating polynomial $\sum_S\mu(S)\prod_{i\in S}z_i$ is
real stable. Then for $i\ne j$,
$$\mu(\Omega)\,\mu(i,j\in S)\le\mu(i\in S)\,\mu(j\in S).$$
For a probability measure this is pairwise negative correlation; it is the Rayleigh inequality at
the all-ones point.

**Theorem (Borcea–Brändén)** [@BorceaBranden2008MixedDeterminants]. Let $A$ be a Hermitian
$m\times m$ matrix and $B_1,\dotsc,B_n$ positive semidefinite $m\times m$ matrices. Then
$\det(A+z_1B_1+\dotsb+z_nB_n)$ is stable or identically zero. If all matrices are real and the
determinant is not identically zero, it is real stable.

**Corollary (Choe–Oxley–Sokal–Wagner)** [@ChoeOxleySokalWagner2004]. If a finite graph $G$ has a
spanning tree, its spanning-tree polynomial $\sum_T\prod_{e\in T}z_e$ is real stable. By Kirchhoff's
weighted matrix-tree theorem it equals the determinant of the reduced Laplacian
$\sum_ez_eb_eb_e^{T}$, a pencil of positive semidefinite rank-one matrices.

**Theorem (hyperbolicity).** A homogeneous $P\in\mathbb R[z_1,\dotsc,z_n]$ is real stable if and
only if it is hyperbolic in every direction $e$ with all $e_i>0$. If a homogeneous $P$ is
hyperbolic in the direction $e$, then it is hyperbolic in every direction $u$ joined to $e$ by a
path in $\{x:P(x)\ne0\}$.

**Theorem (Gårding)** [@Garding1959]. If a homogeneous $P$ is hyperbolic in the direction $e$, its
hyperbolicity cone, the path component of $e$ in $\{x:P(x)\ne0\}$, is convex.

**Theorem (homogenization).** Let $P\ne0$ be real stable with nonnegative coefficients and total
degree $d$. Then $z_0^dP(z_1/z_0,\dotsc,z_n/z_0)$ and the top homogeneous component of $P$ are real
stable. The homogenization in any degree at least $d$ is also real stable.

**Theorem (top component without sign hypothesis).** If $P$ is real stable, then its top
homogeneous component is real stable, and the homogenization
$z_0^dP(z_1/z_0,\dotsc,z_n/z_0)$, with $d$ the total degree of $P$, is hyperbolic in the direction
$(0,b)$ for every $b\in\mathbb R^n$ with all $b_i>0$. In particular the top component does not
vanish at such $b$.

**Theorem (same-phase stability).** If $P$ is real stable, then for every $w\in\mathbb R^n$ with all
$w_i\ge0$ the polynomial $P(w_1t,\dotsc,w_nt)$ is real-rooted.

**Theorem (line restrictions).** $P$ is real stable if and only if, for all $a\in\mathbb R^n$ and
$b\in\mathbb R_{>0}^n$, the restriction $t\mapsto P(a+tb)$ is nonzero and real-rooted.

**Theorem (inversion).** Let $P$ be a stable polynomial in a variable $z_0$ and further variables,
of degree at most $d$ in $z_0$. Then $z_0^dP(-1/z_0,\dotsc)$ is stable, and real stable if $P$
is. For one variable: if $p$ has no zeros in the open upper half-plane and $\deg p\le d$, then
$z^dp(-1/z)$ has none.

**Theorem (specialization).** Let $P$ be stable and $c$ real. Then $P$ with the variable $z_i$
replaced by $c$ is stable or identically zero, with no bound on the degree of $P$ in $z_i$. The same
holds for repeated specialization of several variables at real values, and for setting a finite
block of variables to zero.

**Theorem (differentiation).** Let $P$ be stable in $z_0,z_1,\dotsc,z_n$, of degree at most
$m\ge1$ in $z_0$, and suppose the coefficient of $z_0^m$ is a nonzero constant. Then
$\partial P/\partial z_0$ is stable.

**Theorem (common-rotation criterion).** Call a complex polynomial $Q$ *common-rotation stable* if
$Q(z)\ne0$ whenever some single $c$ with $\operatorname{Im}c>0$ satisfies
$\operatorname{Im}(cz_i)>0$
for all $i$. A homogeneous polynomial $P$ in $z_0,z_1,\dotsc,z_n$ is stable if and only if
$P(1,z_1,\dotsc,z_n)$ is common-rotation stable; for a homogeneous real polynomial the same holds
for real stability. The ordinary homogenization of $p$ in any degree at least $\deg p$ is stable if
and only if $p$ is common-rotation stable.

**Theorem (multiaffine tools).** Let $P$ and $Q$ be multiaffine polynomials not involving $z_k$.
Write $W_i(Q,P)=Q\,\partial_iP-P\,\partial_iQ$ for the coordinate Wronskian,
$R_{ij}(F)=\partial_iF\,\partial_jF-F\,\partial_i\partial_jF$ for the Rayleigh difference, and
$M_{ij}=\partial_iP\,\partial_jQ+\partial_iQ\,\partial_jP
-P\,\partial_i\partial_jQ-Q\,\partial_i\partial_jP$.
Then $P+z_kQ$ is Rayleigh if and only if

* $P$ and $Q$ are Rayleigh,
* $W_i(Q,P)(x)\ge0$ for all $i$ and $x\in\mathbb R^n$, and
* $M_{ij}^2-4R_{ij}(Q)R_{ij}(P)\le0$ at every $x\in\mathbb R^n$, for all $i,j\ne k$.

The Wronskians satisfy the Plücker relation
$W_i(P,A)\,W_i(Q,B)=W_i(P,Q)\,W_i(A,B)+W_i(P,B)\,W_i(Q,A)$. If $P\in\mathbb C[z_1,\dotsc,z_n]$ is
multiaffine and stable, so is $z\mapsto\prod_iz_i\,P(-1/z_1,\dotsc,-1/z_n)$. If $P$ is Rayleigh,
$a\in\mathbb R^n$ and $b\in\mathbb R^n$ has nonnegative entries, then $p(t)=P(a+tb)$ satisfies
$p'(t)^2-p(t)\,p''(t)\ge0$ for all real $t$.

**Theorem (Brändén).** [@Branden2007] The support of a real stable polynomial is a jump system:
for support points $\alpha,\beta$ and a unit step $s=\pm e_i$ from $\alpha$ towards $\beta$, either
$\alpha+s$ is in the support, or some further unit step $t$ towards $\beta$ has $\alpha+s+t$ in the
support.

**Corollary (Brändén).** If $P$ is homogeneous, multiaffine and real stable, its support is the set
of bases of a matroid: $B$ is a basis exactly when its indicator vector lies in the support of $P$.

**Theorem (Brändén–Huh)** [@BrandenHuh2020]. A homogeneous real stable polynomial with nonnegative
coefficients is Lorentzian.

**Theorem (mixed characteristic polynomials).** For real positive semidefinite matrices $A_i$, the
mixed characteristic polynomial
$$\mu[A](x)=\prod_i(1-\partial_{z_i})\det\Bigl(xI+\sum_iz_iA_i\Bigr)\Big|_{z=0}$$
is nonzero and real-rooted.

**Theorem (Marcus–Spielman–Srivastava)** [@MarcusSpielmanSrivastava2015II]. Let $A_1,\dotsc,A_m$ be
real positive semidefinite $n\times n$ matrices with $\sum_iA_i=I$ and
$\operatorname{tr}A_i\le\varepsilon$,
where $\varepsilon>0$. Then every root of $\mu[A]$ is at most $(1+\sqrt\varepsilon)^2$. This is the
root bound behind the solution of the Kadison–Singer problem.

**Theorem (MSS, Thm. 4.1)** [@MarcusSpielmanSrivastava2015II, Thm. 4.1]. The expected
characteristic polynomial of a sum of independent random rank-one matrices equals the mixed
characteristic polynomial of their second-moment matrices.

## Proof

For determinantal pencils, suppose $M=A+\sum_iz_iB_i$ is singular with all
$\operatorname{Im}z_i>0$ and
let $v\ne0$ be in its kernel. The imaginary part of $v^*Mv$ is
$\sum_i\operatorname{Im}(z_i)\,v^*B_iv$, so
each $v^*B_iv$ vanishes. Hence $B_iv=0$ and $Av=0$, so the pencil is singular everywhere. Inversion
works because $\operatorname{Im}(-1/z)=\operatorname{Im}z/|z|^2$, so $z\mapsto-1/z$ maps the open
upper
half-plane to itself. For a fresh affine extension $P+z_kQ$ and $i,j\ne k$, the Rayleigh difference
is a quadratic in $z_k$ with coefficients $R_{ij}(P)$, $M_{ij}$ and $R_{ij}(Q)$; for $i=k$ it equals
$W_j(Q,P)$, independent of $z_k$. The root bound for $\mu[A]$ follows the barrier argument of
Marcus, Spielman and Srivastava, with the Helton–Vinnikov step replaced by an elementary
Pick-function lemma.

## References

See [@Garding1959; @ChoeOxleySokalWagner2004; @Branden2007; @BorceaBranden2008MixedDeterminants;
@BorceaBrandenLiggett2008; @MarcusSpielmanSrivastava2015II; @BrandenHuh2020]. See also the
[stable polynomials](sf:stablePolynomialDefinition) and the
[Rayleigh property](sf:stronglyRayleighProperty) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes the multiaffine Rayleigh criterion, determinantal
stability, hyperbolicity of homogeneous real stable polynomials, the
homogenization, top-component and same-phase consequences, and inversion in
one variable.
-/
