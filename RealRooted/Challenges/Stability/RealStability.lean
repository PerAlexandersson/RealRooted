module

import RealRooted.AffineLineRestriction
import RealRooted.DeterminantalStability
import RealRooted.Hyperbolicity
import RealRooted.HyperbolicityCone
import RealRooted.Multiaffine.Rayleigh
import RealRooted.MultivariateStability
import RealRooted.MultivariateStability.Inversion
import RealRooted.MultivariateStability.JumpSystem
import RealRooted.MultivariateStability.Lorentzian
import RealRooted.MultivariateStability.NegativeCorrelation
import RealRooted.MultivariateStability.RayleighConverse
import RealRooted.MultivariateStability.SamePhase
import RealRooted.SpanningTreeStability

/-!
# Real stability

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "real-stability"
formalized = "2026-10-12"
references = [
  "Garding1959",
  "ChoeOxleySokalWagner2004",
  "Branden2007",
  "BorceaBranden2008MixedDeterminants",
  "BorceaBrandenLiggett2008",
  "BrandenHuh2020",
]
authors = ["Gårding", "Choe", "Oxley", "Sokal", "Wagner", "Brändén", "Borcea",
  "Liggett", "Huh"]
years = [1959, 2004, 2007, 2008, 2020]

[[definitions]]
name = "RealRooted.MvRealStable"
module = "RealRooted.MultivariateStability"
label = "Real stable multivariate polynomial"

[[definitions]]
name = "MvPolynomial.IsRayleigh"
module = "RealRooted.Multiaffine.Rayleigh"
label = "Rayleigh property"

[[theorems]]
name = "RealRooted.MvPolynomial.IsMultiaffine.mvRealStable_iff_isRayleigh_and_ne_zero"
module = "RealRooted.MultivariateStability.RayleighConverse"
label = "Brändén: a multiaffine polynomial is real stable iff it is nonzero and Rayleigh"
headline = true

[[theorems]]
name = "RealRooted.mvRealStable_of_forall_realAffineLineRestriction"
module = "RealRooted.AffineLineRestriction"
label = "Real stability from real-rootedness of all positive-direction line restrictions"

[[theorems]]
name = "RealRooted.MvRealStable.samePhaseStable"
module = "RealRooted.MultivariateStability.SamePhase"
label = "Real stable polynomials are same-phase stable"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStableOrZero_detPencil"
module = "RealRooted.DeterminantalStability"
label = "Borcea–Brändén: det(A + Σ zᵢBᵢ) is stable or zero for Hermitian A and PSD Bᵢ"

[[theorems]]
objects = ["Spanning-tree polynomials"]
property = "real-stable"
name = "RealRooted.mvRealStable_spanningTreePoly"
module = "RealRooted.SpanningTreeStability"
label = "Choe–Oxley–Sokal–Wagner: spanning-tree polynomials are real stable"

[[theorems]]
name = "RealRooted.sum_mul_sum_le_of_mvRealStable_subsetGenPoly"
module = "RealRooted.MultivariateStability.NegativeCorrelation"
label = "Borcea–Brändén–Liggett: strongly Rayleigh measures are negatively correlated"

[[theorems]]
name = "RealRooted.MvRealStable.invertVariable"
module = "RealRooted.MultivariateStability.Inversion"
label = "Inversion $z^d P(-1/z)$ in one variable preserves real stability"

[[theorems]]
name = "RealRooted.MvPolynomial.IsHomogeneous.mvRealStable_iff_forall_hyperbolicAt_pos"
module = "RealRooted.Hyperbolicity"
label = "A homogeneous polynomial is real stable iff hyperbolic in every positive direction"

[[theorems]]
name = "RealRooted.convex_hyperbolicityCone"
module = "RealRooted.HyperbolicityCone"
label = "Gårding: hyperbolicity cones are convex"

[[theorems]]
name = "RealRooted.MvRealStable.isJumpSystem_supportInt"
module = "RealRooted.MultivariateStability.JumpSystem"
label = "Brändén: the support of a real stable polynomial is a jump system"

[[theorems]]
name = "RealRooted.MvRealStable.isLorentzian"
module = "RealRooted.MultivariateStability.Lorentzian"
label = "Brändén–Huh: nonnegative homogeneous real stable polynomials are Lorentzian"
-->

<!-- realrooted-catalog-content -->
# Real stability

A real polynomial in several variables is real stable if it has no zero with all variables in
the open upper half-plane; in one variable this is real-rootedness. Real stability is preserved
by many operations, holds for determinantal pencils, and for multiaffine polynomials it is
equivalent to the Rayleigh inequalities.

## Results

A polynomial $P\in\mathbb C[z_1,\dotsc,z_n]$ is *stable* if $P(z)\ne0$ whenever
$\operatorname{Im}z_i>0$ for all $i$, and *real stable* if moreover its coefficients are real.
It is *multiaffine* if it has degree at most one in each variable, and *Rayleigh* if
$\partial_iP\,\partial_jP-P\,\partial_i\partial_jP\ge0$ on $\mathbb R^n$ for all $i,j$. A real
polynomial is *hyperbolic* in the direction $e$ if $P(e)\ne0$ and $t\mapsto P(x+te)$ is
real-rooted for every $x\in\mathbb R^n$.

**Theorem (Brändén).** [@Branden2007] A multiaffine $P\in\mathbb R[z_1,\dotsc,z_n]$ is real
stable if and only if $P\ne0$ and $P$ is Rayleigh.

**Theorem (restrictions).** $P$ is real stable if and only if $t\mapsto P(a+tb)$ is nonzero
and real-rooted for all $a\in\mathbb R^n$ and $b\in\mathbb R_{>0}^n$. If $P$ is real stable, then
$P(w_1t,\dotsc,w_nt)$ is real-rooted for every $w$ with all $w_i\ge0$, and
$z_1^dP(-1/z_1,z_2,\dots,z_n)$ is real stable when $\deg_{z_1}P\le d$.

**Theorem (Borcea–Brändén; Choe–Oxley–Sokal–Wagner).**
[@BorceaBranden2008MixedDeterminants; @ChoeOxleySokalWagner2004] If $A$ is Hermitian and
$B_1,\dotsc,B_n$ are positive semidefinite, then $\det(A+z_1B_1+\dotsb+z_nB_n)$ is stable or
zero. In particular the spanning-tree polynomial $\sum_T\prod_{e\in T}z_e$ of a connected graph,
which is the determinant of a reduced weighted Laplacian, is real stable.

**Corollary (Borcea–Brändén–Liggett).** [@BorceaBrandenLiggett2008] If the generating polynomial
$\sum_S\mu(S)\prod_{i\in S}z_i$ of a weight function $\mu$ on subsets is real stable, then
$\mu(\Omega)\,\mu(i,j\in S)\le\mu(i\in S)\,\mu(j\in S)$ for $i\ne j$.

**Theorem (hyperbolicity; Gårding).** [@Garding1959] A homogeneous $P$ is real stable if and
only if it is hyperbolic in every direction $e$ with all $e_i>0$. The hyperbolicity cone of a
homogeneous polynomial hyperbolic in the direction $e$, the component of $e$ in
$\{x:P(x)\ne0\}$, is convex.

**Theorem (supports; Brändén–Huh).** [@Branden2007; @BrandenHuh2020] The support of a real
stable polynomial is a jump system, and a homogeneous real stable polynomial with nonnegative
coefficients is Lorentzian.

## Use

If $P$ is real stable, then $P(t,\dots,t)$ is real-rooted, so real-rootedness can be proved by
building a multivariate polynomial with closure operations and specializing. This is the setting
of the [Borcea–Brändén classification](rr:borcea-branden-classification), of
[mixed characteristic polynomials](rr:finite-free-convolutions) and of
[monotone column permanents](rr:monotone-column-permanent).

## Proof

If $v\ne0$ lies in the kernel of $M=A+\sum_iz_iB_i$ with all $\operatorname{Im}z_i>0$, then
$\operatorname{Im}(v^*Mv)=\sum_i\operatorname{Im}(z_i)\,v^*B_iv=0$ forces $B_iv=0$ and $Av=0$,
so the pencil vanishes identically. Inversion uses that $z\mapsto-1/z$ maps the upper
half-plane to itself. Negative correlation is the Rayleigh inequality at the all-ones point.

## References

[@Garding1959]; [@ChoeOxleySokalWagner2004]; [@Branden2007];
[@BorceaBranden2008MixedDeterminants]; [@BorceaBrandenLiggett2008]; [@BrandenHuh2020]. See also
[stable polynomials](sf:stablePolynomialDefinition) and the
[Rayleigh property](sf:stronglyRayleighProperty) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
