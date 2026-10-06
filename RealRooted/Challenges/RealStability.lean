import RealRooted.DeterminantalStability
import RealRooted.HomogeneousComponentStability
import RealRooted.Hyperbolicity
import RealRooted.MultivariateStability.RayleighConverse
import RealRooted.MultivariateStability.SamePhase

/-!
# Real stability challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "real-stability"
authors = ["Brändén", "Borcea", "Gårding"]
years = [1959, 2007, 2008]

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
name = "RealRooted.detPencil"
module = "RealRooted.DeterminantalStability"
label = "Determinant of a linear matrix pencil"

[[theorems]]
name = "RealRooted.Challenges.RealStability.mvRealStable_iff_isRayleigh"
label = "A multiaffine polynomial is real stable iff it is Rayleigh"
headline = true

[[theorems]]
name = "RealRooted.Challenges.RealStability.detPencil_eq_zero_or_stable"
label = "Determinantal pencils are stable or zero"
headline = true

[[theorems]]
name = "RealRooted.Challenges.RealStability.mvRealStable_iff_forall_hyperbolicAt"
label = "A homogeneous polynomial is real stable iff it is hyperbolic in every positive direction"
headline = true

[[theorems]]
name = "RealRooted.Challenges.RealStability.mvRealStable_realDetPencil"
label = "Real determinantal pencils are real stable"

[[theorems]]
name = "RealRooted.Challenges.RealStability.mvRealStable_ordinaryHomogenization"
label = "Homogenization preserves real stability"

[[theorems]]
name = "RealRooted.Challenges.RealStability.mvRealStable_homogeneousComponent_totalDegree"
label = "The top homogeneous component of a real stable polynomial is real stable"

[[theorems]]
name = "RealRooted.Challenges.RealStability.samePhaseStable"
label = "Real stable polynomials are same-phase stable"
-->

<!-- realrooted-catalog-content -->
# Real stability

A polynomial $P \in \mathbb{C}[z_1, \dotsc, z_n]$ is **stable** if
$P(z) \neq 0$ whenever $\operatorname{Im} z_i > 0$ for all $i$; in particular
$P \neq 0$. A polynomial with real coefficients is **real stable** if it is
stable as a complex polynomial. It is **multiaffine** if it has degree at most
one in each variable.

**Theorem** (Brändén). A multiaffine $P \in \mathbb{R}[z_1, \dotsc, z_n]$ is
real stable if and only if $P \neq 0$ and
$$
\frac{\partial P}{\partial z_i}(x) \frac{\partial P}{\partial z_j}(x) -
P(x) \frac{\partial^2 P}{\partial z_i \partial z_j}(x) \geq 0
$$
for all $i$, $j$ and all $x \in \mathbb{R}^n$ (the Rayleigh property).
No homogeneity is needed.

**Theorem** (Borcea–Brändén). Let $A$ be a Hermitian $m \times m$ matrix and
let $B_1, \dotsc, B_n$ be positive semidefinite $m \times m$ matrices. Then
$\det(A + z_1 B_1 + \dotsb + z_n B_n)$ is stable or identically zero. If all
matrices are real and the determinant is not identically zero, then it is
real stable.

A polynomial $P \in \mathbb{R}[z_1, \dotsc, z_n]$ is **hyperbolic** in the
direction $e \in \mathbb{R}^n$ if $P(e) \neq 0$ and $t \mapsto P(x + t e)$ is
real-rooted for every $x \in \mathbb{R}^n$.

**Theorem.** A homogeneous $P \in \mathbb{R}[z_1, \dotsc, z_n]$ is real stable
if and only if it is hyperbolic in every direction $e$ with all $e_i > 0$.

**Theorem.** Let $P \neq 0$ be real stable with nonnegative coefficients and
total degree $d$. Then its homogenization
$z_0^d P(z_1/z_0, \dotsc, z_n/z_0)$ and its top homogeneous component, the
part of degree $d$, are real stable.

**Theorem.** If $P$ is real stable, then $P$ is same-phase stable: for every
$w \in \mathbb{R}^n$ with all $w_i \geq 0$, the univariate polynomial
$P(w_1 t, \dotsc, w_n t)$ is real-rooted.

## Proof idea

For the Rayleigh criterion, the forward direction reduces each inequality to
the bivariate case by specializing the other variables. The converse is an
induction on the variables that occur, with a one-variable pencil argument at
each step. For determinantal pencils, suppose that $M = A + \sum_i z_i B_i$
is singular with all $\operatorname{Im} z_i > 0$, and let $v \neq 0$ be in
its kernel. The imaginary part of $v^* M v$ is
$\sum_i \operatorname{Im}(z_i)\, v^* B_i v$, so each $v^* B_i v$ vanishes.
Hence $B_i v = 0$ and $A v = 0$, so the pencil is singular everywhere.

Real stability of a real polynomial is equivalent to real-rootedness of all
its restrictions $t \mapsto P(x + t e)$ with $x$ real and $e$ positive; for
homogeneous $P$ this is hyperbolicity in every positive direction. The
homogenization is hyperbolic in the boundary directions $(0, e)$, and
hyperbolicity propagates along a path to all positive directions. The top
component is the endpoint of a homotopy of stable polynomials, and root
continuity keeps its line restrictions real-rooted. Same-phase stability is
the case $x = 0$, together with a limit for weights that vanish.

## References

P. Brändén, “Polynomials with the half-plane property and matroid theory,”
*Adv. Math.* 216 (2007), 302–320; J. Borcea and P. Brändén, “Applications of
stable polynomials to mixed determinants,” *Duke Math. J.* 143 (2008),
Proposition 2.4; L. Gårding, “An inequality for hyperbolic polynomials,”
*J. Math. Mech.* 8 (1959), 957–965. See the
[stable polynomials](https://www.symmetricfunctions.com/stablePolynomials.htm#stablePolynomialDefinition)
and the
[Rayleigh property](https://www.symmetricfunctions.com/stablePolynomials.htm#stronglyRayleighProperty)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes the multiaffine Rayleigh criterion, determinantal
stability, hyperbolicity of homogeneous real stable polynomials, and the
homogenization, top-component and same-phase consequences.
-/

open Polynomial
open scoped ComplexOrder

namespace RealRooted
namespace Challenges
namespace RealStability

/-- **Brändén's Rayleigh criterion**: a multiaffine real polynomial is real
stable if and only if it is nonzero and Rayleigh. -/
theorem mvRealStable_iff_isRayleigh {σ : Type*} {P : MvPolynomial σ ℝ}
    (hma : P.IsMultiaffine) :
    MvRealStable P ↔ P.IsRayleigh ∧ P ≠ 0 :=
  MvPolynomial.IsMultiaffine.mvRealStable_iff_isRayleigh_and_ne_zero hma

/-- **Borcea–Brändén determinantal stability**: for Hermitian `A` and positive
semidefinite `B k`, the pencil determinant `det (A + ∑ k, z k • B k)` is zero
or stable. -/
theorem detPencil_eq_zero_or_stable {m σ : Type*} [Fintype m] [DecidableEq m]
    [Fintype σ] (A : Matrix m m ℂ) (B : σ → Matrix m m ℂ) (hA : A.IsHermitian)
    (hB : ∀ k, (B k).PosSemidef) :
    detPencil A B = 0 ∨ MvUpperHalfPlaneStable (detPencil A B) :=
  mvUpperHalfPlaneStableOrZero_detPencil A B hA hB

/-- A nonzero real determinantal pencil with symmetric `A` and positive
semidefinite `B k` is real stable. -/
theorem mvRealStable_realDetPencil {m σ : Type*} [Fintype m] [DecidableEq m]
    [Fintype σ] (A : Matrix m m ℝ) (B : σ → Matrix m m ℝ) (hA : A.IsHermitian)
    (hB : ∀ k, (B k).PosSemidef) (hne : realDetPencil A B ≠ 0) :
    MvRealStable (realDetPencil A B) := by
  refine RealRooted.mvRealStable_realDetPencil A B hA hB fun h ↦ hne ?_
  apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa [complexifyMv] using h

/-- A homogeneous real polynomial is real stable exactly when it is hyperbolic
in every strictly positive direction. -/
theorem mvRealStable_iff_forall_hyperbolicAt {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d) :
    MvRealStable P ↔ ∀ e : σ → ℝ, (∀ i, 0 < e i) → P.HyperbolicAt e :=
  MvPolynomial.IsHomogeneous.mvRealStable_iff_forall_hyperbolicAt_pos hhom

/-- The total-degree homogenization of a nonzero real stable polynomial with
nonnegative coefficients is real stable. -/
theorem mvRealStable_ordinaryHomogenization {σ : Type*} {P : MvPolynomial σ ℝ}
    (hst : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0) :
    MvRealStable (MvPolynomial.ordinaryHomogenization P P.totalDegree) :=
  hst.ordinaryHomogenization hnn hP

/-- The top homogeneous component of a nonzero real stable polynomial with
nonnegative coefficients is real stable. -/
theorem mvRealStable_homogeneousComponent_totalDegree {σ : Type*}
    {P : MvPolynomial σ ℝ} (hst : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hP : P ≠ 0) :
    MvRealStable (MvPolynomial.homogeneousComponent P.totalDegree P) :=
  hst.homogeneousComponent_totalDegree hnn hP

/-- Every real stable polynomial is same-phase stable. -/
theorem samePhaseStable {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P) :
    SamePhaseStable P :=
  hP.samePhaseStable

end RealStability
end Challenges
end RealRooted
