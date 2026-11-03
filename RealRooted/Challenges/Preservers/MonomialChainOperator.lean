module

public import RealRooted.NarayanaTransformation.Interlacing
public import RealRooted.OperatorInterlacingUpgrade.ImplicitRoot
import RealRooted.OperatorInterlacingUpgrade.RootOrder
public import RealRooted.OperatorInterlacingUpgrade.StablePencil
public import RealRooted.PFPolynomial
import RealRooted.QuadraticInterlacingClosure

/-!
# Monomial-chain operator challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monomial-chain-operator"
formalized = "2026-05-12"
references = [
  "Branden2011b",
]

[[definitions]]
name = "RealRooted.quadraticInterlacingPencil"
module = "RealRooted.QuadraticInterlacingClosure"
label = "Quadratic interlacing pencil"

[[definitions]]
name = "RealRooted.quadraticInterlacingTangent"
module = "RealRooted.QuadraticInterlacingClosure"
label = "Tangent of the quadratic interlacing pencil"

[[theorems]]
name = "RealRooted.Challenges.MonomialChainOperator.preservesInterlacing"
label = "The monomial chain gives interlacing preservation"
headline = true

[[theorems]]
name = "RealRooted.rootwiseLE_monomialChain_rootPolynomial_list_set"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "Moving one input root right moves every output root right"

[[theorems]]
name = "RealRooted.rootwiseLE_monomialChain_component_bounds"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "Output roots are bounded by the images of (x + a)^D and (x + b)^D"

[[theorems]]
name = "RealRooted.strictInterl_narayanaTransform"
module = "RealRooted.NarayanaTransformation.Interlacing"
label = "The Mao–Wang Narayana transform preserves interlacing"
headline = true

[[theorems]]
name = "RealRooted.exists_hasDerivAt_finRootPolynomial_shift"
module = "RealRooted.OperatorInterlacingUpgrade.ImplicitRoot"
label = "Implicit derivative of a simple output root in one input root"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_bivariatePencil_map_of_monomialChain"
module = "RealRooted.OperatorInterlacingUpgrade.StablePencil"
label = "Monomial-chain operators preserve nonnegative stable pencils"

[[theorems]]
name = "RealRooted.positiveRootCount_quadraticParameterEvaluation_le_rootCountDrop"
module = "RealRooted.QuadraticInterlacingClosure"
label = "Descartes budget for the quadratic parameter evaluation of an interlacing chain"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.strictInterl_quadraticInterlacingTangent_pencil"
module = "RealRooted.QuadraticInterlacingClosure"
label = "The tangent of a real-rooted quadratic pencil precedes the pencil"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.strictInterl_quadraticInterlacingRight_of_tangent"
module = "RealRooted.QuadraticInterlacingClosure"
label = "The tangent precedes the right member of the quadratic closure"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Interlacing from a monomial chain

Let $T$ be a real-linear operator on $\mathbb R[x]$ and let $D\in\mathbb N$.
Suppose that $T$ maps polynomials with nonnegative coefficients to polynomials
with nonnegative coefficients, sends every nonzero PF polynomial of degree at
most $D$ to a nonzero real-rooted polynomial, and its monomial images form the
oriented chain

$$
T(1) \ll T(X) \ll \dotsb \ll T(X^D).
$$

Then $f\ll g$ with nonnegative coefficients and $\deg g\leq D$ implies
$Tf\ll Tg$. The quadratic interlacing closure lemma propagates the monomial
chain through each nonpositive linear factor.

The proof first propagates the monomial chain through all PF factors, and then
uses the Garloff–Wagner Krein expansion to pass from one-root deletions to every
oriented interlacing pair.

## The quadratic interlacing closure

The step that passes the chain through one nonpositive linear factor is the following
statement about three polynomials with nonnegative coefficients and $F \ll G \ll H$. For
$b \ge 0$ put
$$
Q_b = H + 2bG + b^2 F, \qquad A_b = G + bF, \qquad B_b = H + bG,
$$
so that $Q_b = B_b + b A_b$ and $A_b$ is half the derivative of $Q_b$ in the parameter.

**Theorem.** If $Q_b$ is real-rooted for every $b \ge 0$, then $A_a \ll Q_a$ for every
$a \ge 0$, and consequently $A_a \ll B_a$, that is,
$$
G + aF \;\ll\; H + aG .
$$

The second conclusion is purely algebraic: the pairs $(A_a, Q_a)$ and $(A_a, B_a)$ span the same
real pencil and have the same oriented Wronskian, so interlacing transfers. The first conclusion
is the analytic heart. It follows root-count budgets from Descartes' rule of signs: for a fixed
point $r$, the quadratic $b \mapsto Q_b(r)$ has at most as many positive roots as the number of
roots of $H$ above $r$ minus the number of roots of $F$ above $r$. Together with the signs of the
residues of $A_a / Q_a$ at the roots of $Q_a$, this shows that the roots of $Q_b$ move
monotonically in $b$. Repeated and common roots are removed by a common derivative
regularization, and coefficientwise closure then recovers the general case.

## Consequences

Under the corresponding degree and nonvanishing hypotheses, moving one
nonpositive input root to the right moves every output root weakly to the
right. If $\rho$ is a simple root of $Tp$ and $r_i$ is the input root being
moved, the derivative of the resulting root branch is
$$
\frac{T(p/(x-r_i))(\rho)}{(Tp)'(\rho)}.
$$
The operator also preserves stability of nonnegative bivariate pencils
$f(z)+wg(z)$ under the hypotheses of the listed stable-pencil theorem. The
Mao–Wang Narayana transform is an instance; see the
[Narayana page](/RealRooted/families/narayana/).

## References

The decomposition step uses the Krein expansion for interlacing polynomials;
the operator perspective is related to [@Branden2011b].
<!-- /realrooted-catalog-content -->

This module exposes the fully checked monomial-chain upgrade.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace MonomialChainOperator

/-- A PF-preserving linear operator whose consecutive monomial images form an
oriented interlacing chain preserves every oriented PF interlacing pair. -/
theorem preservesInterlacing
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1)))) :
    StrictInterl (T f) (T g) :=
  strictInterl_map_of_monomialChain hfg hf hg hgdeg hTnn hTrr hmono

end MonomialChainOperator
end Challenges
end RealRooted
