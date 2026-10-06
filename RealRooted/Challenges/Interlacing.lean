import RealRooted.Basic.ProperPosition

/-!
# Interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "interlacing"
authors = ["Fisk"]
years = [2006]

[[definitions]]
name = "RealRooted.StrictInterl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing f ≪ g"

[[definitions]]
name = "RealRooted.Interl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing, allowing zero polynomials"

[[definitions]]
name = "RealRooted.Interlaces"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing with degrees differing by one"

[[definitions]]
name = "RealRooted.IsSturmSeq"
module = "RealRooted.Basic.ProperPosition"
label = "Sturm sequence"

[[theorems]]
name = "RealRooted.Challenges.Interlacing.interlaces_iff"
label = "Interlaces is interlacing with a degree increase"
headline = true

[[theorems]]
name = "RealRooted.StrictInterl.natDegree_eq_or_eq_succ"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing polynomials differ in degree by at most one"

[[theorems]]
name = "RealRooted.StrictInterl.toInterl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing of nonzero polynomials implies Interl"
-->

<!-- realrooted-catalog-content -->
# Polynomial interlacing

Let $f$ and $g$ be nonzero real-rooted polynomials with roots
$s_1 \leq \dotsb \leq s_k$ and $r_1 \leq \dotsb \leq r_m$, listed with multiplicity. We write
$f \ll g$ (`StrictInterl f g`) if either

- $m = k + 1$ and $r_1 \leq s_1 \leq r_2 \leq s_2 \leq \dotsb \leq s_k \leq r_{k+1}$, or
- $m = k$ and $s_1 \leq r_1 \leq s_2 \leq r_2 \leq \dotsb \leq s_k \leq r_k$.

In both cases $g$ has the largest root. Shared and repeated roots are allowed.
The relation `Interl f g` also holds when $f$ or $g$ is zero, and
`Interlaces f g` is the case $m = k + 1$ alone. A list $p_0, p_1, \dotsc$ of
polynomials is a Sturm sequence (`IsSturmSeq`) if `Interlaces` holds for each
consecutive pair $p_{i+1}, p_i$, so that the degrees drop by one at each step.

**Theorem.** We have `Interlaces f g` if and only if $f \ll g$ and
$\deg g = \deg f + 1$. If $f \ll g$, then $\deg g = \deg f$ or
$\deg g = \deg f + 1$.

## References

Steve Fisk, [“Polynomials, roots, and
interlacing,”](https://arxiv.org/abs/math/0612833) arXiv:math/0612833 (2006).
See also the
[interlacing overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacesPolynomial).
<!-- /realrooted-catalog-content -->
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Interlacing

/-- `Interlaces f g` is exactly `StrictInterl f g` together with the degree
condition `f.natDegree + 1 = g.natDegree`. -/
theorem interlaces_iff {f g : ℝ[X]} :
    Interlaces f g ↔ StrictInterl f g ∧ f.natDegree + 1 = g.natDegree := by
  refine ⟨fun h ↦ ⟨h.toStrictInterl, ?_⟩, fun h ↦ h.1.toInterlaces h.2⟩
  rcases h with ⟨-, -, hdeg, -⟩
  exact hdeg

end Interlacing
end Challenges
end RealRooted
