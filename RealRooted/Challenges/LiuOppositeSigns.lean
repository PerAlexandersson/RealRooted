import RealRooted.LiuOppositeSigns.Theorem

/-!
# Liu's opposite-sign compatibility theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "liu-opposite-signs"
authors = ["Liu"]
years = [2012]

[[definitions]]
name = "RealRooted.LiuOppositeSigns.OppositeLeadingSigns"
module = "RealRooted.LiuOppositeSigns.RootCount"
label = "Opposite leading signs"

[[definitions]]
name = "RealRooted.LiuOppositeSigns.rootCountAtOrAbove"
module = "RealRooted.LiuOppositeSigns.RootCount"
label = "Number of roots in [x, ∞)"

[[definitions]]
name = "RealRooted.LiuOppositeSigns.RootCountCompatible"
module = "RealRooted.LiuOppositeSigns.RootCount"
label = "Root counts differing by at most one"

[[definitions]]
name = "RealRooted.LiuOppositeSigns.LeftRootCountBranch"
module = "RealRooted.LiuOppositeSigns"
label = "Root-count condition, deleting the largest root of f"

[[definitions]]
name = "RealRooted.LiuOppositeSigns.RightRootCountBranch"
module = "RealRooted.LiuOppositeSigns"
label = "Root-count condition, deleting the largest root of g"

[[definitions]]
name = "RealRooted.LiuOppositeSigns.CommonRootDeletionCompatibleBranch"
module = "RealRooted.LiuOppositeSigns.Theorem21Statements.CommonRootDeletion"
label = "Common root with compatible cofactors"

[[theorems]]
name = "RealRooted.Challenges.LiuOppositeSigns.compatible_iff_rootCount"
module = "RealRooted.Challenges.LiuOppositeSigns"
label = "Compatibility with opposite leading signs (corrected)"
headline = true

[[theorems]]
name = "RealRooted.Challenges.LiuOppositeSigns.compatible_iff_rootCount_of_noCommonRoots"
module = "RealRooted.Challenges.LiuOppositeSigns"
label = "Compatibility for pairs without common roots"

[[theorems]]
name = "RealRooted.Challenges.LiuOppositeSigns.published_forward_direction_fails"
module = "RealRooted.Challenges.LiuOppositeSigns"
label = "Without the common-root branch the statement fails"

[[theorems]]
name = "RealRooted.Challenges.LiuOppositeSigns.natDegree_diff_le_two"
module = "RealRooted.Challenges.LiuOppositeSigns"
label = "Degrees of compatible pairs differ by at most two"
-->

<!-- realrooted-catalog-content -->
# Liu's opposite-sign compatibility theorem

Two real polynomials $f$ and $g$ are **compatible** if every combination
$\alpha f + \beta g$ with $\alpha, \beta \geq 0$ is real-rooted. When $f$ and $g$ have leading
coefficients of the same sign, compatibility is governed by common
interleavers (Chudnovsky–Seymour). Liu treats the case of **opposite leading
signs**, where the answer is a root-count condition.

Write $n_p(x)$ for the number of roots of $p$ in $[x, \infty)$, counted with
multiplicity.

**Theorem (Liu, corrected).** Let $f$ and $g$ be nonconstant
real-rooted polynomials with opposite leading signs. Then $f$ and $g$ are
compatible if and only if one of the following holds:

- after deleting the largest root from whichever of $f$ and $g$ has the
  larger largest root (from $f$ in case of a tie), the root counts of the
  resulting pair differ by at most one at every point;
- $f$ and $g$ share a root $r$, and the cofactors $f/(x-r)$ and
  $g/(x-r)$ are compatible.

The second branch is missing from the published statement, and it is
necessary: the forward direction of the published version fails for $x$ and
$-x^2$, which share the root $0$.

**Corollary (Liu).** Compatible real-rooted polynomials with
opposite leading signs have degrees differing by at most two.

For pairs without common roots, the forward direction is first proved for
polynomials with simple roots. Small derivative-shift regularizations, which
preserve compatibility, reduce the general case to that one, and root
matching passes back to the limit.

## References

Lily L. Liu, [“Polynomials with real zeros and compatible
sequences,”](https://doi.org/10.37236/2674) Electronic Journal of
Combinatorics 19(3) (2012), #P33.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.LiuOppositeSigns`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace LiuOppositeSigns

open RealRooted.LiuOppositeSigns

/-- Nonconstant real-rooted polynomials with opposite leading signs are compatible
if and only if, after deleting the larger largest root, the root counts differ by
at most one everywhere, or the two polynomials share a root with compatible
cofactors. -/
theorem compatible_iff_rootCount {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔
      (∃ r s, LeftRootCountBranch f g r s ∨ RightRootCountBranch f g r s) ∨
        CommonRootDeletionCompatibleBranch f g :=
  compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant hf hg hsgn hf_deg hg_deg

/-- Without common roots, compatibility is the root-count condition alone. -/
theorem compatible_iff_rootCount_of_noCommonRoots {f g : ℝ[X]} (hf : f.Splits)
    (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔
      ∃ r s, LeftRootCountBranch f g r s ∨ RightRootCountBranch f g r s :=
  theorem21CompatibleRootCountNoCommonNonconstant f g hf hg hsgn hno hf_deg hg_deg

/-- Without the common-root branch, the forward direction fails (for `X` and
`-X ^ 2`). -/
theorem published_forward_direction_fails :
    ¬ ∀ {f g : ℝ[X]}, f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 → Compatible f g →
        ∃ r s, LeftRootCountBranch f g r s ∨ RightRootCountBranch f g r s :=
  not_theorem21CompatibleToRootCountBranchesNonconstantStatement

/-- Compatible real-rooted polynomials with opposite leading signs have degrees
differing by at most two. -/
theorem natDegree_diff_le_two {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff_proof f g hf hg hsgn hcompat

end LiuOppositeSigns
end Challenges
end RealRooted
