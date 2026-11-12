module

public import RealRooted.LiuOppositeSigns
public import RealRooted.LiuOppositeSigns.CompatibilityCriterion
public import RealRooted.LiuOppositeSigns.RootCount
public import RealRooted.LiuOppositeSigns.RootCountBranches.CommonRootDeletion
public import RealRooted.LiuOppositeSigns.RootCountBranches.Interfaces

/-!
# Liu's opposite-sign compatibility theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "liu-opposite-signs"
formalized = "2026-10-02"
tags = []
references = [
  "Liu2012CompatibleSequences",
]
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
module = "RealRooted.LiuOppositeSigns.RootCountBranches.CommonRootDeletion"
label = "Common root with compatible cofactors"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.compatible_iff_rootCountBranchesWithCommon"
module = "RealRooted.LiuOppositeSigns.CompatibilityCriterion"
label = "Compatibility with opposite leading signs (corrected)"
headline = true

[[theorems]]
name = "RealRooted.LiuOppositeSigns.compatible_iff_rootCountBranches_of_noCommonRoots"
module = "RealRooted.LiuOppositeSigns.CompatibilityCriterion"
label = "Compatibility for pairs without common roots"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.not_forall_rootCountBranches_of_compatible"
module = "RealRooted.LiuOppositeSigns.RootCountBranches.Interfaces"
label = "Without the common-root branch the statement fails"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.natDegree_abs_sub_le_two_of_compatible"
module = "RealRooted.LiuOppositeSigns.CompatibilityCriterion"
label = "Degrees of compatible pairs differ by at most two"
-->

<!-- realrooted-catalog-content -->
# Liu's opposite-sign compatibility theorem

For real-rooted polynomials with opposite leading signs, compatibility is a root-count
condition, with an extra branch for common roots.

## Results

Two real polynomials $f$ and $g$ are *compatible* if every combination $\alpha f+\beta g$ with
$\alpha,\beta\ge0$ is zero or real-rooted. For leading coefficients of the same sign,
compatibility is governed by common interleavers (Chudnovsky--Seymour). Liu treats the case of
opposite leading signs. Write $n_p(x)$ for the number of roots of $p$ in $[x,\infty)$, counted
with multiplicity.

**Theorem (Liu).** [@Liu2012CompatibleSequences] Let $f$ and $g$ be nonconstant real-rooted
polynomials with opposite leading signs. Then $f$ and $g$ are compatible if and only if one of
the following holds.

- Delete the largest root from the polynomial with the larger largest root (from $f$ in case of
  a tie), and call the resulting pair $(p,q)$. Then $|n_p(x)-n_q(x)|\le1$ for every real $x$.
- $f$ and $g$ share a root $r$, and the cofactors $f/(x-r)$ and $g/(x-r)$ are compatible.

If $f$ and $g$ have no common root, they are compatible if and only if the first condition
holds.

**Corollary.** Compatible real-rooted polynomials with opposite leading signs have degrees
differing by at most two.

The published statement has the first condition alone, and its forward direction fails: $x$ and
$-x^2$ are compatible, but deleting the largest root $0$ from $x$ leaves a root-count gap of two
at every $x\le0$. The common-root condition above is the correction. Liu's proof for pairs with
no common root also treats such endpoints as if all of their roots were simple, which fails
for individual endpoints.

## Proof

For pairs with simple roots we prove the root-count criterion directly. The general case follows
by small derivative-shift regularizations, which preserve compatibility and reduce to the
simple-root case, and a limit of root matchings.

## References

[@Liu2012CompatibleSequences].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.LiuOppositeSigns`; the library forms are
`compatible_iff_rootCountBranchesWithCommon`,
`compatible_iff_rootCountBranches_of_noCommonRoots`,
`not_forall_rootCountBranches_of_compatible` and
`natDegree_abs_sub_le_two_of_compatible` in
`RealRooted.LiuOppositeSigns.CompatibilityCriterion` and
`RealRooted.LiuOppositeSigns.RootCountBranches.Interfaces`.
-/
