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
name = "RealRooted.LiuOppositeSigns.theorem21RootCountBranchesWithCommon"
module = "RealRooted.LiuOppositeSigns.Theorem21Statements.CommonRootDeletion"
label = "Root-count condition of the corrected Theorem 2.1"

[[theorems]]
name = """RealRooted.LiuOppositeSigns.\
compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant"""
module = "RealRooted.LiuOppositeSigns.Theorem"
label = "Liu, Theorem 2.1 (corrected)"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.theorem21CompatibleRootCountNoCommonNonconstant"
module = "RealRooted.LiuOppositeSigns.Theorem"
label = "Theorem 2.1 for pairs without common roots"

[[theorems]]
name = """RealRooted.LiuOppositeSigns.\
not_theorem21CompatibleToRootCountBranchesNonconstantStatement"""
module = "RealRooted.LiuOppositeSigns.Theorem21Statements.Interfaces"
label = "The published Theorem 2.1 fails"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.corollary22DegreeDiff_proof"
module = "RealRooted.LiuOppositeSigns.Theorem"
label = "Liu, Corollary 2.2: degrees differ by at most two"
-->

<!-- realrooted-catalog-content -->
# Liu's opposite-sign compatibility theorem

Two real polynomials `f` and `g` are **compatible** if every combination
`αf + βg` with `α, β ≥ 0` is real-rooted. When `f` and `g` have leading
coefficients of the same sign, compatibility is governed by common
interleavers (Chudnovsky–Seymour). Liu treats the case of **opposite leading
signs**, where the answer is a root-count condition.

Write `n_p(x)` for the number of roots of `p` in `[x, ∞)`, counted with
multiplicity.

**Theorem (Liu, Theorem 2.1, corrected).** Let `f` and `g` be nonconstant
real-rooted polynomials with opposite leading signs. Then `f` and `g` are
compatible if and only if one of the following holds:

- after deleting the largest root from whichever of `f` and `g` has the
  larger largest root (from `f` in case of a tie), the root counts of the
  resulting pair differ by at most one at every point;
- `f` and `g` share a root `r`, and the cofactors `f / (x - r)` and
  `g / (x - r)` are compatible.

The second branch is missing from the published statement, and it is
necessary: the forward direction of the published version fails for `x` and
`-x²`, which share the root `0`.

**Corollary (Liu, Corollary 2.2).** Compatible real-rooted polynomials with
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
