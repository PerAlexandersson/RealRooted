module

public import RealRooted.ChudnovskySeymour.Core
public import RealRooted.CommonInterleaver.FamilyUpgrade
public import RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.Compatibility.Leander
public import RealRooted.Compatibility.Pair
public import RealRooted.LiuOppositeSigns.CompatibilityCriterion
public import RealRooted.LiuOppositeSigns.RootCountBranches.Interfaces
public import RealRooted.RootLocation.CommonInterlacer

/-!
# Compatible families and common interleavers

<!-- realrooted-catalog
version = 1
kind = "method"
section = "concepts"
slug = "common-interleavers"
formalized = "2026-07-03"
references = [
  "ChudnovskySeymour2007",
  "Liu2012CompatibleSequences",
  "Branden2015",
  "Leander2016x",
]
authors = ["Chudnovsky", "Seymour", "Liu", "Leander"]
years = [2007, 2012, 2016]

[[definitions]]
name = "RealRooted.HasCommonInterleaver"
module = "RealRooted.CommonInterleaver.RootDesc"
label = "Common interleaver of a family"

[[definitions]]
name = "RealRooted.Compatible"
module = "RealRooted.Compatibility.Pair"
label = "Compatible pair: every nonnegative combination is zero or real-rooted"

[[theorems]]
name = "RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver"
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: a family is pairwise compatible iff it has a common interleaver"
headline = true
symcat = "commonInterlacingCompatibilityTheorem"

[[theorems]]
name = "RealRooted.chudnovskySeymour_pairwiseCompatible_iff_familyCompatible"
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: pairwise compatible families are compatible"

[[theorems]]
name = "RealRooted.isRealRooted_sum_of_commonInterleaver"
module = "RealRooted.CommonInterleaver.FamilyUpgrade"
label = "A family with a common interleaver has a real-rooted sum"

[[theorems]]
name = "RealRooted.chudnovskySeymour_compatiblePairHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift"
label = "A compatible pair has a common interleaver"

[[theorems]]
name = "RealRooted.HasCommonInterleaver.map"
module = "RealRooted.RootLocation.CommonInterlacer"
label = "Linear maps preserving real-rootedness on an interval transport common interleavers"

[[theorems]]
name = "RealRooted.Compatible.leanderTransform_ordered"
module = "RealRooted.Compatibility.Leander"
label = "Leander: the diagonal-omitting transform preserves ordered compatibility"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.compatible_iff_rootCountBranchesWithCommon"
module = "RealRooted.LiuOppositeSigns.CompatibilityCriterion"
label = "Liu, corrected: compatibility with opposite leading signs is a root-count condition"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.not_forall_rootCountBranches_of_compatible"
module = "RealRooted.LiuOppositeSigns.RootCountBranches.Interfaces"
label = "Liu's published root-count condition is not necessary: x and −x²"

[[theorems]]
name = "RealRooted.LiuOppositeSigns.natDegree_abs_sub_le_two_of_compatible"
module = "RealRooted.LiuOppositeSigns.CompatibilityCriterion"
label = "Compatible pairs with opposite leading signs differ in degree by at most two"
-->

<!-- realrooted-catalog-content -->
# Compatible families and common interleavers

A family of real-rooted polynomials is compatible if all its nonnegative combinations are
real-rooted. For positive leading coefficients, Chudnovsky and Seymour showed that this holds
exactly when the members have a common interleaver, and that it suffices to check pairs. Liu's
theorem treats pairs with opposite leading signs.

## Results

A family $f_1,\dotsc,f_m$ has a *common interleaver* if some $h$ satisfies $f_i\ll h$ for all
$i$. It is *compatible* if every combination $c_1f_1+\dotsb+c_mf_m$ with $c_i\ge0$ is zero or
real-rooted, and *pairwise compatible* if every pair is.

**Theorem (Chudnovsky–Seymour).** [@ChudnovskySeymour2007] For nonzero real-rooted polynomials
with positive leading coefficients, the following are equivalent:

1. the family is pairwise compatible;
2. the family has a common interleaver;
3. the family is compatible.

Every compatible pair with positive leading coefficients has a common interleaver, and a
nonempty family with a common interleaver has a real-rooted sum.

**Theorem (transport).** Let $T$ be a linear map on real polynomials, $J$ an interval and $n$ a
degree, such that $T$ maps every real-rooted polynomial of degree $n$ with positive leading
coefficient and all roots in $J$ to a real-rooted polynomial with positive leading coefficient.
If $f_1,\dotsc,f_m$ are such polynomials with a common interleaver, so are
$Tf_1,\dotsc,Tf_m$.

**Theorem (Leander).** [@Leander2016x, Thm. 2.3] Let $f_0,\dotsc,f_{n-1}$ have positive leading
coefficients, and suppose that $f_i,f_j$ and $xf_i,f_j$ are compatible whenever $i\le j$. Put
$$
L(f)_k=x\sum_{h<k}f_h+\sum_{h>k}f_h .
$$
Then $L(f)_i,L(f)_j$ and $xL(f)_i,L(f)_j$ are compatible whenever $i\le j$.

**Theorem (Liu, corrected).** [@Liu2012CompatibleSequences] Let $f$ and $g$ be nonconstant
real-rooted polynomials with opposite leading signs, and let $n_p(x)$ be the number of roots of
$p$ in $[x,\infty)$. Then $f$ and $g$ are compatible if and only if one of the following holds:

- deleting the largest root from the polynomial with the larger largest root (from $f$ in case
  of a tie) gives a pair $(p,q)$ with $|n_p(x)-n_q(x)|\le1$ for every real $x$;
- $f$ and $g$ share a root $r$, and $f/(x-r)$ and $g/(x-r)$ are compatible.

In particular their degrees differ by at most two. Liu's published statement has only the
first condition, which is not necessary: $x$ and $-x^2$ are compatible, but deleting the root
$0$ of $x$ leaves a root-count gap of two at every $x\le0$.

## Use

The Chudnovsky–Seymour theorem gives the real-rootedness of independence polynomials of
[claw-free graphs](rr:chudnovsky-seymour). The transport theorem is the criterion of Marcus,
Spielman and Srivastava for common interleavers [@MarcusSpielmanSrivastava2015I, Lemma 4.5].

## Proof

For a compatible pair, equal degrees and degrees differing by one are treated separately. For
real-rooted polynomials of arbitrary degrees, we translate both far enough that their
coefficients become nonnegative, apply that case, and translate the interleaver back. For Liu's
theorem, the root-count criterion is proved directly for simple roots; small
[derivative shifts](rr:hermite-poulain) preserve compatibility and reduce the general
case to it.

## References

[@ChudnovskySeymour2007]; [@Liu2012CompatibleSequences]; [@Branden2015, Sec. 7.8];
[@Leander2016x, Thm. 2.3]. See also the
[Chudnovsky–Seymour compatibility theorem](sf:commonInterlacingCompatibilityTheorem) and
[compatible polynomials](sf:compatiblePolynomials) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
