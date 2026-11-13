module

public import RealRooted.Basic.ProperPosition
public import RealRooted.ChudnovskySeymour.Core
public import RealRooted.CommonInterleaver.FamilySum
public import RealRooted.CommonInterleaver.FamilyUpgrade
public import RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift
public import RealRooted.CommonInterleaver.PairBridge.Reduction.CommonInterleaver
public import RealRooted.CommonInterleaver.PairBridge.SuccDegree.SlotData
public import RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.CommonInterleaver.RootSelection
public import RealRooted.CommonInterleaver.RootSelectionTree
public import RealRooted.CommonInterleaverSeq
public import RealRooted.Compatibility.Basic
public import RealRooted.Compatibility.InterleaverBridge
public import RealRooted.Compatibility.Leander
public import RealRooted.Compatibility.LeanderTransform
public import RealRooted.Compatibility.Pair
public import RealRooted.DegreeDropDivXPrec
public import RealRooted.RootLocation.CommonInterlacer
public import RealRooted.SameDegreeCountFromAnalytic

/-!
# Common interleavers and compatible families

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "common-interleavers"
formalized = "2026-07-03"
tags = []
references = [
  "ChudnovskySeymour2007",
  "Branden2015",
  "Leander2016x",
]
authors = ["Chudnovsky", "Seymour", "Leander"]
years = [2007, 2016]

[[definitions]]
name = "RealRooted.HasCommonInterleaver"
module = "RealRooted.CommonInterleaver.RootDesc"
label = "Common interleaver of a family"

[[definitions]]
name = "RealRooted.PairwiseHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.RootDesc"
label = "Pairwise common interleavers"

[[definitions]]
name = "RealRooted.Compatible"
module = "RealRooted.Compatibility.Pair"
label = "Compatible pair"

[[definitions]]
name = "RealRooted.PairwiseCompatible"
module = "RealRooted.Compatibility.Basic"
label = "Pairwise compatible family"

[[definitions]]
name = "RealRooted.FamilyCompatible"
module = "RealRooted.Compatibility.Basic"
label = "Compatible family"

[[definitions]]
name = "RealRooted.leanderTransform"
module = "RealRooted.Compatibility.LeanderTransform"
label = "Leander’s diagonal-omitting transform"

[[theorems]]
name = "RealRooted.hasCommonInterleaver_of_pairwiseHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.FamilyUpgrade"
label = "Pairwise common interleavers give a common interleaver"

[[theorems]]
name = "RealRooted.isRealRooted_sum_of_commonInterleaver"
module = "RealRooted.CommonInterleaver.FamilyUpgrade"
label = "A family with a common interleaver has a real-rooted sum"

[[theorems]]
name = "RealRooted.isRealRooted_sum_of_pairwiseHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.FamilySum"
label = "Pairwise common interleavers give a real-rooted sum"

[[theorems]]
name = "RealRooted.familyCompatible_of_commonInterleaver"
module = "RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility"
label = "A common interleaver gives a compatible family"

[[theorems]]
name = "RealRooted.pairwiseCompatible_of_pairwiseHasCommonInterleaver"
module = "RealRooted.Compatibility.InterleaverBridge"
label = "Pairwise common interleavers give pairwise compatibility"

[[theorems]]
name = "RealRooted.chudnovskySeymour_compatiblePairHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift"
label = "Chudnovsky–Seymour: a compatible pair has a common interleaver"

[[theorems]]
name = "RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver"
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: pairwise compatible ⇔ common interleaver"
headline = true

[[theorems]]
name = "RealRooted.chudnovskySeymour_pairwiseCompatible_iff_familyCompatible"
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: pairwise compatible ⇔ compatible family"

[[theorems]]
name = "RealRooted.posComboPairHasCommonInterleaver_of_splits"
module = "RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift"
label = "Split polynomials with real-rooted positive combinations have a common interleaver"

[[theorems]]
name = "RealRooted.pairHasCommonInterleaver_of_posCombo_sameDegree"
module = "RealRooted.SameDegreeCountFromAnalytic"
label = "Equal degrees, no common root, real-rooted positive combinations: common interleaver"

[[theorems]]
name = "RealRooted.pairHasCommonInterleaver_of_posCombo_succDegree"
module = "RealRooted.CommonInterleaver.PairBridge.SuccDegree.SlotData"
label = "Degrees differing by one, real-rooted positive combinations: common interleaver"

[[theorems]]
name = "RealRooted.exists_commonInterleaver_of_posCombo_of_no_common_roots"
module = "RealRooted.CommonInterleaver.PairBridge.Reduction.CommonInterleaver"
label = "Degrees differing by at most one, no common root: common interleaver"

[[theorems]]
name = "RealRooted.sameDegree_rootCountAbove_bounds_of_posCombo_noCommon"
module = "RealRooted.SameDegreeCountFromAnalytic"
label = "Equal-degree positive-combination pairs: root counts above x differ by at most 1"

[[theorems]]
name = "RealRooted.pairHasCommonLeftInterleaver_of_commonInterleaver"
module = "RealRooted.CommonInterleaverSeq"
label = "A common right interleaver of a close-degree pair gives a common left interleaver"

[[theorems]]
name = "RealRooted.strictInterl_iff_divX_strictInterl_of_coeff_zero"
module = "RealRooted.DegreeDropDivXPrec"
label = "For g(0) = 0 and deg g = deg f + 1 with nonnegative coefficients: f ≪ g iff g/X ≪ f"

[[theorems]]
name = "RealRooted.leanderTransform_preserves_compatibility"
module = "RealRooted.Compatibility.Leander"
label = "Leander: the transform preserves ordered compatibility"

[[theorems]]
name = "RealRooted.isRealRootedIn_weightedSum_of_splits"
module = "RealRooted.RootLocation.CommonInterlacer"
label = "A split nonnegative combination of same-degree polynomials rooted in J is rooted in J"

[[theorems]]
name = "RealRooted.HasCommonInterleaver.map"
module = "RealRooted.RootLocation.CommonInterlacer"
label = "Linear maps preserving real-rootedness on an interval transport common interleavers"

[[theorems]]
name = "RealRooted.exists_mem_largestRoot_le_sum"
module = "RealRooted.CommonInterleaver.RootSelection"
label = "A common left interlacer gives a member whose largest root is at most that of the sum"

[[theorems]]
name = "RealRooted.RootSelectionTree.Valid.exists_leaf_largestRoot_le"
module = "RealRooted.CommonInterleaver.RootSelectionTree"
label = "Interlacing families: some leaf's largest root is at most the root node's"
-->

<!-- realrooted-catalog-content -->
# Common interleavers and compatible families

A finite family of real-rooted polynomials with positive leading coefficients has a common
interleaver if and only if every nonnegative combination of its members is real-rooted or zero.

## Results

A family $f_1,\dotsc,f_m$ has a
**common interleaver** if a single real-rooted $h$ satisfies $f_i\ll h$ for all $i$. It is
**compatible** if every nonnegative combination
$c_1f_1+\dotsb+c_mf_m$ is zero or real-rooted, and **pairwise compatible** if every pair is.

**Theorem (Chudnovsky–Seymour).** [@ChudnovskySeymour2007] For real-rooted polynomials with
positive leading coefficients, the following are equivalent:

1. the family is pairwise compatible;
2. every pair has a common interleaver;
3. the family has a common interleaver;
4. the family is compatible.

**Corollary.** Let a nonempty family have positive leading coefficients. If it has a common
interleaver, or if all its members are real-rooted and every pair has a common interleaver, then
its sum is real-rooted.

**Theorem (pairs).** Let $f,g$ have positive leading coefficients, and suppose that
$\lambda f+\mu g$ is real-rooted for all $\lambda,\mu>0$. Then $f$ and $g$ have a common
interleaver if $f$ and $g$ are real-rooted, if $\deg g=\deg f+1$, or if
$\deg f\le\deg g\le\deg f+1$ and $f,g$ have no common root. In particular, every compatible
pair has a common interleaver. If moreover $\deg f=\deg g$ and $f,g$ have no common root, then
for every real $x$ that is not a root of $f$ or $g$, the numbers of roots of $f$ and of $g$
larger than $x$ differ by at most one.

**Proposition (left interleavers).** Let $\deg f\le\deg g\le\deg f+1$ and suppose that
$f\ll h$ and $g\ll h$ for some $h$. Then $\ell\ll f$ and $\ell\ll g$ for some $\ell$.

**Proposition (degree drop).** Let $f,g$ have nonnegative coefficients, $\deg g=\deg f+1$
and $g(0)=0$. Then $f\ll g$ if and only if $g/x\ll f$.

**Theorem (transport along linear maps).** Let $T$ be a linear map on real polynomials, $J$ an
interval and $n$ a degree. Suppose that $T$ maps every real-rooted polynomial of degree $n$ with
positive leading coefficient and all roots in $J$ to a real-rooted polynomial with positive
leading coefficient. If $f_1,\dotsc,f_m$ are such polynomials with a common interleaver,
then $Tf_1,\dotsc,Tf_m$ have a common interleaver. The same holds for a compatible or
interlacing pair $f,g$ of such polynomials.

**Proposition (hull).** Let $J$ be an interval and let $g_1,\dotsc,g_k$ be polynomials of the
same degree with positive leading coefficients, real-rooted with all roots in $J$. A nonnegative
combination of the $g_i$ with some positive weight that is real-rooted has all its roots in $J$.

**Theorem (Leander).** [@Leander2016x, Thm. 2.3] Let $f_0,\dotsc,f_{n-1}$ have positive leading
coefficients, and suppose that $f_i,f_j$ and $xf_i,f_j$ are compatible whenever $i\le j$.
Define
$$
L(f)_k = x \sum_{h < k} f_h + \sum_{h > k} f_h .
$$
Then $L(f)_i,L(f)_j$ and $xL(f)_i,L(f)_j$ are compatible whenever $i\le j$.

**Theorem (interlacing families).** Let $p_1,\dotsc,p_m$ be polynomials of degree $d$ with
positive leading coefficients, $m\ge1$, and suppose that some polynomial $h$ of degree $d-1$
satisfies $h\ll p_i$ for all $i$. Then some $p_i$ has largest root at most the largest root of
$\sum_ip_i$. Consequently, let $t$ be a finite rooted tree whose leaves are labelled by
real-rooted polynomials of degree $d\ge1$ with positive leading coefficients, in which every
internal node carries the sum of its children's polynomials, and in which the children of each
internal node have a common left interlacer of degree $d-1$. Then some leaf has largest root at
most that of the polynomial at the root.

## Use

The Chudnovsky–Seymour theorem is the interlacing input for the real-rootedness of independence
polynomials of claw-free graphs; see the
[Chudnovsky–Seymour page](rr:chudnovsky-seymour). The transport theorem is
the criterion for common interleavers of Marcus–Spielman–Srivastava
[@MarcusSpielmanSrivastava2015I, Lemma 4.5], and the last theorem is their selection principle
for roots.

## Proof

For pairs, we treat the degree cases separately. For split polynomials of arbitrary degrees, we
translate both polynomials far enough that their coefficients become nonnegative, apply the
nonnegative case, and translate the interleaver back.

## References

The equivalence of pairwise compatibility and a common interleaver is the
[Chudnovsky–Seymour compatibility theorem](sf:commonInterlacingCompatibilityTheorem). See
[@ChudnovskySeymour2007; @Branden2015, Sec. 7.8; @Leander2016x, Thm. 2.3].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CommonInterleaver` and `RealRooted.Compatibility`.
-/
