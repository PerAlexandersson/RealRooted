module

public import RealRooted.ChudnovskySeymour.Core
public import RealRooted.CommonInterleaver.FamilySum
public import RealRooted.CommonInterleaver.FamilyUpgrade
public import RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility
public import RealRooted.CommonInterleaver.RootSelection
public import RealRooted.CommonInterleaver.RootSelectionTree
public import RealRooted.Compatibility.InterleaverBridge
public import RealRooted.Compatibility.Leander
import RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift
public import RealRooted.Compatibility.Pair
public import RealRooted.RootLocation.CommonInterlacer
public import RealRooted.Basic.ProperPosition
import RealRooted.CommonInterleaverSeq
import RealRooted.DegreeDropDivXPrec
import RealRooted.SameDegreeCountFromAnalytic

/-!
# Common interleaver challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "common-interleavers"
formalized = "2026-07-03"
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
name = "RealRooted.Challenges.CommonInterleaver.compatiblePair_hasCommonInterleaver"
module = "RealRooted.Challenges.Interlacing.CommonInterleaver"
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
headline = true

[[theorems]]
name = "RealRooted.posComboPairHasCommonInterleaver_of_splits"
module = "RealRooted.CommonInterleaver.PairBridge.Compatibility.NonnegativeShift"
label = "Split polynomials with real-rooted positive combinations have a common interleaver"

[[theorems]]
name = "RealRooted.pairHasCommonInterleaver_of_posCombo_sameDegree"
module = "RealRooted.SameDegreeCountFromAnalytic"
label = "Chudnovsky–Seymour for two polynomials of the same degree without common roots"

[[theorems]]
name = "RealRooted.pairHasCommonInterleaver_of_posCombo_succDegree"
module = "RealRooted.CommonInterleaver.PairBridge.SuccDegree.SlotData"
label = "Chudnovsky–Seymour for two polynomials whose degrees differ by one"

[[theorems]]
name = "RealRooted.pairHasCommonInterleaver_of_posCombo_noCommon_of_natDegree_close"
module = "RealRooted.CommonInterleaver.PairBridge.Reduction.CommonInterleaver"
label = "Chudnovsky–Seymour for two polynomials of close degrees without common roots"

[[theorems]]
name = "RealRooted.sameDegree_rootCountAbove_bounds_of_posCombo_noCommon"
module = "RealRooted.SameDegreeCountFromAnalytic"
label = "Same-degree positive-combination pairs have upper root counts differing by at most one"

[[theorems]]
name = "RealRooted.pairHasCommonLeftInterleaver_of_commonInterleaver"
module = "RealRooted.CommonInterleaverSeq"
label = "A common right interleaver of a close-degree pair gives a common left interleaver"

[[theorems]]
name = "RealRooted.strictInterl_iff_strictInterl_divX_left_of_hasNonnegCoeffs_coeff_zero"
module = "RealRooted.DegreeDropDivXPrec"
label = "Degree drop at a zero constant coefficient: f ≪ g iff g/X ≪ f"

[[theorems]]
name = "RealRooted.leanderTransform_preserves_compatibility"
module = "RealRooted.Compatibility.Leander"
label = "Leander: the transform preserves ordered compatibility"

[[theorems]]
name = "RealRooted.isRealRootedIn_weightedSum_of_splits"
module = "RealRooted.RootLocation.CommonInterlacer"
label = "A split nonnegative combination of polynomials rooted in an interval is rooted there"

[[theorems]]
name = "RealRooted.HasCommonInterleaver.map"
module = "RealRooted.RootLocation.CommonInterlacer"
label = "Linear maps preserving real-rootedness on an interval transport common interleavers"

[[theorems]]
name = "RealRooted.exists_mem_largestRoot_le_sum"
module = "RealRooted.CommonInterleaver.RootSelection"
label = "Marcus–Spielman–Srivastava: some member's largest root is at most that of the sum"

[[theorems]]
name = "RealRooted.RootSelectionTree.Valid.exists_leaf_largestRoot_le"
module = "RealRooted.CommonInterleaver.RootSelectionTree"
label = "Interlacing families: some leaf's largest root is at most the root node's"
-->

<!-- realrooted-catalog-content -->
# Common interleavers

A finite family of real-rooted polynomials $f_1, \dotsc, f_m$ has a **common
interleaver** if a single real-rooted $h$ satisfies $f_i \ll h$ for every $i$.
Here $f\ll h$ means that $f$ interlaces $h$; see the
[interlacing page](/RealRooted/concepts/interlacing/).
The family is **compatible** if every nonnegative combination
$c_1 f_1 + \dotsb + c_m f_m$ is zero or real-rooted.

**Theorem (Chudnovsky–Seymour).** [@ChudnovskySeymour2007] For real-rooted
polynomials with positive
leading coefficients, the following are equivalent:

1. every pair is compatible;
2. every pair has a common interleaver;
3. the whole family has a common interleaver;
4. the whole family is compatible.

The library proves each implication:

- **Compatible pairs have common interleavers:** the two-polynomial case of
  1 ⇒ 2.
- **Pairwise compatibility and common interleavers:** 1 ⇔ 3.
- **Pairwise and family compatibility:** 1 ⇔ 4.
- **Pairwise to global:** 2 ⇒ 3.
- **Common interleavers give compatibility:** 3 ⇒ 4. In particular, the sum of
  a family with a common interleaver is real-rooted.

The two-polynomial theorem is proved by cases on the degrees. For a pair
$f, g$ of positive leading coefficients such that every positive combination
$\lambda f + \mu g$ is nonzero and real-rooted, the library has a common
interleaver in each of the following situations:

- $\deg g = \deg f$ and $f, g$ have no common root. Then for every real $x$ that
  is not a root of $f$ or $g$, the numbers of roots of $f$ and of $g$ larger
  than $x$ differ by at most one;
- $\deg g = \deg f + 1$;
- $\deg f \leq \deg g \leq \deg f + 1$ and $f, g$ have no common root, as a
  combination of the two cases above;
- $f$ and $g$ split, with no restriction on the degrees. This is the
  positive-combination form of the theorem for compatible pairs; the proof
  translates both polynomials far enough to make their coefficients
  nonnegative, applies the nonnegative case, and translates back.

If $f, g$ have degrees $d$ and $d$ or $d + 1$, and $h$ is a common right
interleaver, then there is also a common left interleaver $\ell$ with
$\ell \ll f$ and $\ell \ll g$. In the degree-drop situation $\deg g = \deg f + 1$
with $g$ divisible by $x$ and both polynomials having nonnegative coefficients,
$f \ll g$ holds if and only if $g/x \ll f$.

This is the interlacing input for the real-rootedness of independence
polynomials of claw-free graphs; see the
[Chudnovsky–Seymour page](/RealRooted/theorems/chudnovsky-seymour/).

**Transport along linear maps.** Let $T$ be a linear map on real polynomials, $J$ an interval
and $n$ a degree, and suppose $T$ sends every polynomial of degree $n$ with positive leading
coefficient whose roots lie in $J$ to a real-rooted polynomial with positive leading coefficient.
Then $T$ sends a finite family of such polynomials with a common interleaver to a family with a
common interleaver. Indeed, every nonnegative combination of the inputs is real-rooted by
Chudnovsky–Seymour, hence has all its roots in $J$ because outside the convex hull of the roots
all members have the same strict sign. Its image is therefore real-rooted, and the image of a
combination is the combination of the images. The images are thus a compatible family and have a
common interleaver; this is the criterion of Marcus–Spielman–Srivastava
(*Interlacing families I*, Lemma 4.5, arXiv:1304.4132). The output degree need not be
constant. For two polynomials, `Compatible.hasCommonInterleaver_map` and
`StrictInterl.hasCommonInterleaver_map` give the pair versions.

**Theorem (Leander).** [@Leander2016x, Thm. 2.3] Let $f_0, \dotsc, f_{n-1}$ have positive leading
coefficients, and suppose that $f_i$ and $f_j$ are compatible and $x f_i$ and
$f_j$ are compatible whenever $i \le j$. Define
$$
L(f)_k = x \sum_{h < k} f_h + \sum_{h > k} f_h .
$$
Then the family $L(f)_0, \dotsc, L(f)_{n-1}$ satisfies the same two
conditions.

**Interlacing families** (Marcus–Spielman–Srivastava). If polynomials
$p_1,\dotsc,p_m$ of the same degree $d\ge1$ with positive leading
coefficients have a common **left** interlacer—a polynomial $h$ of degree
$d-1$ with $h\ll p_i$ for every $i$—then some $p_i$ has largest root at most
the largest root of $\sum_i p_i$. Iterating along a tree of degree-$d$
polynomials whose sibling polynomials have such common left interlacers, some
leaf has largest root at most that of the root polynomial.

## References

See [@ChudnovskySeymour2007; @Branden2015, Sec. 7.8; @Leander2016x, Thm. 2.3].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CommonInterleaver` and `RealRooted.Compatibility`.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace CommonInterleaver

/-- Two compatible real polynomials with positive leading coefficients have a
common interleaver. -/
theorem compatiblePair_hasCommonInterleaver {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g) (hfg : Compatible f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  RealRooted.chudnovskySeymour_compatiblePairHasCommonInterleaver hf hg hfg

end CommonInterleaver
end Challenges
end RealRooted
