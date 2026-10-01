import RealRooted.CommonInterleaver.FamilySum
import RealRooted.ChudnovskySeymour.Core
import RealRooted.CommonInterleaver.FamilyUpgrade
import RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility
import RealRooted.Compatibility.InterleaverBridge

/-!
# Common interleaver challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "common-interleavers"
authors = ["Chudnovsky", "Seymour"]
years = [2007]

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
name = "RealRooted.FamilyCompatible"
module = "RealRooted.Compatibility.Basic"
label = "Compatible family"

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
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: a compatible pair has a common interleaver"

[[theorems]]
name = "RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge"
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: pairwise compatible ⇔ common interleaver"
headline = true

[[theorems]]
name = "RealRooted.chudnovskySeymour_pairwiseCompatible_iff_familyCompatible"
module = "RealRooted.ChudnovskySeymour.Core"
label = "Chudnovsky–Seymour: pairwise compatible ⇔ compatible family"
headline = true
-->

<!-- realrooted-catalog-content -->
# Common interleavers

A finite family of real-rooted polynomials $f_1, \dotsc, f_m$ has a **common
interleaver** if a single real-rooted $h$ satisfies $f_i \ll h$ for every $i$.
The family is **compatible** if every nonnegative combination
$c_1 f_1 + \dotsb + c_m f_m$ is zero or real-rooted.

**Theorem (Chudnovsky–Seymour).** For real-rooted polynomials with positive
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

This is the interlacing input for the real-rootedness of independence
polynomials of claw-free graphs; see the
[Chudnovsky–Seymour page](/RealRooted/theorems/chudnovsky-seymour/).

## References

M. Chudnovsky and P. Seymour, “The roots of the independence polynomial of a
clawfree graph,” *J. Combin. Theory Ser. B* 97 (2007), 350–357.
P. Brändén, [“Unimodality, log-concavity, real-rootedness and
beyond,”](https://arxiv.org/abs/1410.6601) in *Handbook of Enumerative
Combinatorics*, CRC Press (2015), Section 7.8.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CommonInterleaver` and `RealRooted.Compatibility`.
-/
