import RealRooted.CommonInterleaver.FamilyUpgrade
import RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility
import RealRooted.CommonInterleaver.PairwiseUpgrade.LowDegree
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

[[definitions]]
name = "RealRooted.PairwiseHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.RootDesc"

[[definitions]]
name = "RealRooted.Compatible"
module = "RealRooted.Compatibility.Pair"

[[definitions]]
name = "RealRooted.FamilyCompatible"
module = "RealRooted.Compatibility.Basic"

[[theorems]]
name = "RealRooted.hasCommonInterleaver_of_pairwiseHasCommonInterleaver"
module = "RealRooted.CommonInterleaver.FamilyUpgrade"

[[theorems]]
name = "RealRooted.isRealRooted_sum_of_commonInterleaver"
module = "RealRooted.CommonInterleaver.FamilyUpgrade"

[[theorems]]
name = "RealRooted.familyCompatible_of_commonInterleaver"
module = "RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility"

[[theorems]]
name = "RealRooted.pairwiseCompatible_of_pairwiseHasCommonInterleaver"
module = "RealRooted.Compatibility.InterleaverBridge"

[[theorems]]
name = "RealRooted.chudnovskySeymour_fourWay_of_natDegree_le_two"
module = "RealRooted.CommonInterleaver.PairwiseUpgrade.LowDegree"
-->

<!-- realrooted-catalog-content -->
# Common interleavers

A finite family of real-rooted polynomials `f_1, …, f_m` has a **common
interleaver** if a single real-rooted `h` satisfies `f_i ≪ h` for every `i`.
The family is **compatible** if every nonnegative combination
`c_1 f_1 + ⋯ + c_m f_m` is zero or real-rooted.

For polynomials with positive leading coefficients, the following are
formalized:

- **Pairwise to global:** if every pair has a common interleaver, then the
  whole family has one.
- **Common interleavers give compatibility:** if the family has a common
  interleaver, then every nonnegative combination is real-rooted; in
  particular the sum is real-rooted.
- **Compatible pairs:** a pair with a common interleaver is compatible.

Chudnovsky and Seymour show that for such families all four conditions agree:
pairwise compatibility, pairwise common interleavers, a common interleaver,
and compatibility. The library proves this four-way equivalence for degree at
most two. In general it holds once the two-polynomial converse is supplied:
a compatible pair has a common interleaver
(`CompatiblePairHasCommonRightInterleaverStatement`). That converse remains
open in the library.

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
