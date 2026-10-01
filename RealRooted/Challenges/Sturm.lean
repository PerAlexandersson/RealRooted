import RealRooted.RootCounting.Sturm

/-!
# Sturm root-counting challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "sturm-root-counting"
authors = ["Sturm"]
years = [1829]

[[definitions]]
name = "Polynomial.signedRemainderSequence"
module = "RealRooted.Mathlib.Algebra.Polynomial.Sturm"
label = "Signed remainder sequence"

[[definitions]]
name = "RealRooted.sturmVariations"
module = "RealRooted.RootCounting.Sturm"
label = "Sign variations of the Sturm sequence"

[[definitions]]
name = "RealRooted.distinctRootCountIoo"
module = "RealRooted.RootCounting.Sturm"
label = "Number of distinct roots in an interval"

[[theorems]]
name = "RealRooted.distinctRootCountIoo_eq_distinctSturmVariations_sub"
module = "RealRooted.RootCounting.Sturm"
label = "Sturm's theorem"

[[theorems]]
name = "RealRooted.splits_iff_distinctSturmVariations_sub_eq_natDegree"
module = "RealRooted.RootCounting.Sturm"
label = "A Sturm test for real-rootedness"
-->

<!-- realrooted-catalog-content -->
# Sturm root counting

Evaluate the signed Euclidean remainder sequence of a polynomial and its
derivative at the two endpoints of an interval, omit zero values, and count
sign changes. The drop in sign changes is exactly the number of distinct real
roots in the open interval.

Repeated factors are removed by a canonical squarefree normalization. If the
interval contains every root, the same count tests whether all roots are real.

## References

J. C. F. Sturm, “Mémoire sur la résolution des équations numériques,”
*Bulletin des Sciences de Férussac* 11 (1829), 419–422. See also the root-counting
overview on [symmetricfunctions.com][sturm-overview].

[sturm-overview]: https://www.symmetricfunctions.com/realRootedInterlacing.htm#sturmRootCounting
<!-- /realrooted-catalog-content -->

This module exposes the reusable implementation in
`RealRooted.RootCounting.Sturm`.
-/

namespace RealRooted
namespace Challenges
namespace Sturm

export RealRooted
  (distinctRootCountIoo_eq_distinctSturmVariations_sub
    splits_iff_distinctSturmVariations_sub_eq_natDegree)

end Sturm
end Challenges
end RealRooted
