import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.CombinatorialExamples.TypeBEulerian

open Polynomial

/-!
# Eulerian polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "eulerian"
authors = ["Frobenius", "Brenti"]
years = [1910, 1994]

[[definitions]]
name = "RealRooted.eulerianTilde"
module = "RealRooted.CombinatorialExamples.Eulerian"

[[definitions]]
name = "RealRooted.typeBEulerian"
module = "RealRooted.CombinatorialExamples.TypeBEulerian"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.realRooted"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.interlaces_succ"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.typeB_realRooted"

[[theorems]]
name = "RealRooted.Challenges.Eulerian.typeB_interlaces_succ"
-->

<!-- realrooted-catalog-content -->
# Eulerian polynomials

The ordinary and type `B` Eulerian polynomials satisfy derivative recurrences.
Both families are real-rooted, and consecutive polynomials interlace.

## References

The ordinary Eulerian recurrence and its real-rootedness go back to
F. G. Frobenius, “Über die Bernoullischen Zahlen und die Eulerschen Polynome,”
Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften
(1910), 809–847.  The type `B` family is the standard type `B` Eulerian
polynomial recurrence; see F. Brenti, [“q-Eulerian polynomials arising from
Coxeter groups,”](https://doi.org/10.1006/eujc.1994.1046) *European Journal of
Combinatorics* 15 (1994), 417–441.  Its formal recurrence and proofs are in the
imported `RealRooted.CombinatorialExamples.TypeBEulerian` module.  Additional
context appears in the
[Eulerian-polynomial entry on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedWords.htm#eulerianPolynomial).
<!-- /realrooted-catalog-content -->

Human statements:

* Eulerian polynomials:
  https://www.symmetricfunctions.com/realRootedWords.htm#eulerianPolynomial
* Eulerian Sturm sequence example:
  https://www.symmetricfunctions.com/realRootedWords.htm#ex:eulerianSturm
* Type `B` Eulerian polynomials:
  https://www.symmetricfunctions.com/realRootedWords.htm#typeBEulerianPolynomial

Classical origin: F. G. Frobenius, "Über die Bernoullischen Zahlen und die
Eulerschen Polynome", Sitzungsberichte der Königlich Preussischen Akademie der
Wissenschaften (1910), 809--847.

This module exposes the checked ordinary and type `B` Eulerian real-rootedness
and interlacing statements, together with the corresponding Sturm-prefix API.
-/

namespace RealRooted
namespace Challenges
namespace Eulerian

/-- Ordinary Eulerian tilde polynomials are real-rooted. -/
theorem realRooted :
    ∀ n : Nat, eulerianTilde n ≠ 0 ∧ (eulerianTilde n).Splits :=
  RealRooted.isRealRooted_eulerianTilde

/-- Consecutive ordinary Eulerian tilde polynomials interlace. -/
theorem interlaces_succ :
    ∀ n : Nat, Interlaces (eulerianTilde n) (eulerianTilde (n + 1)) :=
  RealRooted.interlaces_eulerianTilde_succ

/-- Descending ordinary Eulerian prefixes form Sturm sequences. -/
theorem sturmPrefix :
    ∀ n : Nat, IsSturmSeq (eulerianTildePrefix n) :=
  RealRooted.isSturmSeq_eulerianTildePrefix

/-- Type `B` Eulerian polynomials are real-rooted. -/
theorem typeB_realRooted :
    ∀ n : Nat, typeBEulerian n ≠ 0 ∧ (typeBEulerian n).Splits :=
  RealRooted.isRealRooted_typeBEulerian

/-- Consecutive type `B` Eulerian polynomials interlace. -/
theorem typeB_interlaces_succ :
    ∀ n : Nat, Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) :=
  RealRooted.interlaces_typeBEulerian_succ

/-- Descending type `B` Eulerian prefixes form Sturm sequences. -/
theorem typeB_sturmPrefix :
    ∀ n : Nat, IsSturmSeq (typeBEulerianPrefix n) :=
  RealRooted.isSturmSeq_typeBEulerianPrefix

end Eulerian
end Challenges
end RealRooted
