import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.CombinatorialExamples.TypeBEulerian

/-!
# Eulerian polynomial challenge entry point

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
and Sturm-sequence statements.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Eulerian

/-- Ordinary Eulerian tilde polynomials are real-rooted. -/
theorem realRooted :
    ∀ n : Nat, (eulerianTilde n) ≠ 0 ∧ (eulerianTilde n).Splits :=
  RealRooted.isRealRooted_eulerianTilde

/-- Consecutive ordinary Eulerian tilde polynomials interlace. -/
theorem interlaces_succ (n : Nat) :
    Interlaces (eulerianTilde n) (eulerianTilde (n + 1)) :=
  RealRooted.interlaces_eulerianTilde_succ n

/-- Descending ordinary Eulerian prefixes form Sturm sequences. -/
theorem sturmPrefix :
    ∀ n : Nat, IsSturmSeq (eulerianTildePrefix n) :=
  RealRooted.isSturmSeq_eulerianTildePrefix

/-- Type `B` Eulerian polynomials are real-rooted. -/
theorem typeB_realRooted :
    ∀ n : Nat, (typeBEulerian n) ≠ 0 ∧ (typeBEulerian n).Splits :=
  RealRooted.isRealRooted_typeBEulerian

/-- Consecutive type `B` Eulerian polynomials interlace. -/
theorem typeB_interlaces_succ (n : Nat) :
    Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) :=
  RealRooted.interlaces_typeBEulerian_succ n

/-- Descending type `B` Eulerian prefixes form Sturm sequences. -/
theorem typeB_sturmPrefix :
    ∀ n : Nat, IsSturmSeq (typeBEulerianPrefix n) :=
  RealRooted.isSturmSeq_typeBEulerianPrefix

end Eulerian
end Challenges
end RealRooted
