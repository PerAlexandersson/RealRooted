import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.CombinatorialExamples.TypeBEulerian

open Polynomial

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

namespace RealRooted
namespace Challenges
namespace Eulerian

/-- Challenge-facing name for the ordinary Eulerian polynomial normalization
used in this project. -/
noncomputable abbrev OrdinaryEulerianPolynomial (n : Nat) : ℝ[X] :=
  eulerianTilde n

/-- Challenge-facing name for the ordinary Eulerian Sturm prefix. -/
noncomputable abbrev OrdinaryEulerianPrefix (n : Nat) : List ℝ[X] :=
  eulerianTildePrefix n

/-- Challenge-facing name for the type `B` Eulerian polynomials. -/
noncomputable abbrev TypeBEulerianPolynomial (n : Nat) : ℝ[X] :=
  typeBEulerian n

/-- Challenge-facing name for the type `B` Eulerian Sturm prefix. -/
noncomputable abbrev TypeBEulerianPrefix (n : Nat) : List ℝ[X] :=
  typeBEulerianPrefix n

/-- Challenge-facing predicate for a real-rooted polynomial family. -/
abbrev RealRootedPolynomialFamily (A : Nat → ℝ[X]) : Prop :=
  ∀ n : Nat, A n ≠ 0 ∧ (A n).Splits

/-- Challenge-facing predicate for consecutive interlacing in a polynomial family. -/
abbrev ConsecutiveInterlacing (A : Nat → ℝ[X]) : Prop :=
  ∀ n : Nat, Interlaces (A n) (A (n + 1))

/-- Challenge-facing predicate for Sturm prefixes attached to a polynomial family. -/
abbrev SturmPrefixFamily (pref : Nat → List ℝ[X]) : Prop :=
  ∀ n : Nat, IsSturmSeq (pref n)

/-- Ordinary Eulerian tilde polynomials are real-rooted. -/
theorem realRooted :
    RealRootedPolynomialFamily OrdinaryEulerianPolynomial :=
  RealRooted.isRealRooted_eulerianTilde

/-- Consecutive ordinary Eulerian tilde polynomials interlace. -/
theorem interlaces_succ :
    ConsecutiveInterlacing OrdinaryEulerianPolynomial :=
  RealRooted.interlaces_eulerianTilde_succ

/-- Descending ordinary Eulerian prefixes form Sturm sequences. -/
theorem sturmPrefix :
    SturmPrefixFamily OrdinaryEulerianPrefix :=
  RealRooted.isSturmSeq_eulerianTildePrefix

/-- Type `B` Eulerian polynomials are real-rooted. -/
theorem typeB_realRooted :
    RealRootedPolynomialFamily TypeBEulerianPolynomial :=
  RealRooted.isRealRooted_typeBEulerian

/-- Consecutive type `B` Eulerian polynomials interlace. -/
theorem typeB_interlaces_succ :
    ConsecutiveInterlacing TypeBEulerianPolynomial :=
  RealRooted.interlaces_typeBEulerian_succ

/-- Descending type `B` Eulerian prefixes form Sturm sequences. -/
theorem typeB_sturmPrefix :
    SturmPrefixFamily TypeBEulerianPrefix :=
  RealRooted.isSturmSeq_typeBEulerianPrefix

end Eulerian
end Challenges
end RealRooted
