import RealRooted.Hadamard

/-!
# Hadamard challenge entry point

Human statements:

* Hadamard product theorems:
  https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems
* Schur--Szego composition:
  https://www.symmetricfunctions.com/realRooted.htm#schurSzegoComposition
* Polya-frequency sequences:
  https://www.symmetricfunctions.com/polyaFrequency.htm#aissenSchoenbergWhitney

Original publications include:

* G. Polya and I. Schur, "Ueber zwei Arten von Faktorenfolgen in der Theorie
  der algebraischen Gleichungen", J. Reine Angew. Math. 144 (1914), 89--113.
* D. G. Wagner, "Total positivity of Hadamard products", J. Math. Anal. Appl.
  163 (1992), 459--483.
* J. Garloff and D. G. Wagner, "Hadamard products of stable polynomials are
  stable", J. Math. Anal. Appl. 202 (1996), 797--809.

This module exposes the main theorem interfaces.  The reduction graph,
Hurwitz-matrix routes, and low-degree support lemmas remain in
`RealRooted.Hadamard`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Hadamard

/-- Fixed-degree Schur--Szego composition theorem. -/
theorem finiteSchurSzegoComposition :
    RealRooted.finiteSchurSzegoCompositionStatement :=
  RealRooted.finiteSchurSzegoComposition

/-- Finite Polya--Schur theorem in the nonnegative-coefficient convention. -/
theorem finitePolyaSchur_nonneg :
    RealRooted.finitePolyaSchurNonnegStatement :=
  RealRooted.finitePolyaSchur_nonneg

/-- Garloff--Wagner proper-position Hadamard target. -/
abbrev garloffWagnerHadamardNonnegPrecTarget : Prop :=
  RealRooted.garloffWagnerHadamardNonnegPrecStatement

/-- Garloff--Wagner target from the bundled classical inputs. -/
theorem garloffWagnerHadamardNonnegPrec_of_classicalInputs
    (h : RealRooted.GarloffWagnerClassicalInputs) :
    garloffWagnerHadamardNonnegPrecTarget :=
  RealRooted.garloffWagnerHadamardNonnegPrec_of_classicalInputsBundle h

/-- PF-polynomial closure under Hadamard product from bundled classical inputs. -/
theorem hadamardProduct_preserves_pf_of_classicalInputs
    (h : RealRooted.GarloffWagnerClassicalInputs)
    {p q : ℝ[X]}
    (hp : IsPFPolynomial p)
    (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  RealRooted.hadamardProduct_preserves_pf_of_classicalInputsBundle h hp hq

end Hadamard
end Challenges
end RealRooted
