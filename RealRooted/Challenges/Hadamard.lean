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

/-- Challenge-facing name for the fixed-degree Schur--Szego composition. -/
noncomputable abbrev SchurSzegoComposition (n : Nat) (f g : ℝ[X]) : ℝ[X] :=
  schurSzegoComp n f g

/-- Challenge-facing name for coefficientwise Hadamard product. -/
noncomputable abbrev HadamardProduct (p q : ℝ[X]) : ℝ[X] :=
  hadamardProduct p q

/-- Challenge-facing name for polynomial-side Pólya-frequency. -/
abbrev PolyaFrequencyPolynomial (p : ℝ[X]) : Prop :=
  IsPFPolynomial p

/-- Challenge-facing name for a nonnegative-coefficient proper-position pair. -/
abbrev NonnegativeProperPositionPair (f g : ℝ[X]) : Prop :=
  HasNonnegCoeffs f ∧ HasNonnegCoeffs g ∧ Prec f g

/-- Fixed-degree Schur--Szego composition theorem. -/
theorem finiteSchurSzegoComposition :
    ∀ {n : ℕ} {f p : ℝ[X]},
      PolyaFrequencyPolynomial f →
      f.natDegree ≤ n →
      p.natDegree ≤ n →
      p.Splits →
        SchurSzegoComposition n f p = 0 ∨ (SchurSzegoComposition n f p).Splits :=
  RealRooted.finiteSchurSzegoComposition

/-- Finite Polya--Schur theorem in the nonnegative-coefficient convention. -/
theorem finitePolyaSchur_nonneg :
    ∀ {n : ℕ} {gamma : ℕ → ℝ},
      (∀ k, 0 ≤ gamma k) →
        (IsFiniteMultiplierSequence n gamma ↔
          PolyaFrequencyPolynomial (jensenPolynomial n gamma)) :=
  RealRooted.finitePolyaSchur_nonneg

/-- Garloff--Wagner proper-position Hadamard theorem. -/
theorem garloffWagnerHadamardNonnegPrec :
    ∀ {f g p q : ℝ[X]},
      NonnegativeProperPositionPair f g →
      NonnegativeProperPositionPair p q →
      Prec0 (HadamardProduct f p) (HadamardProduct g q) :=
  fun hfg hpq =>
    RealRooted.garloffWagnerHadamardNonnegPrec
      hfg.1 hfg.2.1 hpq.1 hpq.2.1 hfg.2.2 hpq.2.2

end Hadamard
end Challenges
end RealRooted
