module

import RealRooted.Mathlib.Algebra.LinearRecurrence.Veronese
import RealRooted.VeroneseSection
import RealRooted.Tactic.Examples.RowData
import RealRooted.Tactic.Examples.RowInterlacing

/-!
# Veronese recurrence breadth examples

We reuse the binomial rows, Fibonacci tiling rows and Delannoy triangle rows already
defined in the regression suite. Each example only packages the source recurrence
and applies the general transport theorem. The resulting orders are two, six and four.
-/

open Polynomial
open RealRooted.Tactic.RowDataExamples RealRooted.Tactic.RowInterlacingExamples

namespace RealRooted.Tactic.VeroneseRecurrenceExamples

noncomputable section

-- Binomial rows: `R₀ = 1`, `Rₙ₊₁ = (1 + X) Rₙ`; even and odd sections.
example {i : ℕ} (hi : i < 2) :
    let E : LinearRecurrence ℝ[X] := ⟨1, ![1 + X]⟩
    (E.veronese 2).order = 2 ∧
      (E.veronese 2).IsSolution (fun n => veroneseSectionPolynomial 2 i (binomialRows n)) := by
  let E : LinearRecurrence ℝ[X] := ⟨1, ![1 + X]⟩
  have hE : E.IsSolution binomialRows := by
    intro n
    simp [E, binomialRows]
  exact ⟨rfl, by
    simpa only [veroneseSectionPolynomial_eq_veroneseSection] using hE.veronese (by decide) hi⟩

-- Fibonacci tiling rows: `R₀ = R₁ = 1`, `Rₙ₊₂ = Rₙ₊₁ + X Rₙ`; all three sections.
example {i : ℕ} (hi : i < 3) :
    let E : LinearRecurrence ℝ[X] := ⟨2, ![X, 1]⟩
    (E.veronese 3).order = 6 ∧
      (E.veronese 3).IsSolution (fun n => veroneseSectionPolynomial 3 i (A011973 n)) := by
  let E : LinearRecurrence ℝ[X] := ⟨2, ![X, 1]⟩
  have hE : E.IsSolution A011973 := by
    intro n
    simp [E, Fin.sum_univ_two, A011973, add_comm]
  exact ⟨rfl, by
    simpa only [veroneseSectionPolynomial_eq_veroneseSection] using hE.veronese (by decide) hi⟩

-- Delannoy triangle rows: `R₀ = 1`, `R₁ = 1 + X`, `Rₙ₊₂ = (1 + X) Rₙ₊₁ + X Rₙ`.
example {i : ℕ} (hi : i < 2) :
    let E : LinearRecurrence ℝ[X] := ⟨2, ![X, 1 + X]⟩
    (E.veronese 2).order = 4 ∧
      (E.veronese 2).IsSolution (fun n => veroneseSectionPolynomial 2 i (A008288 n)) := by
  let E : LinearRecurrence ℝ[X] := ⟨2, ![X, 1 + X]⟩
  have hE : E.IsSolution A008288 := by
    intro n
    simp [E, Fin.sum_univ_two, A008288, add_comm]
  exact ⟨rfl, by
    simpa only [veroneseSectionPolynomial_eq_veroneseSection] using hE.veronese (by decide) hi⟩

end

end RealRooted.Tactic.VeroneseRecurrenceExamples
