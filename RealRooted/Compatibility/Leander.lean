import RealRooted.Compatibility.LeanderXOutput

open Polynomial

noncomputable section

namespace RealRooted

/-- Leander Theorem 2.3: the diagonal-omitting transform preserves both
ordered compatibility conditions.

No output positive-leading claim is included: for a singleton family the
transform output is identically zero. -/
theorem leanderTransform_preserves_compatibility {n : ℕ}
    (f : Fin n → ℝ[X])
    (hpos : ∀ h, HasPosLeadingCoeff (f h))
    (hnn : ∀ h, HasNonnegCoeffs (f h))
    (hff : ∀ ⦃i j⦄, i ≤ j → Compatible (f i) (f j))
    (hXf : ∀ ⦃i j⦄, i ≤ j → Compatible (X * f i) (f j)) :
    (∀ ⦃i j⦄, i ≤ j →
      Compatible (leanderTransform f i) (leanderTransform f j)) ∧
    (∀ ⦃i j⦄, i ≤ j →
      Compatible (X * leanderTransform f i) (leanderTransform f j)) := by
  have hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits := fun h =>
    (hff le_rfl).isRealRooted_left (hpos h)
  constructor
  · intro i j hij
    exact compatible_leanderTransform f hrr hpos hnn
      (fun {_ _} hlt => hff (le_of_lt hlt))
      (fun {_ _} hlt => hXf (le_of_lt hlt)) hij
  · intro i j hij
    exact compatible_X_mul_leanderTransform f hrr hpos hnn
      (fun {_ _} hlt => hff (le_of_lt hlt))
      (fun {_ _} hlt => hXf (le_of_lt hlt)) hij

/-- The two-coordinate endpoint of Leander's transform: `[f₀, f₁]` is sent
to `[f₁, X * f₀]`, and both ordered compatibility conditions are preserved. -/
theorem leanderTransform_two_compatible (f : Fin 2 → ℝ[X])
    (hpos : ∀ h, HasPosLeadingCoeff (f h))
    (hnn : ∀ h, HasNonnegCoeffs (f h))
    (hff : ∀ ⦃i j⦄, i ≤ j → Compatible (f i) (f j))
    (hXf : ∀ ⦃i j⦄, i ≤ j → Compatible (X * f i) (f j)) :
    Compatible (f 1) (X * f 0) ∧
      Compatible (X * f 1) (X * f 0) := by
  have h := leanderTransform_preserves_compatibility f hpos hnn hff hXf
  have h01 : (0 : Fin 2) ≤ 1 := by decide
  simpa using And.intro (h.1 h01) (h.2 h01)

end RealRooted
