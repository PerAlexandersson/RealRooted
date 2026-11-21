module

public import Mathlib.Basic.Real.Basic

/-!
# Exact real cofactor residues
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube.RationalSeries

/-- The reversed cubic numerator at a real reciprocal root. -/
noncomputable def numeratorValue (a b c x : ℝ) : ℝ := x ^ 3 + a * x ^ 2 + b * x + c

/-- Squared distance from a real point to the selected complex root. -/
noncomputable def pairDistance (a c x : ℝ) : ℝ := (x - a) ^ 2 + c ^ 2

/-- The coefficient of a real cofactor mode. -/
noncomputable def realResidue (a c u v w x y : ℝ) : ℝ :=
  numeratorValue u v w x / (pairDistance a c x * (x - y))

/-- The exact sum of the two real cofactor modes. -/
noncomputable def modeRemainder (a c u v w x y : ℝ) (n : ℕ) : ℝ :=
  realResidue a c u v w x y * x ^ n + realResidue a c u v w y x * y ^ n

end RealRooted.EffectiveBKW.PathCube.RationalSeries
