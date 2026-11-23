/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Aeration
public import RealRooted.Mathlib.MeasureTheory.Measure.AeratedMoments

/-!
# Aerated moments as a square-variable formal series
-/

public section

namespace PowerSeries

/-- The ordinary series of the aerated moment sequence is the square-variable substitution. -/
theorem mk_aeratedMoment (m : ℕ → ℝ) :
    mk (MeasureTheory.aeratedMoment m) = (mk m).subst (X ^ 2 : ℝ⟦X⟧) := by
  ext n
  simp only [coeff_mk, coeff_subst_X_sq, MeasureTheory.aeratedMoment]

end PowerSeries
