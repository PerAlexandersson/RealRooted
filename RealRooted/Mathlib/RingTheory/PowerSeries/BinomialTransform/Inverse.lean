/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform

/-!
# Inverting a formal binomial transform
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Translation by zero fixes the formal series. -/
@[simp] theorem binomialTransform_zero (f : R⟦X⟧) : binomialTransform 0 f = f := by
  ext n
  simp only [coeff_binomialTransform, Polynomial.momentTranslate_zero_left]

/-- Negative translation inverts the formal binomial transform. -/
@[simp] theorem binomialTransform_neg_cancel (c : R) (f : R⟦X⟧) :
    binomialTransform (-c) (binomialTransform c f) = f := by
  rw [binomialTransform_binomialTransform, neg_add_cancel, binomialTransform_zero]

end PowerSeries
