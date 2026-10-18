/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Nested power-series constants

This Mathlib-shaped shim records the multiplication rule for the composite
constant map from a coefficient ring to polynomials and then to power series.
-/

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The composite constant map from `R` to `R[X]⟦Y⟧` preserves multiplication. -/
theorem C_C_mul (a b : R) :
    C (Polynomial.C a) * C (Polynomial.C b) = C (Polynomial.C (a * b)) := by
  rw [← map_mul, ← Polynomial.C_mul]

end PowerSeries
