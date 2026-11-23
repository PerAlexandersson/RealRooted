/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.Resolvent
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing formal matrix resolvents
-/

public section

namespace Matrix

variable {R ι κ : Type*} [CommRing R]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Simultaneous reindexing preserves every formal resolvent entry. -/
theorem powerSeriesResolvent_submatrix_equiv (A : Matrix ι ι R) (e : κ ≃ ι) (i j : κ) :
    powerSeriesResolvent (A.submatrix e e) i j = powerSeriesResolvent A (e i) (e j) := by
  ext n
  rw [coeff_powerSeriesResolvent, coeff_powerSeriesResolvent]
  have h := congrArg (fun M : Matrix κ κ R => M i j)
    ((reindexRingEquiv R e.symm).map_pow A n)
  exact h.symm

end Matrix
