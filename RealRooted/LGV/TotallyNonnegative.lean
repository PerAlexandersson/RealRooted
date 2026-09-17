/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Ordered
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity from ordered LGV certificates

This file connects the determinant nonnegativity theorem in standalone
LeanLGV to the total-nonnegativity interface in `RealRooted`.  It is neutral
about the shape of the path matrix: Toeplitz and Pólya-frequency consequences
belong in downstream adapters.
-/

namespace LGV.FinitePathNetwork

noncomputable section

universe u v

/-- If every strictly ordered finite minor of a path network has an ordered
LGV cancellation certificate, then nonnegative path weights make its path
matrix totally nonnegative. -/
theorem matrix_isTotallyNonneg_of_orderedCertificates
    {R : Type u} {ι : Type v}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [PartialOrder ι]
    (N : LGV.FinitePathNetwork R ι)
    (certificate : ∀ {n : ℕ} {rows cols : Fin n → ι},
      StrictMono rows → StrictMono cols →
        OrderedCancellationCertificate (N.reindex rows cols))
    (hweight : ∀ {s t : ι} (p : N.Path s t), 0 ≤ N.weight p) :
    N.matrix.IsTotallyNonneg := by
  intro n rows cols hrows hcols
  rw [← N.reindex_matrix rows cols]
  exact (certificate hrows hcols).det_nonneg fun p ↦ hweight p

end

end LGV.FinitePathNetwork
