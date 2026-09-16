/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Finite
import RealRooted.AissenSchoenbergWhitneyBase

/-!
# LGV path matrices as Toeplitz minors

This file is the orientation bridge between standalone LeanLGV path networks
and the Toeplitz matrices used by `RealRooted`. It deliberately contains no
path-disjointness argument and no Pólya-frequency conclusion.
-/

namespace RealRooted

noncomputable section

universe u

/-- Ordered source-row and sink-column maps describing a strict finite
Toeplitz minor. -/
structure StrictToeplitzMinorIndex (n : ℕ) where
  sourceRow : Fin n → ℕ
  sinkColumn : Fin n → ℕ
  sourceRow_strictMono : StrictMono sourceRow
  sinkColumn_strictMono : StrictMono sinkColumn

namespace StrictToeplitzMinorIndex

variable {n : ℕ}

/-- Reindex a path network using the source rows and sink columns of a strict
Toeplitz minor. -/
def pathNetwork {R : Type u} (I : StrictToeplitzMinorIndex n)
    (N : LGV.FinitePathNetwork R ℕ) : LGV.FinitePathNetwork R (Fin n) :=
  N.reindex I.sourceRow I.sinkColumn

/-- The Toeplitz submatrix selected by the source rows and sink columns. -/
def toeplitzSubmatrix {R : Type u} [Zero R] (I : StrictToeplitzMinorIndex n)
    (a : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  (toeplitz a).submatrix I.sourceRow I.sinkColumn

/-- Reindexing selects the path-matrix submatrix in source-row,
sink-column orientation. -/
@[simp]
theorem pathNetwork_matrix {R : Type u} [AddCommMonoid R]
    (I : StrictToeplitzMinorIndex n) (N : LGV.FinitePathNetwork R ℕ) :
    (I.pathNetwork N).matrix =
      N.matrix.submatrix I.sourceRow I.sinkColumn :=
  LGV.FinitePathNetwork.reindex_matrix N I.sourceRow I.sinkColumn

/-- If a path matrix is Toeplitz, its strict reindexing is exactly the
corresponding Toeplitz submatrix, with no row/column transpose. -/
theorem pathNetwork_matrix_eq_toeplitzSubmatrix
    {R : Type u} [AddCommMonoid R] (I : StrictToeplitzMinorIndex n)
    (N : LGV.FinitePathNetwork R ℕ) (a : ℕ → R)
    (hN : N.matrix = toeplitz a) :
    (I.pathNetwork N).matrix = I.toeplitzSubmatrix a := by
  rw [pathNetwork_matrix, hN]
  rfl

/-- Determinant form of the source-row/sink-column Toeplitz orientation. -/
theorem det_pathNetwork_eq_toeplitzSubmatrix
    {R : Type u} [CommRing R] (I : StrictToeplitzMinorIndex n)
    (N : LGV.FinitePathNetwork R ℕ) (a : ℕ → R)
    (hN : N.matrix = toeplitz a) :
    Matrix.det (I.pathNetwork N).matrix =
      Matrix.det (I.toeplitzSubmatrix a) := by
  rw [I.pathNetwork_matrix_eq_toeplitzSubmatrix N a hN]

end StrictToeplitzMinorIndex

end

end RealRooted
