import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity from finite truncations

This file transfers total nonnegativity from a compatible family of finite
principal truncations to a matrix indexed by the natural numbers.
-/

namespace Matrix

/-- Total nonnegativity of a matrix indexed by `ℕ` can be checked on a
compatible family of finite principal truncations. -/
protected theorem IsTotallyNonneg.of_fin_truncations
    {R : Type*} [CommRing R] [PartialOrder R] (M : Matrix ℕ ℕ R)
    (Mfin : (N : ℕ) → Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hentry : ∀ (N : ℕ) (i j : Fin (N + 1)), Mfin N i j = M i.val j.val)
    (hfin : ∀ N, (Mfin N).IsTotallyNonneg) : M.IsTotallyNonneg := by
  intro n rows cols hrows hcols
  cases n with
  | zero =>
      have hempty : StrictMono (Fin.elim0 : Fin 0 → Fin 1) := by
        intro i
        exact Fin.elim0 i
      have hone := hfin 0 (n := 0) (rows := Fin.elim0)
        (cols := Fin.elim0) hempty hempty
      simpa using hone
  | succ n =>
      let B := max (rows (Fin.last n)) (cols (Fin.last n))
      let rows' : Fin (n + 1) → Fin (B + 1) := fun i =>
        ⟨rows i, Nat.lt_succ_of_le <|
          le_trans (hrows.monotone (Fin.le_last i)) (le_max_left _ _)⟩
      let cols' : Fin (n + 1) → Fin (B + 1) := fun i =>
        ⟨cols i, Nat.lt_succ_of_le <|
          le_trans (hcols.monotone (Fin.le_last i)) (le_max_right _ _)⟩
      have hrows' : StrictMono rows' := by
        intro i j hij
        exact Fin.lt_def.mpr (hrows hij)
      have hcols' : StrictMono cols' := by
        intro i j hij
        exact Fin.lt_def.mpr (hcols hij)
      have hminor : M.submatrix rows cols = (Mfin B).submatrix rows' cols' := by
        ext i j
        symm
        exact hentry B (rows' i) (cols' j)
      rw [hminor]
      exact hfin B hrows' hcols'

end Matrix
