module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Matrix
variable {ι κ R : Type*} [PartialOrder ι] [PartialOrder κ] [CommRing R] [PartialOrder R]
  {M : Matrix ι ι R} {i j : ι} {f g : κ → ι}

/-- A matrix is totally nonnegative if all its finite minors have nonnegative determinant. -/
@[expose]
def IsTotallyNonneg (M : Matrix ι ι R) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows cols : Fin n → ι⦄, StrictMono rows → StrictMono cols →
    0 ≤ (M.submatrix rows cols).det

protected lemma IsTotallyNonneg.submatrix (hM : M.IsTotallyNonneg) (hf : StrictMono f)
    (hg : StrictMono g) : (M.submatrix f g).IsTotallyNonneg :=
  fun n rows cols hrows hcols ↦ by simpa using hM (hf.comp hrows) (hg.comp hcols)

lemma IsTotallyNonneg.nonneg (hM : M.IsTotallyNonneg) (i j : ι) : 0 ≤ M i j := by
  simpa using hM (rows := ![i]) (cols := ![j])

variable [IsStrictOrderedRing R]

@[simp] protected lemma IsTotallyNonneg.zero : (0 : Matrix ι ι R).IsTotallyNonneg
  | 0 => by simp
  | n + 1 => by simp

end Matrix
