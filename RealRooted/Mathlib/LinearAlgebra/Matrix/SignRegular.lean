import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Sign-consistent and sign-regular rectangular matrices

This file introduces orientation-free predicates for Karlin's sign-consistent
and sign-regular matrices. Two minors have a common weak (respectively strict)
sign exactly when their product is nonnegative (respectively positive).
-/

public section

namespace Matrix

variable {R ι κ : Type*} [CommRing R] [PartialOrder R]
variable [Preorder ι] [Preorder κ]

/-- The minors of order `q` of `M` have a common weak sign. -/
def IsSignConsistentOrder (M : Matrix ι κ R) (q : ℕ) : Prop :=
  ∀ ⦃rows rows' : Fin q → ι⦄ ⦃cols cols' : Fin q → κ⦄,
    StrictMono rows → StrictMono rows' → StrictMono cols → StrictMono cols' →
      0 ≤ (M.submatrix rows cols).det * (M.submatrix rows' cols').det

/-- The minors of order `q` of `M` are nonzero and have a common strict sign. -/
def IsStrictlySignConsistentOrder (M : Matrix ι κ R) (q : ℕ) : Prop :=
  ∀ ⦃rows rows' : Fin q → ι⦄ ⦃cols cols' : Fin q → κ⦄,
    StrictMono rows → StrictMono rows' → StrictMono cols → StrictMono cols' →
      0 < (M.submatrix rows cols).det * (M.submatrix rows' cols').det

/-- A matrix is sign regular if its minors have a common weak sign at every order. -/
def IsSignRegular (M : Matrix ι κ R) : Prop :=
  ∀ q, M.IsSignConsistentOrder q

/-- A matrix is strictly sign regular if its minors have a common strict sign
at every order. -/
def IsStrictlySignRegular (M : Matrix ι κ R) : Prop :=
  ∀ q, M.IsStrictlySignConsistentOrder q

protected lemma IsStrictlySignConsistentOrder.toSignConsistentOrder
    {M : Matrix ι κ R} {q : ℕ} (hM : M.IsStrictlySignConsistentOrder q) :
    M.IsSignConsistentOrder q := by
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  exact (hM hrows hrows' hcols hcols').le

protected lemma IsStrictlySignRegular.toSignRegular {M : Matrix ι κ R}
    (hM : M.IsStrictlySignRegular) : M.IsSignRegular :=
  fun q ↦ (hM q).toSignConsistentOrder

section OrderedRing

variable [IsStrictOrderedRing R]

lemma IsTotallyNonnegRect.isSignConsistentOrder {M : Matrix ι κ R}
    (hM : M.IsTotallyNonnegRect) (q : ℕ) : M.IsSignConsistentOrder q := by
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  exact mul_nonneg (hM hrows hcols) (hM hrows' hcols')

lemma IsTotallyNonnegRect.isSignRegular {M : Matrix ι κ R}
    (hM : M.IsTotallyNonnegRect) : M.IsSignRegular :=
  fun q ↦ hM.isSignConsistentOrder q

lemma isStrictlySignConsistentOrder_of_posMinors {M : Matrix ι κ R} {q : ℕ}
    (hM :
      ∀ ⦃rows : Fin q → ι⦄ ⦃cols : Fin q → κ⦄,
        StrictMono rows → StrictMono cols → 0 < (M.submatrix rows cols).det) :
    M.IsStrictlySignConsistentOrder q := by
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  exact mul_pos (hM hrows hcols) (hM hrows' hcols')

end OrderedRing

lemma IsSignConsistentOrder.minorProduct_nonneg {M : Matrix ι κ R} {q : ℕ}
    (hM : M.IsSignConsistentOrder q) {cols : Fin q → κ} (hcols : StrictMono cols) :
    ∀ ⦃rows rows' : Fin q → ι⦄,
      StrictMono rows → StrictMono rows' →
        0 ≤ (M.submatrix rows cols).det * (M.submatrix rows' cols).det := by
  intro rows rows' hrows hrows'
  exact hM hrows hrows' hcols hcols

lemma IsStrictlySignConsistentOrder.minorProduct_pos
    {M : Matrix ι κ R} {q : ℕ} (hM : M.IsStrictlySignConsistentOrder q)
    {cols : Fin q → κ} (hcols : StrictMono cols) :
    ∀ ⦃rows rows' : Fin q → ι⦄,
      StrictMono rows → StrictMono rows' →
        0 < (M.submatrix rows cols).det * (M.submatrix rows' cols).det := by
  intro rows rows' hrows hrows'
  exact hM hrows hrows' hcols hcols

end Matrix
