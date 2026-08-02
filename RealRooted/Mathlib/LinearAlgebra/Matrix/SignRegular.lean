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

protected lemma IsSignConsistentOrder.submatrix
    {ι' κ' : Type*} [Preorder ι'] [Preorder κ'] {M : Matrix ι κ R} {q : ℕ}
    (hM : M.IsSignConsistentOrder q) {rows : ι' → ι} {cols : κ' → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    (M.submatrix rows cols).IsSignConsistentOrder q := by
  intro rows₁ rows₂ cols₁ cols₂ hrows₁ hrows₂ hcols₁ hcols₂
  simpa using hM (hrows.comp hrows₁) (hrows.comp hrows₂)
    (hcols.comp hcols₁) (hcols.comp hcols₂)

protected lemma IsStrictlySignConsistentOrder.submatrix
    {ι' κ' : Type*} [Preorder ι'] [Preorder κ'] {M : Matrix ι κ R} {q : ℕ}
    (hM : M.IsStrictlySignConsistentOrder q) {rows : ι' → ι} {cols : κ' → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    (M.submatrix rows cols).IsStrictlySignConsistentOrder q := by
  intro rows₁ rows₂ cols₁ cols₂ hrows₁ hrows₂ hcols₁ hcols₂
  simpa using hM (hrows.comp hrows₁) (hrows.comp hrows₂)
    (hcols.comp hcols₁) (hcols.comp hcols₂)

protected lemma IsSignConsistentOrder.transpose {M : Matrix ι κ R} {q : ℕ}
    (hM : M.IsSignConsistentOrder q) : M.transpose.IsSignConsistentOrder q := by
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  have hdet (r : Fin q → κ) (c : Fin q → ι) :
      (M.transpose.submatrix r c).det = (M.submatrix c r).det := by
    rw [← Matrix.det_transpose (M.submatrix c r), Matrix.transpose_submatrix]
  rw [hdet rows cols, hdet rows' cols']
  exact hM hcols hcols' hrows hrows'

protected lemma IsStrictlySignConsistentOrder.transpose {M : Matrix ι κ R} {q : ℕ}
    (hM : M.IsStrictlySignConsistentOrder q) :
    M.transpose.IsStrictlySignConsistentOrder q := by
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  have hdet (r : Fin q → κ) (c : Fin q → ι) :
      (M.transpose.submatrix r c).det = (M.submatrix c r).det := by
    rw [← Matrix.det_transpose (M.submatrix c r), Matrix.transpose_submatrix]
  rw [hdet rows cols, hdet rows' cols']
  exact hM hcols hcols' hrows hrows'

protected lemma IsSignRegular.submatrix
    {ι' κ' : Type*} [Preorder ι'] [Preorder κ'] {M : Matrix ι κ R}
    (hM : M.IsSignRegular) {rows : ι' → ι} {cols : κ' → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    (M.submatrix rows cols).IsSignRegular :=
  fun q ↦ (hM q).submatrix hrows hcols

protected lemma IsStrictlySignRegular.submatrix
    {ι' κ' : Type*} [Preorder ι'] [Preorder κ'] {M : Matrix ι κ R}
    (hM : M.IsStrictlySignRegular) {rows : ι' → ι} {cols : κ' → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    (M.submatrix rows cols).IsStrictlySignRegular :=
  fun q ↦ (hM q).submatrix hrows hcols

protected lemma IsSignRegular.transpose {M : Matrix ι κ R}
    (hM : M.IsSignRegular) : M.transpose.IsSignRegular :=
  fun q ↦ (hM q).transpose

protected lemma IsStrictlySignRegular.transpose {M : Matrix ι κ R}
    (hM : M.IsStrictlySignRegular) : M.transpose.IsStrictlySignRegular :=
  fun q ↦ (hM q).transpose

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
variable {ι' κ' : Type*} [PartialOrder ι'] [PartialOrder κ']

lemma IsTotallyNonnegRect.isSignConsistentOrder {M : Matrix ι' κ' R}
    (hM : M.IsTotallyNonnegRect) (q : ℕ) : M.IsSignConsistentOrder q := by
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  exact mul_nonneg (hM hrows hcols) (hM hrows' hcols')

lemma IsTotallyNonnegRect.isSignRegular {M : Matrix ι' κ' R}
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

section LinearOrder

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

lemma IsSignConsistentOrder.minor_nonneg_of_pos
    {M : Matrix ι κ S} {q : ℕ} (hM : M.IsSignConsistentOrder q)
    {rows₀ : Fin q → ι} {cols₀ : Fin q → κ}
    (hrows₀ : StrictMono rows₀) (hcols₀ : StrictMono cols₀)
    (href : 0 < (M.submatrix rows₀ cols₀).det)
    {rows : Fin q → ι} {cols : Fin q → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ (M.submatrix rows cols).det :=
  nonneg_of_mul_nonneg_left
    (hM hrows hrows₀ hcols hcols₀) href

lemma IsSignConsistentOrder.minor_nonpos_of_neg
    {M : Matrix ι κ S} {q : ℕ} (hM : M.IsSignConsistentOrder q)
    {rows₀ : Fin q → ι} {cols₀ : Fin q → κ}
    (hrows₀ : StrictMono rows₀) (hcols₀ : StrictMono cols₀)
    (href : (M.submatrix rows₀ cols₀).det < 0)
    {rows : Fin q → ι} {cols : Fin q → κ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    (M.submatrix rows cols).det ≤ 0 :=
  nonpos_of_mul_nonneg_left
    (hM hrows hrows₀ hcols hcols₀) href

end LinearOrder

end Matrix
