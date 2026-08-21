import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.CauchyBinet
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Compound matrices

The `q`-th **compound matrix** of `A` collects all `q × q` minors of `A`, indexed
by the increasing `q`-element selections of rows and columns.  Its two basic
properties are:

* multiplicativity, `compound q (L * A) = compound q L * compound q A`, which is
  exactly the Cauchy-Binet expansion re-indexed;
* entrywise nonnegativity for totally nonnegative `A`, which is immediate from
  the definitions.

These are the two inputs the Gantmacher-Krein route needs before the spectral
step (that the eigenvalues of `compound q A` are the `q`-fold products of the
eigenvalues of `A`), which is not proved here.
-/

open scoped BigOperators

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The increasing enumeration of a `q`-element selection, as a function. -/
def powersetEnum {n q : ℕ} (s : Set.powersetCard (Fin n) q) : Fin q → Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm s

theorem strictMono_powersetEnum {n q : ℕ} (s : Set.powersetCard (Fin n) q) :
    StrictMono (powersetEnum s) :=
  (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono

/-- The `q`-th compound matrix: its `(s, t)` entry is the minor of `A` on the
rows selected by `s` and the columns selected by `t`. -/
def compound {m n : ℕ} (q : ℕ) (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Set.powersetCard (Fin m) q) (Set.powersetCard (Fin n) q) R :=
  fun s t => (A.submatrix (powersetEnum s) (powersetEnum t)).det

@[simp] theorem compound_apply {m n q : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Set.powersetCard (Fin m) q) (t : Set.powersetCard (Fin n) q) :
    compound q A s t = (A.submatrix (powersetEnum s) (powersetEnum t)).det := rfl

/-- **Compound matrices are multiplicative.**  This is the Cauchy-Binet
expansion, re-indexed. -/
theorem compound_mul {l n m : ℕ} (q : ℕ)
    (L : Matrix (Fin l) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) :
    compound q (L * A) = compound q L * compound q A := by
  ext s t
  rw [compound_apply, Matrix.mul_apply]
  rw [Matrix.det_submatrix_mul_eq_sum_powersetCard]
  rfl

/-- A totally nonnegative matrix has an entrywise nonnegative compound matrix. -/
theorem compound_nonneg {m n : ℕ} [PartialOrder R] (q : ℕ)
    {A : Matrix (Fin m) (Fin n) R} (hA : A.IsTotallyNonnegRect)
    (s : Set.powersetCard (Fin m) q) (t : Set.powersetCard (Fin n) q) :
    0 ≤ compound q A s t :=
  hA (strictMono_powersetEnum s) (strictMono_powersetEnum t)

/-- The first compound matrix is `A` itself, up to the canonical indexing. -/
theorem compound_one_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Set.powersetCard (Fin m) 1) (t : Set.powersetCard (Fin n) 1) :
    compound 1 A s t = A (powersetEnum s 0) (powersetEnum t 0) := by
  rw [compound_apply, Matrix.det_fin_one]
  rfl

end Matrix
