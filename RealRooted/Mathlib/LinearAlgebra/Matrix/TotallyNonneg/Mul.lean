import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.CauchyBinet
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity is closed under products

The Cauchy-Binet expansion writes a minor of a product as a sum of products of
minors, indexed by the intermediate column set.  Each intermediate selection is
the increasing enumeration of a subset, hence strictly monotone, so every
summand is a product of two nonnegative minors and the sum is nonnegative.

This lives in its own file rather than in
`RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg` only because that file
is a `module` while `...Determinant.CauchyBinet` is not, and a `module` cannot
import a non-`module`.  When upstreaming, both belong together.
-/

namespace Matrix

/-- **Total nonnegativity is closed under products.** -/
protected theorem IsTotallyNonnegRect.mul {R : Type*} [CommRing R] [PartialOrder R]
    [IsOrderedRing R] {l n m : ℕ} {L : Matrix (Fin l) (Fin n) R} {A : Matrix (Fin n) (Fin m) R}
    (hL : L.IsTotallyNonnegRect) (hA : A.IsTotallyNonnegRect) :
    (L * A).IsTotallyNonnegRect := by
  intro q rows cols hrows hcols
  rw [Matrix.det_submatrix_mul_eq_sum_powersetCard]
  refine Finset.sum_nonneg fun s _ => mul_nonneg ?_ ?_
  · exact hL hrows (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono
  · exact hA (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hcols

/-- Square total nonnegativity is closed under products. -/
protected theorem IsTotallyNonneg.mul {R : Type*} [CommRing R] [PartialOrder R]
    [IsOrderedRing R] {n : ℕ} {L A : Matrix (Fin n) (Fin n) R}
    (hL : L.IsTotallyNonneg) (hA : A.IsTotallyNonneg) :
    (L * A).IsTotallyNonneg :=
  (hL.toRect.mul hA.toRect).toSquare

end Matrix
