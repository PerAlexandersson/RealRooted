import RealRooted.JacobiDeformation.CriticalProduct
import RealRooted.JacobiDeformation.RootGeometry

/-!
# Product coordinates for cleared Jacobi image roots

This is only the finite-product consequence of the scalar cleared root-image
identity.  It does not identify the product with a deformation polynomial.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The interior-node product in the image-coordinate identity is positive. -/
theorem prod_node_mul_one_sub_pos {m : ℕ} (t : Fin m → ℝ)
    (ht : ∀ i, 0 < t i ∧ t i < 1) :
    0 < ∏ i, t i * (1 - t i) := by
  refine Finset.prod_pos fun i _ => ?_
  exact mul_pos (ht i).1 (sub_pos.mpr (ht i).2)

private theorem eval_imageProduct_eq_prod {m : ℕ} (U V xi : ℝ) (t : Fin m → ℝ) :
    (imageProduct U V t).eval xi =
      ∏ i, xi + U / t i + V / (1 - t i) := by
  simp [imageProduct, imageValue, eval_multiset_prod]

/-- Multiplying the cleared root-image identities at a finite family of
interior nodes yields the exact `imageProduct` coordinate formula. -/
theorem imageProduct_coordinate_identity
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {xi r z U V : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    xi ^ m * (∏ i, r - t i) * (∏ i, z - t i) =
      (-1 : ℝ) ^ m * (∏ i, t i * (1 - t i)) *
        (imageProduct U V t).eval xi := by
  have hterm : ∀ i : Fin m,
      xi * (r - t i) * (z - t i) =
        -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i)) := by
    intro i
    have ht0 : t i ≠ 0 := (ht i).1.ne'
    have h1t0 : 1 - t i ≠ 0 := (sub_pos.mpr (ht i).2).ne'
    have hcleared := image_root_product_cleared hprod hcomp (t := t i)
    field_simp [ht0, h1t0]
    nlinarith [hcleared]
  have hterms :
      (∏ i, xi * (r - t i) * (z - t i)) =
        ∏ i, -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i)) := by
    refine Finset.prod_congr rfl fun i _ => hterm i
  have himage := eval_imageProduct_eq_prod U V xi t
  calc
    xi ^ m * (∏ i, r - t i) * (∏ i, z - t i) =
        ∏ i, xi * (r - t i) * (z - t i) := by
          simp [Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
    _ = ∏ i, -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i)) := hterms
    _ = (∏ i, ((-1 : ℝ) * (t i * (1 - t i))) *
          (xi + U / t i + V / (1 - t i)) := by
          apply Finset.prod_congr rfl
          intro i _
          ring
    _ = (∏ i, (-1 : ℝ) * (t i * (1 - t i))) *
          (∏ i, xi + U / t i + V / (1 - t i)) := by
          rw [Finset.prod_mul_distrib]
    _ = ((∏ i, (-1 : ℝ)) * (∏ i, t i * (1 - t i))) *
          (∏ i, xi + U / t i + V / (1 - t i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ m * (∏ i, t i * (1 - t i)) *
          (imageProduct U V t).eval xi := by
          rw [himage]
          simp

end RealRooted.JacobiDeformation
