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
      Finset.univ.prod (fun i : Fin m => xi + U / t i + V / (1 - t i)) := by
  unfold imageProduct
  rw [eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C]
  rw [show ((Finset.univ : Finset (Fin m)).1.map (fun i =>
      xi - -(imageValue U V (t i)))).prod =
        Finset.univ.prod (fun i : Fin m => xi - -(imageValue U V (t i))) by rfl]
  apply Finset.prod_congr rfl
  intro i _
  unfold imageValue
  ring

/-- Multiplying the cleared root-image identities at a finite family of
interior nodes yields the exact `imageProduct` coordinate formula. -/
theorem imageProduct_coordinate_identity
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {xi r z U V : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    xi ^ m * Finset.univ.prod (fun i : Fin m => r - t i) *
        Finset.univ.prod (fun i : Fin m => z - t i) =
      (-1 : ℝ) ^ m * Finset.univ.prod (fun i : Fin m => t i * (1 - t i)) *
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
      Finset.univ.prod (fun i : Fin m => xi * (r - t i) * (z - t i)) =
        Finset.univ.prod (fun i : Fin m =>
          -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i))) := by
    refine Finset.prod_congr rfl fun i _ => hterm i
  have himage := eval_imageProduct_eq_prod U V xi t
  calc
    xi ^ m * Finset.univ.prod (fun i : Fin m => r - t i) *
        Finset.univ.prod (fun i : Fin m => z - t i) =
        Finset.univ.prod (fun i : Fin m => xi * (r - t i) * (z - t i)) := by
          simp [Finset.prod_mul_distrib, mul_assoc]
    _ = Finset.univ.prod (fun i : Fin m =>
          -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i))) := hterms
    _ = Finset.univ.prod (fun i : Fin m =>
          ((-1 : ℝ) * (t i * (1 - t i))) *
            (xi + U / t i + V / (1 - t i))) := by
          apply Finset.prod_congr rfl
          intro i _
          ring
    _ = Finset.univ.prod (fun i : Fin m => (-1 : ℝ) * (t i * (1 - t i))) *
          Finset.univ.prod (fun i : Fin m =>
            xi + U / t i + V / (1 - t i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (Finset.univ.prod (fun _i : Fin m => (-1 : ℝ)) *
          Finset.univ.prod (fun i : Fin m => t i * (1 - t i))) *
          Finset.univ.prod (fun i : Fin m =>
            xi + U / t i + V / (1 - t i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ m * Finset.univ.prod (fun i : Fin m => t i * (1 - t i)) *
          (imageProduct U V t).eval xi := by
          rw [himage]
          simp

end RealRooted.JacobiDeformation
