import RealRooted.JacobiDeformation.CriticalProduct
import RealRooted.JacobiDeformation.RootGeometry

/-!
# Fixed-coordinate derivative identity for the image product

This finite-product calculation is independent of the later identification of
`imageProduct` with a Jacobi deformation polynomial.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem eval_derivative_prod_div_eval_prod
    {ι : Type*} (s : Finset ι) (g : ι → ℝ[X]) (x : ℝ)
    (h : ∀ i ∈ s, (g i).eval x ≠ 0) :
    (derivative (∏ i ∈ s, g i)).eval x / (∏ i ∈ s, g i).eval x =
      ∑ i ∈ s, (derivative (g i)).eval x / (g i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hprod : (∏ i ∈ s, g i).eval x ≠ 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hga : (g a).eval x ≠ 0 := h a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Polynomial.derivative_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul]
      rw [← ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
      field_simp

private theorem image_node_log_derivative
    (t xi r z U V : ℝ) (ht0 : t ≠ 0) (ht1 : 1 - t ≠ 0)
    (hr : r - t ≠ 0) (hz : z - t ≠ 0)
    (himage : xi + (U / t + V / (1 - t)) ≠ 0)
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    xi * (r - z) / (xi + (U / t + V / (1 - t))) =
      (r - z) + r * (1 - r) / (r - t) - z * (1 - z) / (z - t) := by
  have hU : U = -(xi * r * z) := by linarith
  have hV : V = -(xi * (1 - r) * (1 - z)) := by linarith
  subst U
  subst V
  rw [div_eq_iff himage]
  field_simp [ht0, ht1, hr, hz]
  ring

private theorem imageProduct_eq_prod_imageValue {m : ℕ} (U V : ℝ) (t : Fin m → ℝ) :
    imageProduct U V t = ∏ i, X + C (imageValue U V (t i)) := by
  simp [imageProduct, sub_eq_add_neg]

/-- The fixed-coordinate logarithmic derivative identity for the actual
image product.  The hypotheses allow the empty family `Fin 0`. -/
theorem imageProduct_derivative_identity
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {U V xi r z : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V)
    (hqr : (∏ i, (X - C (t i))).eval r ≠ 0)
    (hqz : (∏ i, (X - C (t i))).eval z ≠ 0)
    (himage : (imageProduct U V t).eval xi ≠ 0) :
    xi * (r - z) * (imageProduct U V t).derivative.eval xi /
        (imageProduct U V t).eval xi =
      (m : ℝ) * (r - z) +
        r * (1 - r) * (derivative (∏ i, X - C (t i))).eval r /
          (∏ i, X - C (t i)).eval r -
        z * (1 - z) * (derivative (∏ i, X - C (t i))).eval z /
          (∏ i, X - C (t i)).eval z := by
  let g : Fin m → ℝ[X] := fun i => X + C (imageValue U V (t i))
  have himageProduct : imageProduct U V t = ∏ i, g i := by
    simpa only [g] using imageProduct_eq_prod_imageValue U V t
  have ht0 : ∀ i : Fin m, t i ≠ 0 := fun i => (ht i).1.ne'
  have ht1 : ∀ i : Fin m, 1 - t i ≠ 0 := fun i =>
    (sub_pos.mpr (ht i).2).ne'
  have hfacr : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (X - C (t i)).eval r ≠ 0 := by
    intro i hi
    rw [Polynomial.eval_prod] at hqr
    exact Finset.prod_ne_zero_iff.mp hqr i hi
  have hfacz : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (X - C (t i)).eval z ≠ 0 := by
    intro i hi
    rw [Polynomial.eval_prod] at hqz
    exact Finset.prod_ne_zero_iff.mp hqz i hi
  have hfacxi : ∀ i ∈ (Finset.univ : Finset (Fin m)), (g i).eval xi ≠ 0 := by
    intro i hi
    rw [himageProduct, Polynomial.eval_prod] at himage
    exact Finset.prod_ne_zero_iff.mp himage i hi
  have hqderr :
      (derivative (∏ i, X - C (t i))).eval r / (∏ i, X - C (t i)).eval r =
        ∑ i, 1 / (r - t i) := by
    rw [eval_derivative_prod_div_eval_prod _ _ _ hfacr]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hqderz :
      (derivative (∏ i, X - C (t i))).eval z / (∏ i, X - C (t i)).eval z =
        ∑ i, 1 / (z - t i) := by
    rw [eval_derivative_prod_div_eval_prod _ _ _ hfacz]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hgder :
      (derivative (∏ i, g i)).eval xi / (∏ i, g i).eval xi =
        ∑ i, 1 / (xi + (U / t i + V / (1 - t i))) := by
    rw [eval_derivative_prod_div_eval_prod _ _ _ hfacxi]
    exact Finset.sum_congr rfl fun i _ => by simp [g, imageValue]
  rw [himageProduct]
  calc
    xi * (r - z) * (derivative (∏ i, g i)).eval xi / (∏ i, g i).eval xi =
        ∑ i, xi * (r - z) / (xi + (U / t i + V / (1 - t i))) := by
          rw [mul_div_assoc, hgder, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [mul_one_div]
    _ = ∑ i, ((r - z) + r * (1 - r) / (r - t i) -
          z * (1 - z) / (z - t i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          apply image_node_log_derivative (t i) xi r z U V (ht0 i) (ht1 i)
          · simpa using hfacr i (Finset.mem_univ i)
          · simpa using hfacz i (Finset.mem_univ i)
          · simpa [g, imageValue] using hfacxi i (Finset.mem_univ i)
          · exact hprod
          · exact hcomp
    _ = (m : ℝ) * (r - z) +
          r * (1 - r) * (derivative (∏ i, X - C (t i))).eval r /
            (∏ i, X - C (t i)).eval r -
          z * (1 - z) * (derivative (∏ i, X - C (t i))).eval z /
            (∏ i, X - C (t i)).eval z := by
          have e0 : ∑ _i : Fin m, (r - z) = (m : ℝ) * (r - z) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have e1 : ∑ i : Fin m, r * (1 - r) / (r - t i) =
              r * (1 - r) * ∑ i : Fin m, 1 / (r - t i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => (mul_one_div _ _).symm
          have e2 : ∑ i : Fin m, z * (1 - z) / (z - t i) =
              z * (1 - z) * ∑ i : Fin m, 1 / (z - t i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => (mul_one_div _ _).symm
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, e0, e1, e2,
            mul_div_assoc, hqderr, hqderz]

/-- At a zero of the image-product derivative, the fixed-coordinate right
hand side of `imageProduct_derivative_identity` vanishes. -/
theorem imageProduct_derivative_identity_of_derivative_eval_zero
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {U V xi r z : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V)
    (hqr : (∏ i, (X - C (t i))).eval r ≠ 0)
    (hqz : (∏ i, (X - C (t i))).eval z ≠ 0)
    (himage : (imageProduct U V t).eval xi ≠ 0)
    (hderivative : (imageProduct U V t).derivative.eval xi = 0) :
    (m : ℝ) * (r - z) +
        r * (1 - r) * (derivative (∏ i, X - C (t i))).eval r /
          (∏ i, X - C (t i)).eval r -
        z * (1 - z) * (derivative (∏ i, X - C (t i))).eval z /
          (∏ i, X - C (t i)).eval z = 0 := by
  rw [← imageProduct_derivative_identity t ht hprod hcomp hqr hqz himage,
    hderivative, mul_zero, zero_div]
  ring

end RealRooted.JacobiDeformation
