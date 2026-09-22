import RealRooted.JacobiDeformation.CriticalProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Double roots of the Jacobi image product

This records the finite algebraic sign calculation at a double image root.
It is independent of the later critical-case assembly.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The second derivative of `(X - C c)^2 * g`, evaluated at the double root `c`,
is `2 * g c`. -/
private theorem eval_derivative_derivative_sq_mul (c : ℝ) (g : ℝ[X]) :
    (derivative (derivative ((X - C c) ^ 2 * g))).eval c = 2 * g.eval c := by
  simp [derivative_mul, pow_two, add_mul]
  ring

/-- The derivative of the node polynomial at `t a` is the product over all
other nodes. -/
private theorem eval_derivative_prod_X_sub_C {m : ℕ} (t : Fin m → ℝ) (a : Fin m) :
    (derivative (∏ i : Fin m, (X - C (t i)))).eval (t a) =
      ∏ i ∈ (univ : Finset (Fin m)).erase a, (t a - t i) := by
  classical
  rw [derivative_prod_finset, eval_finset_sum, Finset.sum_eq_single a]
  · simp [eval_prod]
  · intro i _ hia
    simp only [eval_prod, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
      derivative_C, sub_zero, mul_one]
    refine Finset.prod_eq_zero (i := a) ?_ ?_
    · exact Finset.mem_erase.mpr ⟨fun h => hia (h ▸ rfl), Finset.mem_univ a⟩
    · ring
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The cleared scalar identity for an image coordinate at an interior node. -/
private theorem image_coordinate_identity {r z s U V xi : ℝ}
    (hs0 : s ≠ 0) (hs1 : (1 : ℝ) - s ≠ 0)
    (hU : xi * r * z = -U) (hV : xi * (1 - r) * (1 - z) = -V) :
    xi + (U / s + V / (1 - s)) =
      (-xi / (s * (1 - s))) * ((r - s) * (z - s)) := by
  have hUe : U = -(xi * r * z) := by linarith
  have hVe : V = -(xi * (1 - r) * (1 - z)) := by linarith
  subst hUe
  subst hVe
  field_simp
  ring

/-- Rewrite the actual image product as its finite product of image factors. -/
private theorem imageProduct_eq_prod_X_add_C {m : ℕ} (U V : ℝ) (t : Fin m → ℝ) :
    imageProduct U V t = ∏ i : Fin m, (X + C (U / t i + V / (1 - t i))) := by
  unfold imageProduct
  simp only [Multiset.map_map, Function.comp_apply]
  rw [show ((Finset.univ : Finset (Fin m)).1.map (fun i =>
      X - C (-(imageValue U V (t i))))).prod =
        Finset.univ.prod (fun i : Fin m => X - C (-(imageValue U V (t i)))) by rfl]
  apply Finset.prod_congr rfl
  intro i _
  unfold imageValue
  ring

/-- At a double image root, the second derivative of `imageProduct` has the
strict sign obtained from the two distinguished node derivatives. -/
theorem imageProduct_double_root_sign {m : ℕ} (t : Fin m → ℝ) (U V xi : ℝ)
    (hinj : Function.Injective t)
    (ht0 : ∀ i : Fin m, 0 < t i) (ht1 : ∀ i : Fin m, t i < 1)
    (a b : Fin m) (hab : a ≠ b) (hxi : xi < 0)
    (hU : xi * t a * t b = -U) (hV : xi * (1 - t a) * (1 - t b) = -V) :
    (imageProduct U V t).derivative.derivative.eval xi *
        (derivative (∏ i : Fin m, (X - C (t i)))).eval (t a) *
        (derivative (∏ i : Fin m, (X - C (t i)))).eval (t b) < 0 := by
  classical
  set c : Fin m → ℝ := fun i => U / t i + V / (1 - t i) with hc
  set I : Finset (Fin m) := ((univ : Finset (Fin m)).erase a).erase b with hI
  have hne0 : ∀ i : Fin m, t i ≠ 0 := fun i => ne_of_gt (ht0 i)
  have hne1 : ∀ i : Fin m, (1 : ℝ) - t i ≠ 0 := fun i =>
    (sub_pos.mpr (ht1 i)).ne'
  have hca : c a = -xi := by
    have h := image_coordinate_identity (r := t a) (z := t b) (s := t a)
      (hne0 a) (hne1 a) hU hV
    simp only [sub_self, zero_mul, mul_zero] at h
    simp only [hc]
    linarith
  have hcb : c b = -xi := by
    have h := image_coordinate_identity (r := t a) (z := t b) (s := t b)
      (hne0 b) (hne1 b) hU hV
    simp only [sub_self, mul_zero] at h
    simp only [hc]
    linarith
  have hbmem : b ∈ (univ : Finset (Fin m)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, mem_univ b⟩
  have hamem : a ∈ (univ : Finset (Fin m)).erase b :=
    Finset.mem_erase.mpr ⟨hab, mem_univ a⟩
  have himage : imageProduct U V t = ∏ i : Fin m, (X + C (c i)) := by
    rw [imageProduct_eq_prod_X_add_C]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hc]
  have hf : (∏ i : Fin m, (X + C (c i))) =
      (X - C xi) ^ 2 * ∏ i ∈ I, (X + C (c i)) := by
    rw [← Finset.mul_prod_erase (univ : Finset (Fin m)) (fun i => X + C (c i))
      (mem_univ a), ← Finset.mul_prod_erase ((univ : Finset (Fin m)).erase a)
      (fun i => X + C (c i)) hbmem, hca, hcb, hI]
    rw [map_neg, ← sub_eq_add_neg]
    ring
  have hf2 : (derivative (derivative (∏ i : Fin m, (X + C (c i))))).eval xi =
      2 * ∏ i ∈ I, (xi + c i) := by
    rw [hf, eval_derivative_derivative_sq_mul, eval_prod]
    simp
  have hqa : (derivative (∏ i : Fin m, (X - C (t i)))).eval (t a) =
      (t a - t b) * ∏ i ∈ I, (t a - t i) := by
    rw [eval_derivative_prod_X_sub_C, hI,
      ← Finset.mul_prod_erase ((univ : Finset (Fin m)).erase a) (fun i => t a - t i) hbmem]
  have hqb : (derivative (∏ i : Fin m, (X - C (t i)))).eval (t b) =
      (t b - t a) * ∏ i ∈ I, (t b - t i) := by
    rw [eval_derivative_prod_X_sub_C, hI, Finset.erase_right_comm,
      ← Finset.mul_prod_erase ((univ : Finset (Fin m)).erase b) (fun i => t b - t i) hamem]
  have hprod : (∏ i ∈ I, (xi + c i)) =
      (∏ i ∈ I, (-xi / (t i * (1 - t i)))) *
        ((∏ i ∈ I, (t a - t i)) * ∏ i ∈ I, (t b - t i)) := by
    have hcongr : ∀ i ∈ I, xi + c i =
        (-xi / (t i * (1 - t i))) * ((t a - t i) * (t b - t i)) := by
      intro i _
      exact image_coordinate_identity (hne0 i) (hne1 i) hU hV
    rw [Finset.prod_congr rfl hcongr, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hW : 0 < ∏ i ∈ I, (-xi / (t i * (1 - t i))) := by
    refine Finset.prod_pos ?_
    intro i _
    have hden : 0 < t i * (1 - t i) :=
      mul_pos (ht0 i) (sub_pos.mpr (ht1 i))
    exact div_pos (by linarith) hden
  have hPa : (∏ i ∈ I, (t a - t i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (hI ▸ hi)).2).1
    exact sub_ne_zero_of_ne fun h => hia (hinj h.symm)
  have hPb : (∏ i ∈ I, (t b - t i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    have hib : i ≠ b := (Finset.mem_erase.mp (hI ▸ hi)).1
    exact sub_ne_zero_of_ne fun h => hib (hinj h.symm)
  have htab : t a - t b ≠ 0 := sub_ne_zero_of_ne fun h => hab (hinj h)
  rw [himage, hqa, hqb, hf2, hprod]
  have hsq1 : 0 < (t a - t b) ^ 2 := by positivity
  have hsq2 : 0 < (∏ i ∈ I, (t a - t i)) ^ 2 := by positivity
  have hsq3 : 0 < (∏ i ∈ I, (t b - t i)) ^ 2 := by positivity
  have hkey : 0 < 2 * (∏ i ∈ I, (-xi / (t i * (1 - t i)))) * (t a - t b) ^ 2 *
      (∏ i ∈ I, (t a - t i)) ^ 2 * (∏ i ∈ I, (t b - t i)) ^ 2 := by
    positivity
  nlinarith [hkey]

/-- The two-node double-root sign, retaining the empty remaining product. -/
theorem imageProduct_double_root_sign_two_nodes (t : Fin 2 → ℝ) (U V xi : ℝ)
    (hinj : Function.Injective t)
    (ht0 : ∀ i : Fin 2, 0 < t i) (ht1 : ∀ i : Fin 2, t i < 1) (hxi : xi < 0)
    (hU : xi * t 0 * t 1 = -U) (hV : xi * (1 - t 0) * (1 - t 1) = -V) :
    (imageProduct U V t).derivative.derivative.eval xi *
        (derivative (∏ i : Fin 2, (X - C (t i)))).eval (t 0) *
        (derivative (∏ i : Fin 2, (X - C (t i)))).eval (t 1) < 0 :=
  imageProduct_double_root_sign t U V xi hinj ht0 ht1 0 1 (by decide) hxi hU hV

end RealRooted.JacobiDeformation
