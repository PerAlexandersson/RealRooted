import RealRooted.JacobiDeformation.Kernel

/-!
# Normalization of the Jacobi kernel weights

The finite identity here is the elementary normalization of equation (5).
The Pfaff--Saalschutz finite sum belongs in the separate Newton-identity layer.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Splitting a rising factorial at a natural-number offset. -/
theorem risingFactorial_mul_shift (a : ℝ) (u v : ℕ) :
    risingFactorial a u * risingFactorial (a + u) v =
      risingFactorial a (u + v) := by
  have h := congrArg (fun p : ℝ[X] => p.eval a) (ascPochhammer_mul ℝ u v)
  simpa [risingFactorial] using h

/-- The tail of a rising factorial is the matching descending Pochhammer
evaluation. -/
theorem risingFactorial_sub_mul_descPochhammer (δ : ℝ) {m j : ℕ} (hjm : j ≤ m) :
    risingFactorial δ (m - j) *
        (descPochhammer ℝ j).eval ((m : ℝ) + δ - 1) =
      risingFactorial δ m := by
  rw [descPochhammer_eval_eq_ascPochhammer]
  have harg : (m : ℝ) + δ - 1 - (j : ℝ) + 1 = δ + ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hjm]
    ring
  rw [harg]
  simpa [risingFactorial, Nat.sub_add_cancel hjm] using
    risingFactorial_mul_shift δ (m - j) j

/-- The normalized Jacobi kernel weight has the finite Pochhammer quotient
needed by the Newton expansion. -/
theorem kernelWeight_div_kernelWeight_zero {m j : ℕ} {δ s : ℝ}
    (hjm : j ≤ m) (hδ : 0 < δ) (_hδ1 : δ < 1) (hs : 0 < s) :
    kernelWeight m δ s j / kernelWeight m δ s 0 =
      (descPochhammer ℝ j).eval (m : ℝ) *
          risingFactorial ((m : ℝ) + s - 1 + δ) j /
        ((descPochhammer ℝ j).eval ((m : ℝ) + δ - 1) *
          risingFactorial ((m : ℝ) + s) j) := by
  have htail_pos : 0 < risingFactorial δ (m - j) :=
    risingFactorial_pos _ hδ
  have hfall_pos : 0 < (descPochhammer ℝ j).eval ((m : ℝ) + δ - 1) := by
    apply descPochhammer_pos
    have hj : (j : ℝ) ≤ m := by exact_mod_cast hjm
    linarith
  have hsm_pos : 0 < (m : ℝ) + s := by
    positivity
  have hbase_pos : 0 < risingFactorial s m :=
    risingFactorial_pos _ hs
  have hhead_pos : 0 < risingFactorial ((m : ℝ) + s) j :=
    risingFactorial_pos _ hsm_pos
  have hsplit_delta := risingFactorial_sub_mul_descPochhammer δ hjm
  have hsplit_s := risingFactorial_mul_shift s m j
  simp only [kernelWeight, descPochhammer_zero, eval_one, risingFactorial_zero,
    mul_one, one_mul, Nat.sub_zero]
  rw [← hsplit_delta, ← hsplit_s]
  simp only [Nat.add_zero, add_comm s (m : ℝ)]
  field_simp [ne_of_gt htail_pos, ne_of_gt hfall_pos, ne_of_gt hbase_pos,
    ne_of_gt hhead_pos]

end RealRooted.JacobiDeformation
