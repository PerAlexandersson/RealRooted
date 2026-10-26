/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Certificates
public import RealRooted.IntervalDifferential.Degree
public import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
public import Mathlib.Tactic

/-!
# The three-sign quartic seed

Appendix C.3 of `alternating_eulerian_shorter_proof.md` reduces the even
quartic seed to three strict signs at squared arguments `0`, `1/4`, and `1`.
This module proves the complete root-location conclusion from those signs.
The signs' derivation from the complex input disk is separate.
-/

public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- Three scalar signs force four simple interval roots of the quartic transform. -/
theorem zigzagTransform_quartic_roots_of_signs (k p : ℝ)
    (hzero : 0 < 33 - 3 * k + p) (hmid : p < 45 / 2)
    (hone : 0 < 81 + 9 * k + p) :
    (zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)).Splits ∧
      (zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)).roots.Nodup ∧
      ∀ r ∈ (zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)).roots,
        -1 < r ∧ r < 1 := by
  let F := zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)
  have heval (z : ℝ) : F.eval z =
      360 * z ^ 4 + (12 * k - 312) * z ^ 2 + 33 - 3 * k + p := by
    simp only [F, zigzagTransform_quartic, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    ring
  have hF : F ≠ 0 := by
    intro h
    have hz := heval 0
    rw [h] at hz
    simp only [eval_zero] at hz
    linarith
  have hdeg : F.natDegree ≤ 4 := by
    rw [show F = zigzagTransform (X ^ 4 + C k * X ^ 2 + C p) by rfl,
      zigzagTransform_natDegree, natDegree_add_C]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  let x : Fin 5 → ℝ := fun i => (i.val : ℝ) / 2 - 1
  have hx : StrictMono x := by
    intro i j hij
    have hv : (i.val : ℝ) < j.val := by exact_mod_cast hij
    dsimp [x]
    linarith
  have hsign : ∀ i : Fin 4, F.eval (x i.castSucc) * F.eval (x i.succ) < 0 := by
    intro i
    fin_cases i <;> simp only [x, heval] <;> norm_num <;> nlinarith
  obtain ⟨_, hs, hn, hr⟩ :=
    Polynomial.splits_nodup_roots_of_strict_sign_changes hF hdeg x hx hsign
  refine ⟨hs, hn, ?_⟩
  intro r hroot
  convert hr r hroot using 1 <;> norm_num [x]

end RealRooted.IntervalDifferential
