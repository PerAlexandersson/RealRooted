/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Certificates
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Interval roots of the cubic seed

The odd cubic seed in Appendix C.3 of
`alternating_eulerian_shorter_proof.md` has three distinct roots in `(-1, 1)`.
The coefficient bound here is the bound induced by the input root disk;
its derivation from the complex roots is a separate step.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- The cubic transform factors over the reals with an explicit positive root. -/
theorem zigzagTransform_cubic_factorization (k : ℝ) (hk : k < 11) :
    zigzagTransform (X ^ 3 + C k * X) =
      C 60 * X * (X - C (Real.sqrt ((11 - k) / 20))) *
        (X + C (Real.sqrt ((11 - k) / 20))) := by
  have hs : Real.sqrt ((11 - k) / 20) ^ 2 = (11 - k) / 20 :=
    Real.sq_sqrt (by linarith)
  rw [zigzagTransform_cubic]
  have hc : C (Real.sqrt ((11 - k) / 20)) ^ 2 = C ((11 - k) / 20) := by
    rw [← map_pow, hs]
  calc
    C 3 * X * (C 20 * X ^ 2 + C (k - 11)) =
      C 60 * X * (X ^ 2 - C ((11 - k) / 20)) := by
        have hscale : C (60 : ℝ) * C ((11 - k) / 20) = C (33 - 3 * k) := by
          rw [← map_mul]
          congr 1
          ring
        simp only [map_sub, map_mul, map_ofNat] at hscale ⊢
        linear_combination X * hscale
    _ = C 60 * X * (X - C (Real.sqrt ((11 - k) / 20))) *
        (X + C (Real.sqrt ((11 - k) / 20))) := by rw [← hc]; ring

/-- Appendix C.3: the odd cubic seed has simple roots strictly inside the interval. -/
theorem zigzagTransform_cubic_roots (k : ℝ) (hk : |k| ≤ 13 / 3) :
    (zigzagTransform (X ^ 3 + C k * X)).Splits ∧
      (zigzagTransform (X ^ 3 + C k * X)).roots.Nodup ∧
      ∀ r ∈ (zigzagTransform (X ^ 3 + C k * X)).roots, -1 < r ∧ r < 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hk
  let t := Real.sqrt ((11 - k) / 20)
  have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have htsq : t ^ 2 = (11 - k) / 20 := Real.sq_sqrt (by linarith)
  have ht1 : t < 1 := by nlinarith
  rw [zigzagTransform_cubic_factorization k (by linarith)]
  have hX : (X : ℝ[X]) ≠ 0 := X_ne_zero
  have hm : (X - C t : ℝ[X]) ≠ 0 := X_sub_C_ne_zero t
  have hp : (X + C t : ℝ[X]) ≠ 0 := X_add_C_ne_zero t
  have hc : (C 60 : ℝ[X]) ≠ 0 := by norm_num
  have hroots : (C 60 * X * (X - C t) * (X + C t)).roots =
      ({0, t, -t} : Multiset ℝ) := by
    rw [roots_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hc hX) hm) hp),
      roots_mul (mul_ne_zero (mul_ne_zero hc hX) hm),
      roots_mul (mul_ne_zero hc hX)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · exact (((Splits.C 60).mul Splits.X).mul (Splits.X_sub_C t)).mul
      (Splits.X_add_C t)
  · rw [hroots]
    simp [ht.ne', ht.ne'.symm, show t ≠ -t by linarith]
  · rw [hroots]
    intro r hr
    have hcases : r = 0 ∨ r = t ∨ r = -t := by simpa using hr
    rcases hcases with rfl | rfl | rfl <;> constructor <;> linarith

end RealRooted.IntervalDifferential
