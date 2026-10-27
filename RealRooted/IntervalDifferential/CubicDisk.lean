/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Seeds
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The cubic disk hypothesis implies the seed coefficient bound

For the odd cubic `X³ + kX`, roots of its quadratic factor satisfy
`c² = -k`. Thus the squared modulus of such a root is `|k|`. This turns
the disk assumption of Appendix B into the exact coefficient hypothesis of
the checked cubic seed in Appendix C.3 of
`alternating_eulerian_shorter_proof.md`.
-/

public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- The complex-root disk bound for `X³ + kX` controls its linear coefficient. -/
theorem cubic_abs_le_of_root_normSq_le (k : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 3 + C k * X : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    |k| ≤ 13 / 3 := by
  obtain ⟨c, hc⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-(k : ℂ)) (n := 2) (by norm_num)
  have hroot :
      ((X ^ 3 + C k * X : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 := by
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X,
      Polynomial.map_mul, map_C, eval_add, eval_pow, eval_X,
      eval_mul, eval_C]
    calc
      c ^ 3 + (k : ℂ) * c = c * (c ^ 2 + (k : ℂ)) := by ring
      _ = 0 := by rw [hc]; ring
  have hbound := hroots c hroot
  have hnormSq : Complex.normSq c ^ 2 = k ^ 2 := by
    calc
      Complex.normSq c ^ 2 = Complex.normSq (c ^ 2) := by
        rw [pow_two, pow_two, Complex.normSq_mul]
      _ = Complex.normSq (-(k : ℂ)) := by rw [hc]
      _ = k ^ 2 := by
        rw [Complex.normSq_neg, Complex.normSq_ofReal]
        ring
  have habs : |k| = Complex.normSq c :=
    (sq_eq_sq₀ (abs_nonneg k) (Complex.normSq_nonneg c)).mp (by
      rw [sq_abs]
      exact hnormSq.symm)
  rw [habs]
  exact hbound

/-- The cubic disk assumption yields three simple transformed roots in `(-1, 1)`. -/
theorem zigzagTransform_cubic_roots_of_disk (k : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 3 + C k * X : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    (zigzagTransform (X ^ 3 + C k * X)).Splits ∧
      (zigzagTransform (X ^ 3 + C k * X)).roots.Nodup ∧
      ∀ r ∈ (zigzagTransform (X ^ 3 + C k * X)).roots, -1 < r ∧ r < 1 := by
  exact zigzagTransform_cubic_roots k (cubic_abs_le_of_root_normSq_le k hroots)

end RealRooted.IntervalDifferential
