module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Real cofactor roots and affine norm bounds

The negative constant term makes the cofactor roots real, distinct, and of
opposite signs. The two Jury inequalities then give the required common disk.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

/-- The positive root of a quadratic with negative constant term. -/
noncomputable def cofactorPositive (s p : ℝ) : ℝ := (-s + Real.sqrt (s ^ 2 - 4 * p)) / 2

/-- The negative root of a quadratic with negative constant term. -/
noncomputable def cofactorNegative (s p : ℝ) : ℝ := (-s - Real.sqrt (s ^ 2 - 4 * p)) / 2

/-- The explicit roots have opposite signs and the prescribed elementary functions. -/
theorem cofactor_roots_spec {s p : ℝ} (hp : p < 0) :
    0 < cofactorPositive s p ∧ cofactorNegative s p < 0 ∧
      cofactorPositive s p + cofactorNegative s p = -s ∧
      cofactorPositive s p * cofactorNegative s p = p := by
  have hdisc : 0 ≤ s ^ 2 - 4 * p := by nlinarith [sq_nonneg s]
  have hsq := Real.sq_sqrt hdisc
  have hlarge : |s| < Real.sqrt (s ^ 2 - 4 * p) :=
    (Real.lt_sqrt (abs_nonneg s)).mpr (by rw [sq_abs]; linarith)
  have hb := abs_lt.mp hlarge
  dsimp [cofactorPositive, cofactorNegative]
  refine ⟨by linarith [hb.2], by linarith [hb.1], by ring, ?_⟩
  nlinarith

/-- For roots of opposite signs, the Jury inequality puts both inside the disk. -/
theorem abs_cofactor_roots_lt {x y s p R : ℝ} (hx : 0 < x) (hy : y < 0)
    (hs : x + y = -s) (hp : x * y = p) (hR : 0 < R)
    (hJ : |s| * R < R ^ 2 + p) : |x| < R ∧ |y| < R := by
  have hsumR := congrArg (fun v : ℝ ↦ R * v) hs
  have hplus : 0 < (R - x) * (R - y) := by
    have hbound := mul_le_mul_of_nonneg_right (neg_abs_le s) hR.le
    nlinarith [hsumR, hp]
  have hminus : 0 < (R + x) * (R + y) := by
    have hbound := mul_le_mul_of_nonneg_right (le_abs_self s) hR.le
    nlinarith [hsumR, hp]
  have hxR : x < R := by
    rcases mul_pos_iff.mp hplus with hh | hh
    · linarith [hh.1]
    · linarith [hh.2]
  have hyR : -R < y := by
    rcases mul_pos_iff.mp hminus with hh | hh
    · linarith [hh.2]
    · linarith [hh.1]
  rw [abs_of_pos hx, abs_of_neg hy]
  exact ⟨hxR, by linarith⟩

/-- The squared version of the Jury conditions implies the unsquared inequality. -/
theorem jury_of_sq {s p R : ℝ} (h₁ : 0 < R ^ 2 + p)
    (h₂ : R ^ 2 * s ^ 2 < (R ^ 2 + p) ^ 2) : |s| * R < R ^ 2 + p := by
  have hsq : (|s| * R) ^ 2 < (R ^ 2 + p) ^ 2 := by
    simpa only [mul_pow, sq_abs, mul_comm] using h₂
  nlinarith

/-- The explicit opposite roots obey the disk bound from squared Jury conditions. -/
theorem abs_cofactor_lt_of_jury {s p R : ℝ} (hp : p < 0) (hR : 0 < R)
    (h₁ : 0 < R ^ 2 + p) (h₂ : R ^ 2 * s ^ 2 < (R ^ 2 + p) ^ 2) :
    |cofactorPositive s p| < R ∧ |cofactorNegative s p| < R := by
  obtain ⟨hx, hy, hs, hprod⟩ := cofactor_roots_spec (s := s) hp
  exact abs_cofactor_roots_lt hx hy hs hprod hR (jury_of_sq h₁ h₂)

/-- A numerator bound on the squared scale gives the normalized absolute weight. -/
theorem abs_div_pow_le_of_sq {v R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β) (j : ℕ)
    (h : v ^ 2 ≤ β ^ 2 * (R ^ 2) ^ j) : |v / R ^ j| ≤ β := by
  have hb : 0 ≤ β * R ^ j := mul_nonneg hβ (pow_nonneg hR.le j)
  have hv : |v| ≤ β * R ^ j := by
    apply abs_le_of_sq_le_sq _ hb
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm j 2] using h
  rw [abs_div, abs_of_pos (pow_pos hR j)]
  exact (div_le_iff₀ (pow_pos hR j)).mpr hv

/-- Squared norm of a real affine expression on a prescribed circle. -/
theorem normSq_affine {a c b : ℝ} (hc : a ^ 2 + c ^ 2 = b) (u v : ℝ) :
    Complex.normSq ((u : ℂ) * (⟨a, c⟩ : ℂ) + v) =
      u ^ 2 * b + 2 * u * v * a + v ^ 2 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im]
  linear_combination (u ^ 2) * hc

end RealRooted.EffectiveBKW.PathCube
