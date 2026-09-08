import RealRooted.ClassicalHurwitzMatrix.Stability.Criterion
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Closure
import RealRooted.Mathlib.Topology.Algebra.Polynomial

open Polynomial

noncomputable section

namespace RealRooted

/-- A positive translation moves every root of a quasi-stable polynomial into
the open left half-plane. -/
theorem IsHurwitzStable.strictlyStable_comp_X_add_C
    {p : ℝ[X]} (h : IsHurwitzStable p) {r : ℝ} (hr : 0 < r) :
    IsStrictlyHurwitzStable (p.comp (X + C r)) := by
  intro z hz
  by_contra hz_nonneg
  have hz_re : 0 ≤ z.re := le_of_not_gt hz_nonneg
  have hroot : (complexify p).eval (z + (r : ℂ)) = 0 := by
    simpa [complexify, Polynomial.map_comp, Polynomial.eval_comp] using hz
  exact h.rightHalfPlaneStable (z + (r : ℂ)) (by simp; linarith) hroot

/-- Removing a zero root preserves the project's closed-half-plane Hurwitz
stability predicate. -/
theorem isHurwitzStable_iff_divX_of_coeff_zero {p : ℝ[X]}
    (h0 : p.coeff 0 = 0) :
    IsHurwitzStable p ↔ IsHurwitzStable p.divX := by
  have hp : p = X * p.divX := by
    simpa [h0] using (Polynomial.X_mul_divX_add p).symm
  constructor
  · intro h
    refine ⟨h.hasNonnegCoeffs.divX, ?_⟩
    intro z hz hdiv
    apply h.rightHalfPlaneStable z hz
    rw [hp]
    simp only [complexify] at hdiv
    simp only [complexify, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_X]
    exact mul_eq_zero.mpr (Or.inr hdiv)
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hp]
      exact hasNonnegCoeffs_X.mul h.hasNonnegCoeffs
    · intro z hz hpz
      have hz0 : z ≠ 0 := by
        intro hz0
        subst z
        simp at hz
      apply h.rightHalfPlaneStable z hz
      rw [hp] at hpz
      simp only [complexify, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.eval_mul, Polynomial.eval_X] at hpz
      exact (mul_eq_zero.mp hpz).resolve_left hz0

/-- The corrected infinite Hurwitz matrix of every quasi-stable polynomial is
totally nonnegative, including boundary roots and vanishing constant term. -/
theorem _root_.Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable
    {p : ℝ[X]} (h : IsHurwitzStable p) :
    (Matrix.hurwitz p.coeff).IsTotallyNonneg := by
  have hp_ne : p ≠ 0 := by
    intro hp
    have hne := h.rightHalfPlaneStable (1 : ℂ) (by norm_num)
    simp [hp] at hne
  have hp_pos : HasPosLeadingCoeff p :=
    h.hasNonnegCoeffs.pos_leadingCoeff hp_ne
  let A : ℝ → Matrix ℕ ℕ ℝ := fun r ↦
    Matrix.hurwitz (p.comp (X + C r)).coeff
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [A, Matrix.hurwitz_apply]
    split
    · exact p.continuous_coeff_comp_X_add_C _
    · exact continuous_const
  have hA0 : A 0 = Matrix.hurwitz p.coeff := by
    simp [A]
  rw [← hA0]
  apply Matrix.IsTotallyNonneg.of_continuous_curve hA
  intro r hr
  exact Matrix.hurwitz_isTotallyNonneg_of_strictlyStable
    (h.strictlyStable_comp_X_add_C hr) (hp_pos.comp_X_add_C r)

end RealRooted
