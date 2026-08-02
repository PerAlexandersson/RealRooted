import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.Matrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegular

/-!
# Karlin's finite Gaussian matrices

This file starts the formalization of Karlin, *Total Positivity*, Vol. I,
Chapter V, Section 1, Proposition 1.1.  Karlin uses the Gaussian matrix

`F(a) i j = exp (-a * (i - j) ^ 2)`.

The proposition has two parts: `F(a)` tends to the identity as `a` tends to
positive infinity, and `F(a)` is strictly totally positive when `a > 0`.
This file proves the first part.  The second part requires the source's
strict-total-positivity theorem for the exponential kernel `exp (x * y)`;
it is intentionally not assumed here.
-/

public section

open Filter Topology

namespace Matrix

/-- Karlin's finite Gaussian matrix from Proposition V.1.1. -/
noncomputable def gaussianMatrix (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (-a * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2)

@[simp] lemma gaussianMatrix_apply (n : ℕ) (a : ℝ) (i j : Fin n) :
    gaussianMatrix n a i j =
      Real.exp (-a * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2) :=
  rfl

@[simp] lemma gaussianMatrix_apply_self (n : ℕ) (a : ℝ) (i : Fin n) :
    gaussianMatrix n a i i = 1 := by
  simp

lemma gaussianMatrix_apply_pos (n : ℕ) (a : ℝ) (i j : Fin n) :
    0 < gaussianMatrix n a i j :=
  Real.exp_pos _

/-- Karlin's Gaussian matrix converges entrywise to the identity as its
parameter tends to positive infinity. -/
theorem tendsto_gaussianMatrix_atTop (n : ℕ) :
    Tendsto (gaussianMatrix n) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  change Tendsto
    (fun a => (gaussianMatrix n a : Fin n → Fin n → ℝ)) atTop
    (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ))
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  by_cases hij : i = j
  · subst j
    simp only [gaussianMatrix_apply_self, one_apply, if_pos]
    exact tendsto_const_nhds
  · have hcast :
        (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      have hval : (i : ℕ) = (j : ℕ) := by
        exact_mod_cast heq
      exact hij (Fin.ext hval)
    have hsquare :
        0 < (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 :=
      sq_pos_of_ne_zero hcast
    have hneg :
        -(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 < 0 :=
      neg_lt_zero.mpr hsquare
    have hlinear :
        Tendsto
          (fun a : ℝ =>
            a * -(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2)
          atTop atBot :=
      tendsto_id.atTop_mul_const_of_neg hneg
    have hexp :=
      Real.tendsto_exp_atBot.comp hlinear
    convert hexp using 1
    · funext a
      simp only [Function.comp_apply, gaussianMatrix_apply]
      ring_nf
    · simp [hij]

end Matrix
