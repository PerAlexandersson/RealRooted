module

public import RealRooted.LiuWang.CombinedFlux

/-!
# The finite-family Liu--Wang criterion

This file formalizes Theorem 2.3 of Liu--Wang, *A unified approach to polynomial
sequences with only real zeros* (arXiv:math/0509207v5, DOI
10.1016/j.aam.2006.02.003).

The combined condition `F(r) * f'(r) ≤ 0` does not suffice at repeated roots, where it is
vacuous: `f = X^2`, `g = X` and `F = X^3 + X^2 + X` satisfy it at zero, but `F` has two nonreal
roots.  The theorem below keeps the termwise hypotheses `b i (r) ≤ 0` instead.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.LiuWang

/-- The finite-family Liu--Wang criterion with positive leading coefficients.

Every member of the finite family is below `f`; the coefficient of each member
is nonpositive at the roots of `f`; and the resulting polynomial has the same
positive leading orientation and one of the two allowed degrees.
-/
theorem strictInterl_mul_add_sum_mul_of_eval_nonpos_of_pos
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) := by
  apply strictInterl_mul_add_sum_mul_of_combined_flux_of_pos hf_pos hf hg hg_pos
  · intro r hr
    rw [eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_nonpos fun i hi ↦ ?_
    rw [eval_mul, mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg (hb i hi r hr)
      ((hg i hi).eval_mul_eval_derivative_nonneg (hg_pos i hi) hf_pos hr)
  · exact fun i hi r hr _ ↦ hb i hi r hr
  · exact hF_pos
  · exact hdeg_lo
  · exact hdeg_hi

/-- The finite-family Liu--Wang criterion, allowing either sign for the
leading coefficient of `f`.

The leading coefficients of the interlacers and of the output are positive;
the sign of `f` is absorbed into the multiplier `a`.
-/
theorem strictInterl_mul_add_sum_mul_of_eval_nonpos
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_ne : f ≠ 0) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) := by
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hneg | hpos
  · have hnf_pos : HasPosLeadingCoeff (-f) := by
      simpa [HasPosLeadingCoeff] using hneg
    have hng : ∀ i ∈ s, StrictInterl (g i) (-f) := by
      intro i hi
      simpa using (hg i hi).C_mul_right (a := (-1 : ℝ)) (by norm_num)
    have hF_eq : a * f + ∑ i ∈ s, b i * g i =
        (-a) * (-f) + ∑ i ∈ s, b i * g i := by
      ring
    rw [hF_eq] at hF_pos hdeg_lo hdeg_hi ⊢
    have h := strictInterl_mul_add_sum_mul_of_eval_nonpos_of_pos hnf_pos
      (by simpa using hf) hng hg_pos
      (fun i hi r hr ↦ hb i hi r (by simpa using hr)) hF_pos
      (by simpa [natDegree_neg] using hdeg_lo)
      (by simpa [natDegree_neg] using hdeg_hi)
    simpa using h.C_mul_left (a := (-1 : ℝ)) (by norm_num)
  · exact strictInterl_mul_add_sum_mul_of_eval_nonpos_of_pos
      (by simpa [HasPosLeadingCoeff] using hpos) hf hg hg_pos hb hF_pos hdeg_lo hdeg_hi

/-! ## Derivative--lag specialization -/

/-- The finite-family criterion for a derivative--lag step.

The derivative and lag summands are treated symmetrically, so common roots are
allowed and the degree bounds include both the plateau and successor cases.
-/
theorem strictInterl_derivative_lag_of_eval_nonpos
    {f g u v w : ℝ[X]}
    (hf_ne : f ≠ 0) (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hgf : StrictInterl g f) (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative + w * g))
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative + w * g).natDegree)
    (hdeg_hi : (u * f + v * f.derivative + w * g).natDegree ≤ f.natDegree + 1)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0)
    (hw_nonpos : ∀ r, f.IsRoot r → w.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative + w * g) := by
  have _hf_ne := hf_ne
  apply strictInterl_derivative_lag_of_combined_flux hf_pos hf hgf hg_pos
  · intro r hr
    have hgf_sign := hgf.eval_mul_eval_derivative_nonneg hg_pos hf_pos hr
    nlinarith [hv_nonpos r hr, hw_nonpos r hr, sq_nonneg (f.derivative.eval r)]
  · exact fun r hr _ ↦ hv_nonpos r hr
  · exact fun r hr _ ↦ hw_nonpos r hr
  · exact hF_pos
  · exact hdeg_lo
  · exact hdeg_hi

/-! ## Regression examples -/

example : StrictInterl (X ^ 2 : ℝ[X])
    ((1 : ℝ[X]) * X ^ 2 + (0 : ℝ[X]) * X ^ 2) := by
  have hrr : (X ^ 2 : ℝ[X]) ≠ 0 ∧ (X ^ 2 : ℝ[X]).Splits :=
    ⟨by simp, Splits.X_pow 2⟩
  have hsum : (1 : ℝ[X]) * X ^ 2 + (0 : ℝ[X]) * X ^ 2 =
      (1 : ℝ[X]) * X ^ 2 + ∑ i ∈ ({0} : Finset Unit),
        (0 : ℝ[X]) * X ^ 2 := by simp
  rw [hsum]
  apply strictInterl_mul_add_sum_mul_of_eval_nonpos (s := ({0} : Finset Unit))
    (b := fun _ : Unit ↦ (0 : ℝ[X])) (g := fun _ : Unit ↦ (X ^ 2 : ℝ[X])) hrr.1 hrr.2
  · intro i hi
    simpa using StrictInterl.refl hrr.1 hrr.2
  · intro i hi
    simpa using hasPosLeadingCoeff_of_monic (monic_X_pow 2)
  · intro i hi r hr
    simp
  · simp [HasPosLeadingCoeff]
  · simp
  · simp

example : StrictInterl (X ^ 2 : ℝ[X])
    ((1 : ℝ[X]) * X ^ 2 + ∑ _i ∈ (∅ : Finset Unit),
      (0 : ℝ[X]) * X ^ 2) := by
  have hrr : (X ^ 2 : ℝ[X]) ≠ 0 ∧ (X ^ 2 : ℝ[X]).Splits :=
    ⟨by simp, Splits.X_pow 2⟩
  apply strictInterl_mul_add_sum_mul_of_eval_nonpos (s := (∅ : Finset Unit))
    (b := fun _ : Unit ↦ (0 : ℝ[X])) (g := fun _ : Unit ↦ (X ^ 2 : ℝ[X])) hrr.1 hrr.2
  · simp
  · simp
  · simp
  · simp [HasPosLeadingCoeff]
  · simp
  · simp

end RealRooted.LiuWang
