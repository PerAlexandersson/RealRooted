/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.AnalyticBranch
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# Logarithmic branches and sector continuations

The open-strip principal branch extends continuously to both radial edges.
Its square on the closed strip follows by density, without separate endpoint algebra.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate Interval Topology

/-- A continuous half-plane square-root formula with chosen imaginary sign. -/
def sidedRoot (side : ℝ) (u : ℂ) : ℂ :=
  (Real.sqrt ((‖u‖ + u.re) / 2) : ℂ) +
    ((side * Real.sqrt ((‖u‖ - u.re) / 2) : ℝ) : ℂ) * I

private theorem sidedRoot_continuous (side : ℝ) : Continuous (sidedRoot side) := by
  unfold sidedRoot
  fun_prop

private theorem sidedRoot_real_nonneg (side a : ℝ) (ha : 0 ≤ a) :
    sidedRoot side (a : ℂ) = (Real.sqrt a : ℂ) := by
  have h : (a + a) / 2 = a := by ring
  simp [sidedRoot, abs_of_nonneg ha, h]

private theorem sidedRoot_real_nonpos (side a : ℝ) (ha : a ≤ 0) :
    sidedRoot side (a : ℂ) = ((side * Real.sqrt (-a) : ℝ) : ℂ) * I := by
  have h : (-a - a) / 2 = -a := by ring
  simp [sidedRoot, abs_of_nonpos ha, h]

private theorem sidedRoot_above {u : ℂ} (h : 0 ≤ u.im) :
    sidedRoot 1 u = principalRoot u := by
  apply Complex.ext
  · simp [sidedRoot, principalRoot, Complex.mul_re, cpow_inv_two_re]
  · simp [sidedRoot, principalRoot, Complex.mul_im, cpow_inv_two_im_eq_sqrt h]

private theorem sidedRoot_below {u : ℂ} (h : u.im ≤ 0) (hu : u ∈ slitPlane) :
    sidedRoot (-1) u = principalRoot u := by
  have he : sidedRoot (-1) u = conj (sidedRoot 1 (conj u)) := by
    apply Complex.ext <;> simp [sidedRoot]
  rw [he, sidedRoot_above (by simpa only [Complex.conj_im, neg_nonneg] using h),
    principalRoot_conj hu, Complex.conj_conj]

/-- The normalized factor in logarithmic coordinates. -/
def logRootArgument (R : ℝ) (x : ℂ) : ℂ := 1 - exp x / (R : ℂ)

/-- Extend the principal square root from inside a full logarithmic strip. -/
def logStripRoot (R : ℝ) (x : ℂ) : ℂ :=
  if x.im ≤ Real.pi then sidedRoot (-1) (logRootArgument R x)
  else sidedRoot 1 (logRootArgument R x)

private theorem logRootArgument_im (R : ℝ) (x : ℂ) :
    (logRootArgument R x).im = -(Real.exp x.re * Real.sin x.im / R) := by
  simp [logRootArgument, Complex.exp_im]

private theorem logRootArgument_at {R : ℝ} (x y : ℝ) (hc : Real.cos y = 1)
    (hs : Real.sin y = 0) :
    logRootArgument R ((x : ℂ) + (y : ℂ) * I) = ((1 - Real.exp x / R : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [logRootArgument, Complex.exp_re, Complex.mul_re, Complex.mul_im, hc]
  · simp [logRootArgument_im, Complex.mul_im, hs]

private theorem logRootArgument_pi (R : ℝ) {x : ℂ} (hx : x.im = Real.pi) :
    logRootArgument R x = ((1 + Real.exp x.re / R : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [logRootArgument, Complex.exp_re, hx, sub_neg_eq_add, neg_div]
  · simp [logRootArgument_im, hx]

/-- The changes in the imaginary part of the square root agree at angle π. -/
theorem logStripRoot_continuous {R : ℝ} (hR : 0 < R) : Continuous (logStripRoot R) := by
  have hArg : Continuous (logRootArgument R) := by
    unfold logRootArgument
    fun_prop
  unfold logStripRoot
  apply Continuous.if_le ((sidedRoot_continuous (-1)).comp hArg)
    ((sidedRoot_continuous 1).comp hArg) continuous_im continuous_const
  intro x hx
  simp only [Function.comp_apply]
  have hp : 0 ≤ 1 + Real.exp x.re / R := by positivity
  rw [logRootArgument_pi R hx, sidedRoot_real_nonneg _ _ hp, sidedRoot_real_nonneg _ _ hp]

private theorem sin_neg_between_pi_two_pi {y : ℝ}
    (h₁ : Real.pi < y) (h₂ : y < 2 * Real.pi) : Real.sin y < 0 := by
  have hSin := Real.sin_pos_of_pos_of_lt_pi (show 0 < y - Real.pi by linarith)
    (show y - Real.pi < Real.pi by linarith)
  rw [Real.sin_sub_pi] at hSin
  linarith

/-- An open logarithmic strip avoids the normalized factor cut. -/
theorem exp_div_mem_slitPlane {R : ℝ} (hR : 0 < R) {x : ℂ}
    (h₁ : 0 < x.im) (h₂ : x.im < 2 * Real.pi) :
    1 - exp x / (R : ℂ) ∈ slitPlane := by
  change logRootArgument R x ∈ slitPlane
  rcases lt_trichotomy x.im Real.pi with ha | ha | ha
  · right
    rw [logRootArgument_im]
    exact neg_ne_zero.mpr (div_pos
      (mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h₁ ha)) hR).ne'
  · rw [logRootArgument_pi R ha, ofReal_mem_slitPlane]
    positivity
  · right
    rw [logRootArgument_im]
    exact neg_ne_zero.mpr (div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (Real.exp_pos _) (sin_neg_between_pi_two_pi ha h₂)) hR).ne

/-- Inside the open strip the extension agrees with the principal root. -/
theorem logStripRoot_eq_principal {R : ℝ} (hR : 0 < R) {x : ℂ}
    (h₁ : 0 < x.im) (h₂ : x.im < 2 * Real.pi) :
    logStripRoot R x = principalRoot (1 - exp x / (R : ℂ)) := by
  unfold logStripRoot
  split_ifs with h
  · apply sidedRoot_below _ (exp_div_mem_slitPlane hR h₁ h₂)
    change (logRootArgument R x).im ≤ 0
    rw [logRootArgument_im, neg_nonpos]
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.sin_nonneg_of_nonneg_of_le_pi h₁.le h)) hR.le
  · apply sidedRoot_above
    rw [logRootArgument_im, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sin_neg_between_pi_two_pi (lt_of_not_ge h) h₂).le) hR.le

private theorem logRootArgument_real (R x : ℝ) :
    logRootArgument R (x : ℂ) = ((1 - Real.exp x / R : ℝ) : ℂ) := by
  simpa using (logRootArgument_at (R := R) x 0 Real.cos_zero Real.sin_zero)

private theorem logStripRoot_lower_boundary (R x : ℝ) :
    logStripRoot R (x : ℂ) = sidedRoot (-1) ((1 - Real.exp x / R : ℝ) : ℂ) := by
  rw [logStripRoot, ite_eq_left (by simpa using Real.pi_pos.le), logRootArgument_real]

private theorem logStripRoot_upper_boundary (R x : ℝ) :
    logStripRoot R ((x : ℂ) + (2 * Real.pi : ℝ) * I) =
      sidedRoot 1 ((1 - Real.exp x / R : ℝ) : ℂ) := by
  rw [logStripRoot, ite_eq_right, logRootArgument_at x _ Real.cos_two_pi Real.sin_two_pi]
  simp [Complex.mul_im, Real.pi_pos]

/-- The two boundary values agree on the inward segment. -/
theorem logStripRoot_boundary_eq (R x : ℝ) (h : Real.exp x / R ≤ 1) :
    logStripRoot R (x : ℂ) = logStripRoot R ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
  rw [logStripRoot_lower_boundary, logStripRoot_upper_boundary,
    sidedRoot_real_nonneg _ _ (sub_nonneg.mpr h), sidedRoot_real_nonneg _ _ (sub_nonneg.mpr h)]

/-- The lower-angle boundary value minus the upper-angle one on the outward ray. -/
theorem logStripRoot_jump (R x : ℝ) (h : 1 ≤ Real.exp x / R) :
    logStripRoot R (x : ℂ) - logStripRoot R ((x : ℂ) + (2 * Real.pi : ℝ) * I) =
      -2 * I * (Real.sqrt (Real.exp x / R - 1) : ℂ) := by
  rw [logStripRoot_lower_boundary, logStripRoot_upper_boundary,
    sidedRoot_real_nonpos _ _ (sub_nonpos.mpr h), sidedRoot_real_nonpos _ _ (sub_nonpos.mpr h),
    neg_sub]
  push_cast
  ring

/-- The defining square extends to the closed strip by continuity. -/
theorem logStripRoot_sq {R : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : 0 ≤ z.im) (h₂ : z.im ≤ 2 * Real.pi) :
    logStripRoot R z ^ 2 = 1 - exp z / (R : ℂ) := by
  have he : EqOn (fun x ↦ logStripRoot R x ^ 2) (fun x ↦ 1 - exp x / (R : ℂ))
      (im ⁻¹' Ioo 0 (2 * Real.pi)) := by
    intro x hx
    change logStripRoot R x ^ 2 = 1 - exp x / (R : ℂ)
    rw [logStripRoot_eq_principal hR hx.1 hx.2, principalRoot_sq]
  apply he.closure ((logStripRoot_continuous hR).pow 2) (by fun_prop)
  rw [closure_preimage_im, closure_Ioo (by linarith [Real.pi_pos])]
  exact ⟨h₁, h₂⟩

private theorem principalRoot_real_nonneg {a : ℝ} (ha : 0 ≤ a) :
    principalRoot (a : ℂ) = (Real.sqrt a : ℂ) := by
  rw [← sidedRoot_above (u := (a : ℂ)) (by simp), sidedRoot_real_nonneg _ _ ha]

/-- On circles inside the branch point, the same principal root also gives
both boundary values of the logarithmic strip. -/
theorem logStripRoot_eq_principal_of_le_radius {R : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : 0 ≤ z.im) (h₂ : z.im ≤ 2 * Real.pi) (hRz : ‖exp z‖ ≤ R) :
    logStripRoot R z = principalRoot (1 - exp z / (R : ℂ)) := by
  have h₃ : 0 ≤ 1 - Real.exp z.re / R := sub_nonneg.mpr
    ((div_le_one hR).mpr (by simpa only [norm_exp] using hRz))
  change logStripRoot R z = principalRoot (logRootArgument R z)
  rcases h₁.eq_or_lt with hbot | hlo
  · have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [← hbot]
    rw [hz, logStripRoot_lower_boundary, logRootArgument_real,
      sidedRoot_real_nonneg _ _ h₃, principalRoot_real_nonneg h₃]
  rcases h₂.eq_or_lt with htop | hhi
  · have hz : z = (z.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [htop, Complex.mul_re, Complex.mul_im]
    rw [hz, logStripRoot_upper_boundary, logRootArgument_at _ _ Real.cos_two_pi Real.sin_two_pi,
      sidedRoot_real_nonneg _ _ h₃, principalRoot_real_nonneg h₃]
  exact logStripRoot_eq_principal hR hlo hhi

private theorem logRootArgument_shift (R θ : ℝ) (z : ℂ) :
    logRootArgument R (z - (θ : ℂ) * I) =
      1 - exp z / ((R : ℂ) * exp ((θ : ℂ) * I)) := by
  rw [logRootArgument, Complex.exp_sub, div_div, mul_comm (exp _)]

/-- Rotating the open strip avoids the radial cut of the rotated factor. -/
theorem exp_div_mem_slitPlane_shift {R θ : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : θ < z.im) (h₂ : z.im < θ + 2 * Real.pi) :
    1 - exp z / ((R : ℂ) * exp ((θ : ℂ) * I)) ∈ slitPlane := by
  rw [← logRootArgument_shift]
  apply exp_div_mem_slitPlane hR
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]; linarith
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]; linarith

/-- Rotating the strip handles the radial cut in the direction of a branch point. -/
theorem logStripRoot_eq_cutFactor {R θ : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : θ < z.im) (h₂ : z.im < θ + 2 * Real.pi) :
    logStripRoot R (z - (θ : ℂ) * I) = cutFactor ((R : ℂ) * exp ((θ : ℂ) * I)) (exp z) := by
  rw [logStripRoot_eq_principal hR, cutFactor, Complex.exp_sub, div_div, mul_comm (exp _)]
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]
    linarith
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]
    linarith

/-- The rotated strip branch agrees with the principal factor up to both
edges on a circle inside its branch point. -/
theorem logStripRoot_eq_cutFactor_of_le_radius {R θ : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : θ ≤ z.im) (h₂ : z.im ≤ θ + 2 * Real.pi) (hz : ‖exp z‖ ≤ R) :
    logStripRoot R (z - (θ : ℂ) * I) = cutFactor ((R : ℂ) * exp ((θ : ℂ) * I)) (exp z) := by
  rw [logStripRoot_eq_principal_of_le_radius hR]
  · change principalRoot (logRootArgument R (z - (θ : ℂ) * I)) = _
    rw [logRootArgument_shift, cutFactor]
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]; linarith
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]; linarith
  · simpa [norm_exp, Complex.mul_re] using hz

/-- The branch points in circular order, starting with the upper near point. -/
def cutPoint (d : ℝ) (i : Fin 4) : ℂ :=
  match i.val with
  | 0 => nearPoint d
  | 1 => farPoint d
  | 2 => conj (farPoint d)
  | _ => conj (nearPoint d)

private theorem near_arg_bounds {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    0 < (nearPoint d).arg ∧ (nearPoint d).arg < Real.pi / 2 := by
  have him := nearPoint_im_pos hd hD
  refine ⟨lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) ?_,
    arg_lt_pi_div_two_iff.mpr (Or.inl (nearPoint_re_pos hd))⟩
  intro h
  exact him.ne' (arg_eq_zero_iff.mp h.symm).2

private theorem far_arg_bounds {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    Real.pi / 2 < (farPoint d).arg ∧ (farPoint d).arg < Real.pi := by
  have him := farPoint_im_pos hd hD
  have hre := farPoint_re_neg hd
  refine ⟨lt_of_not_ge ?_, arg_lt_pi_iff.mpr (Or.inr him.ne')⟩
  intro h
  exact (arg_le_pi_div_two_iff.mp h).elim (not_le_of_gt hre) (not_lt_of_gt him)

/-- The real-axis endpoints and the four cut angles in increasing order. -/
def sectorAngle (d : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => (nearPoint d).arg
  | 2 => (farPoint d).arg
  | 3 => 2 * Real.pi - (farPoint d).arg
  | 4 => 2 * Real.pi - (nearPoint d).arg
  | _ => 2 * Real.pi

/-- Adjacent cut angles are strictly ordered. -/
theorem sectorAngle_step {d : ℝ} (hd : 0 < d) (hD : d < 1) {j : ℕ}
    (hj : j ≤ 4) : sectorAngle d j < sectorAngle d (j + 1) := by
  have hn := near_arg_bounds hd hD
  have hf := far_arg_bounds hd hD
  interval_cases j <;> simp only [sectorAngle, Nat.reduceAdd] <;>
    linarith [hn.1, hn.2, hf.1, hf.2]

/-- The extended cut-angle sequence is monotone. -/
theorem sectorAngle_mono {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    Monotone (sectorAngle d) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases hj : j ≤ 4
  · exact (sectorAngle_step hd hD hj).le
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by lia⟩
    rfl

/-- The circular cut angle gives the polar form of each point. -/
theorem cutPoint_polar {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    (‖cutPoint d i‖ : ℂ) * exp ((sectorAngle d (i.val + 1) : ℂ) * I) = cutPoint d i := by
  have hn := near_arg_bounds hd hD
  have hf := far_arg_bounds hd hD
  have hPolarConj (u : ℂ) (hu : u.arg < Real.pi) :
      (‖conj u‖ : ℂ) * exp (((2 * Real.pi - u.arg : ℝ) : ℂ) * I) = conj u := by
    have hArg : (conj u).arg = -u.arg := by simp [Complex.arg_conj, hu.ne]
    have hExp : exp (((2 * Real.pi - u.arg : ℝ) : ℂ) * I) =
        exp (((-u.arg : ℝ) : ℂ) * I) := by
      rw [show 2 * Real.pi - u.arg = -u.arg + 2 * Real.pi by ring]
      push_cast
      exact Complex.exp_mul_I_periodic (-(u.arg : ℂ))
    rw [hExp, ← hArg]
    exact norm_mul_exp_arg_mul_I _
  fin_cases i
  · exact norm_mul_exp_arg_mul_I _
  · exact norm_mul_exp_arg_mul_I _
  · exact hPolarConj _ hf.2
  · exact hPolarConj _ (by linarith [hn.2, Real.pi_pos])

/-- Choose a representative of each cut angle immediately below the sector. -/
def liftedAngle (d : ℝ) (j : ℕ) (i : Fin 4) : ℝ :=
  if i.val < j then sectorAngle d (i.val + 1) else sectorAngle d (i.val + 1) - 2 * Real.pi

/-- Lifting an angle preserves its branch point. -/
theorem liftedAngle_polar {d : ℝ} (hd : 0 < d) (hD : d < 1) (j : ℕ) (i : Fin 4) :
    (‖cutPoint d i‖ : ℂ) * exp ((liftedAngle d j i : ℂ) * I) = cutPoint d i := by
  unfold liftedAngle
  split_ifs
  · exact cutPoint_polar hd hD i
  · rw [show exp (((sectorAngle d (i.val + 1) - 2 * Real.pi : ℝ) : ℂ) * I) =
        exp ((sectorAngle d (i.val + 1) : ℂ) * I) by
      push_cast
      exact Complex.exp_mul_I_periodic.sub_eq (sectorAngle d (i.val + 1) : ℂ)]
    exact cutPoint_polar hd hD i

/-- Each sector lies in every lifted closed strip. -/
theorem liftedAngle_within_strip {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) (i : Fin 4) {y : ℝ}
    (hy : y ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    liftedAngle d j i ≤ y ∧ y ≤ liftedAngle d j i + 2 * Real.pi := by
  have hmono := sectorAngle_mono hd hD
  have hβ₀ : 0 ≤ sectorAngle d (i.val + 1) := hmono (Nat.zero_le _)
  have hβ₁ : sectorAngle d (i.val + 1) ≤ 2 * Real.pi := hmono (show i.val + 1 ≤ 5 by lia)
  have hlow : 0 ≤ sectorAngle d j := hmono (Nat.zero_le _)
  have hhigh : sectorAngle d (j + 1) ≤ 2 * Real.pi := hmono (show j + 1 ≤ 5 by lia)
  unfold liftedAngle
  split_ifs with hi
  · refine ⟨(hmono (show i.val + 1 ≤ j by lia)).trans hy.1, ?_⟩
    linarith [hy.2]
  · refine ⟨?_, hy.2.trans ?_⟩
    · linarith [hy.1]
    · simpa using hmono (show j + 1 ≤ i.val + 1 by lia)

/-- A square-root factor continued across a closed sector. -/
def sectorFactor (d : ℝ) (j : ℕ) (i : Fin 4) (z : ℂ) : ℂ :=
  logStripRoot ‖cutPoint d i‖ (z - (liftedAngle d j i : ℂ) * I)

/-- The product of four continued square-root factors. -/
def logBranch (d : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin 4, sectorFactor d j i z

private lemma cutPoint_norm {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    ‖cutPoint d i‖ = if i = 0 ∨ i = 3 then radius d else (radius d)⁻¹ := by
  fin_cases i <;> simp [cutPoint, nearPoint_norm hd hD, farPoint_norm hd hD]

/-- Every branch point has positive norm. -/
theorem cutPoint_norm_pos {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    0 < ‖cutPoint d i‖ := by
  rw [cutPoint_norm hd hD]
  have hp := radius_pos hd.le
  split_ifs <;> positivity

/-- Every branch point lies outside the dominant open disk. -/
theorem radius_le_cutPoint {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    radius d ≤ ‖cutPoint d i‖ := by
  rw [cutPoint_norm hd hD]
  split_ifs
  · rfl
  · simpa only [nearPoint_norm hd hD, farPoint_norm hd hD] using (norm_order hd hD).le

private theorem cutFactor_product (d : ℝ) (z : ℂ) :
    (∏ i : Fin 4, cutFactor (cutPoint d i) z) = branch d z := by
  simp only [Fin.prod_univ_four, cutPoint, branch, Fin.val_zero, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod]
  ring

private theorem logBranch_continuous {d : ℝ} (hd : 0 < d) (hD : d < 1) (j : ℕ) :
    Continuous (logBranch d j) := by
  unfold logBranch sectorFactor
  apply continuous_finsetProd Finset.univ
  intro i _
  exact (logStripRoot_continuous (cutPoint_norm_pos hd hD i)).comp (by fun_prop)

/-- The continued product squares to the quartic on a closed sector. -/
theorem logBranch_sq {d : ℝ} (hd : 0 < d) (hD : d < 1) {j : ℕ} (hj : j ≤ 4)
    {z : ℂ} (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    logBranch d j z ^ 2 = quartic (scale d) (exp z) := by
  rw [← branch_sq hd hD, ← cutFactor_product, logBranch, ← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨h₁, h₂⟩ := liftedAngle_within_strip hd hD hj i hz
  rw [sectorFactor, logStripRoot_sq (cutPoint_norm_pos hd hD i), cutFactor, principalRoot_sq,
    Complex.exp_sub, div_div, mul_comm (exp _), liftedAngle_polar hd hD]
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]; linarith
  · simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]; linarith

private theorem logBranch_eq_branch_of_lifts {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} {z : ℂ} (hz : ∀ i : Fin 4, liftedAngle d j i < z.im ∧
      z.im < liftedAngle d j i + 2 * Real.pi) :
    logBranch d j z = branch d (exp z) := by
  rw [← cutFactor_product, logBranch]
  apply Finset.prod_congr rfl
  intro i _
  rw [sectorFactor, logStripRoot_eq_cutFactor (cutPoint_norm_pos hd hD i) (hz i).1 (hz i).2,
    liftedAngle_polar hd hD]

private lemma liftedAngle_inside_strip {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {y : ℝ}
    (hy : y ∈ Ioo (sectorAngle d j) (sectorAngle d (j + 1))) (i : Fin 4) :
    liftedAngle d j i < y ∧ y < liftedAngle d j i + 2 * Real.pi := by
  have hl := (liftedAngle_within_strip hd hD hj i
    ⟨le_rfl, (sectorAngle_step hd hD hj).le⟩).1
  have hu := (liftedAngle_within_strip hd hD hj i
    ⟨(sectorAngle_step hd hD hj).le, le_rfl⟩).2
  exact ⟨hl.trans_lt hy.1, hy.2.trans_le hu⟩

private theorem logBranch_eq_branch_inside {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Ioo (sectorAngle d j) (sectorAngle d (j + 1))) :
    logBranch d j z = branch d (exp z) :=
  logBranch_eq_branch_of_lifts hd hD (liftedAngle_inside_strip hd hD hj hz)

/-- The continued product agrees with the principal branch on inner circles. -/
theorem logBranch_eq_branch_inner {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1)))
    (hr : ‖exp z‖ ≤ radius d) :
    logBranch d j z = branch d (exp z) := by
  rw [← cutFactor_product, logBranch]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨h₁, h₂⟩ := liftedAngle_within_strip hd hD hj i hz
  rw [sectorFactor, logStripRoot_eq_cutFactor_of_le_radius (cutPoint_norm_pos hd hD i) h₁ h₂
    (hr.trans (radius_le_cutPoint hd hD i)), liftedAngle_polar hd hD]

private theorem cutPoint_im_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    (cutPoint d i).im ≠ 0 := by
  have hn := (nearPoint_im_pos hd hD).ne'
  have hf := (farPoint_im_pos hd hD).ne'
  fin_cases i
  · exact hn
  · exact hf
  · simpa [cutPoint, Complex.conj_im] using hf
  · simpa [cutPoint, Complex.conj_im] using hn

/-- Every radial cut avoids the real axis. -/
theorem exp_im_ne_zero_on_cut {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : ℕ) (i : Fin 4) (z : ℂ)
    (hy : z.im = liftedAngle d j i ∨ z.im = liftedAngle d j i + 2 * Real.pi) :
    (exp z).im ≠ 0 := by
  have hPolar := liftedAngle_polar hd hD j i
  have hExp : exp ((z.im : ℂ) * I) = exp ((liftedAngle d j i : ℂ) * I) := by
    rcases hy with hy | hy
    · rw [hy]
    · rw [hy]
      push_cast
      exact Complex.exp_mul_I_periodic (liftedAngle d j i : ℂ)
  have hr : (‖cutPoint d i‖ : ℂ) ≠ 0 := by exact_mod_cast (cutPoint_norm_pos hd hD i).ne'
  have hS : exp z = ((Real.exp z.re / ‖cutPoint d i‖ : ℝ) : ℂ) * cutPoint d i := by
    calc
      exp z = (Real.exp z.re : ℂ) * exp ((liftedAngle d j i : ℂ) * I) := by
        conv_lhs => rw [← Complex.re_add_im z, exp_add, hExp]
        rw [Complex.ofReal_exp]
      _ = ((Real.exp z.re / ‖cutPoint d i‖ : ℝ) : ℂ) *
          ((‖cutPoint d i‖ : ℂ) * exp ((liftedAngle d j i : ℂ) * I)) := by
        push_cast
        field_simp [hr]
      _ = _ := by rw [hPolar]
  rw [hS, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_ne_zero (div_pos (Real.exp_pos _) (cutPoint_norm_pos hd hD i)).ne'
    (cutPoint_im_ne_zero hd hD i)

/-- The continued generating denominator never vanishes on a sector. -/
theorem logGenerating_denominator_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Icc (sectorAngle d j) (sectorAngle d (j + 1))) :
    1 - (exp z) ^ 2 + logBranch d j z ≠ 0 := by
  intro h
  have hprod : (1 - (exp z) ^ 2 - logBranch d j z) *
      (1 - (exp z) ^ 2 + logBranch d j z) = 4 * exp z * ((scale d : ℂ) - exp z) := by
    calc
      _ = (1 - (exp z) ^ 2) ^ 2 - logBranch d j z ^ 2 := by ring
      _ = _ := by rw [logBranch_sq hd hD hj hz]; unfold quartic; ring
  rw [h, mul_zero, eq_comm, mul_eq_zero, mul_eq_zero] at hprod
  have hexp : exp z = (scale d : ℂ) := by
    rcases hprod with (h4 | he) | hs
    · norm_num at h4
    · exact (exp_ne_zero _ he).elim
    · exact (sub_eq_zero.mp hs).symm
  have hIm : (exp z).im = 0 := by simp [hexp]
  have hstrict (i : Fin 4) :
      liftedAngle d j i < z.im ∧ z.im < liftedAngle d j i + 2 * Real.pi := by
    obtain ⟨hlo, hhi⟩ := liftedAngle_within_strip hd hD hj i hz
    refine ⟨hlo.lt_of_ne ?_, hhi.lt_of_ne ?_⟩
    · intro he
      exact exp_im_ne_zero_on_cut hd hD j i z (Or.inl he.symm) hIm
    · intro he
      exact exp_im_ne_zero_on_cut hd hD j i z (Or.inr he) hIm
  rw [logBranch_eq_branch_of_lifts hd hD hstrict] at h
  exact rationalized_denominator_ne_zero hd hD _ h

/-- The coefficient integrand continued to a closed logarithmic sector. -/
def logSector (d : ℝ) (n j : ℕ) (z : ℂ) : ℂ :=
  (exp z)⁻¹ ^ n * (2 / (1 - (exp z) ^ 2 + logBranch d j z))

/-- The principal coefficient integrand in logarithmic coordinates. -/
def logIntegrand (d : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (exp z)⁻¹ ^ n * analyticGenerating d (exp z)

private theorem exp_mem_slitDomain {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) {z : ℂ}
    (hz : z.im ∈ Ioo (sectorAngle d j) (sectorAngle d (j + 1))) :
    exp z ∈ slitDomain d := by
  have hFactor (i : Fin 4) : 1 - exp z / cutPoint d i ∈ slitPlane := by
    obtain ⟨h₁, h₂⟩ := liftedAngle_inside_strip hd hD hj hz i
    rw [← liftedAngle_polar hd hD j i]
    exact exp_div_mem_slitPlane_shift (cutPoint_norm_pos hd hD i)
      h₁ h₂
  exact ⟨hFactor 0, hFactor 3, hFactor 1, hFactor 2⟩

/-- The coefficient integrand is continuous on each closed sector. -/
theorem logSector_continuousOn {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) (n : ℕ) :
    ContinuousOn (logSector d n j) (im ⁻¹' Icc (sectorAngle d j) (sectorAngle d (j + 1))) := by
  have hInv : Continuous fun z : ℂ => (exp z)⁻¹ := continuous_exp.inv₀ exp_ne_zero
  have hDen : Continuous (fun z : ℂ => 1 - (exp z) ^ 2 + logBranch d j z) :=
    (continuous_const.sub (continuous_exp.pow 2)).add (logBranch_continuous hd hD j)
  exact (hInv.pow n).continuousOn.mul
    (continuousOn_const.div hDen.continuousOn fun z hz =>
      logGenerating_denominator_ne_zero hd hD hj hz)

/-- The coefficient integrand is holomorphic in each open sector. -/
theorem logSector_differentiableOn {d : ℝ} (hd : 0 < d) (hD : d < 1)
    {j : ℕ} (hj : j ≤ 4) (n : ℕ) :
    DifferentiableOn ℂ (logSector d n j)
      (im ⁻¹' Ioo (sectorAngle d j) (sectorAngle d (j + 1))) := by
  have hDiff : DifferentiableOn ℂ (logIntegrand d n)
      (im ⁻¹' Ioo (sectorAngle d j) (sectorAngle d (j + 1))) := by
    intro z hz
    have hInv : DifferentiableAt ℂ (fun u : ℂ => (exp u)⁻¹) z :=
      (differentiable_exp z).inv (exp_ne_zero z)
    have hGen := (analyticGenerating_analyticAt hd hD
      (exp_mem_slitDomain hd hD hj hz)).differentiableAt.comp z (differentiable_exp z)
    exact ((hInv.pow n).mul hGen).differentiableWithinAt
  apply hDiff.congr
  intro z hz
  simp only [logSector, logIntegrand, analyticGenerating, logBranch_eq_branch_inside hd hD hj hz]

/-- The first and last sector agree on the positive real boundary. -/
theorem logSector_periodic_boundary (d : ℝ) (n : ℕ) (x : ℝ) :
    logSector d n 0 (x : ℂ) = logSector d n 4 ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
  have hExp : exp ((x : ℂ) + (2 * Real.pi : ℝ) * I) = exp (x : ℂ) := by
    push_cast
    exact Complex.exp_periodic (x : ℂ)
  have hBranch : logBranch d 0 (x : ℂ) = logBranch d 4 ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
    unfold logBranch
    apply Finset.prod_congr rfl
    intro i _
    simp only [sectorFactor, liftedAngle, Nat.not_lt_zero, ite_false, i.isLt, ite_true]
    congr 1
    push_cast
    ring
  simp only [logSector, hExp, hBranch]

private theorem inside_disk_norm {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ‖exp ((Real.log r : ℂ) + (y : ℂ) * I)‖ = r := by
  simp [Complex.norm_exp, Complex.mul_re, Real.exp_log hr]

/-- The coefficient integrand is continuous along an inner circle. -/
theorem logIntegrand_continuous_on_circle {d r : ℝ} (hd : 0 < d) (hD : d < 1)
    (h₀ : 0 < r) (hr : r < radius d) (n : ℕ) :
    Continuous (fun y : ℝ => logIntegrand d n ((Real.log r : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  let x : ℝ → ℂ := fun t => exp ((Real.log r : ℂ) + (t : ℂ) * I)
  have hx : x y ∈ Metric.closedBall (0 : ℂ) r :=
    mem_closedBall_zero_iff.mpr (inside_disk_norm h₀ y).le
  have hExp : ContinuousAt x y := by dsimp [x]; fun_prop
  have hGen := (analyticGenerating_analyticAt hd hD
    (closedBall_subset_slitDomain hd hD hr hx)).continuousAt
  exact ((hExp.inv₀ (exp_ne_zero _)).pow n).mul (hGen.comp hExp)

end RealRooted.CatalanWordPeaks.CutGeometry
