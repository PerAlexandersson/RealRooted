/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.Coefficients
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Partial sums of the arcsine series at `s = 1` are at most `π/2`
Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.
-/

@[expose] public section

open PowerSeries Real

namespace RealRooted.CenteredEulerian

/-- Partial sums of `1/√(1-s²)`. -/
noncomputable def Wsum (N : ℕ) (s : ℝ) : ℝ := ∑ n ∈ Finset.range (N + 1), ic n * s ^ n
/-- Their derivative. -/
noncomputable def Wder (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ic n * ((n : ℝ) * s ^ (n - 1))

lemma hasDerivAt_Wsum (N : ℕ) (s : ℝ) : HasDerivAt (Wsum N) (Wder N s) s := by
  unfold Wsum Wder
  have : ∀ n ∈ Finset.range (N + 1), HasDerivAt (fun s => ic n * s ^ n)
      (ic n * ((n : ℝ) * s ^ (n - 1))) s := by
    intro n _
    exact (hasDerivAt_pow n s).const_mul (ic n)
  have h := HasDerivAt.fun_sum this
  convert h using 1

lemma Wkey (N : ℕ) (s : ℝ) : (1 - s ^ 2) * Wder N s - s * Wsum N s =
    -((N : ℝ) * ic (N - 1) * s ^ N + (N + 1) * ic N * s ^ (N + 1)) := by
  induction N with
  | zero => simp [Wder, Wsum, ic_zero]
  | succ N ih =>
    have e1 : Wder (N + 1) s = Wder N s + ic (N + 1) * (((N + 1 : ℕ) : ℝ) * s ^ N) := by
      rw [Wder, Finset.sum_range_succ, ← Wder]; simp
    have e2 : Wsum (N + 1) s = Wsum N s + ic (N + 1) * s ^ (N + 1) := by
      rw [Wsum, Finset.sum_range_succ, ← Wsum]
    rw [e1, e2]
    have hrel : (N : ℝ) * ic (N - 1) = (N + 1) * ic (N + 1) := by
      rcases N with _ | N
      · simp [ic_one]
      · rw [show N + 1 + 1 = N + 2 by ring, ic_rec, show N + 1 - 1 = N by lia]
        push_cast; field_simp; ring
    have : (1 - s ^ 2) * (Wder N s + ic (N + 1) * (((N + 1 : ℕ) : ℝ) * s ^ N)) -
        s * (Wsum N s + ic (N + 1) * s ^ (N + 1)) =
        ((1 - s ^ 2) * Wder N s - s * Wsum N s) + (N + 1) * ic (N + 1) * s ^ N -
          (N + 2) * ic (N + 1) * s ^ (N + 2) := by push_cast; ring
    rw [this, ih, show N + 1 - 1 = N by lia]
    push_cast
    linear_combination (-(s ^ N)) * hrel

lemma Wsum_mul_sqrt_le (N : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Wsum N s * Real.sqrt (1 - s ^ 2) ≤ 1 := by
  set u : ℝ → ℝ := fun t => Real.sqrt (1 - t ^ 2) * Wsum N t with hu
  have hanti : AntitoneOn u (Set.Ico 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
    · apply ContinuousOn.mul
      · exact (continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).continuousOn
      · exact fun t _ => (hasDerivAt_Wsum N t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.mul
      · exact DifferentiableAt.sqrt ((differentiableAt_const _).sub (differentiableAt_pow 2))
          hpos.ne'
      · exact (hasDerivAt_Wsum N t).differentiableAt
    · intro t ht
      rw [interior_Ico] at ht
      have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hsq : HasDerivAt (fun t => Real.sqrt (1 - t ^ 2))
          (-(t) / Real.sqrt (1 - t ^ 2)) t := by
        have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
          have := (hasDerivAt_pow 2 t).const_sub 1
          simpa using this
        have h2 := (Real.hasDerivAt_sqrt hpos.ne').comp t h1
        convert h2 using 1
        · rfl
        · have hsqrt : Real.sqrt (1 - t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
          field_simp [hsqrt]
      have hd : HasDerivAt u (-t / Real.sqrt (1 - t ^ 2) * Wsum N t +
          Real.sqrt (1 - t ^ 2) * Wder N t) t := hsq.mul (hasDerivAt_Wsum N t)
      rw [hd.deriv]
      have hsqrt : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
      have key := Wkey N t
      have hnum : (1 - t ^ 2) * Wder N t - t * Wsum N t ≤ 0 := by
        rw [key]
        have := (ic_props (N - 1)).1; have := (ic_props N).1
        have ht0 : 0 ≤ t := ht.1.le
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have : 0 ≤ (N : ℝ) * ic (N - 1) * t ^ N + (N + 1) * ic N * t ^ (N + 1) := by positivity
        linarith
      have : -t / Real.sqrt (1 - t ^ 2) * Wsum N t + Real.sqrt (1 - t ^ 2) * Wder N t =
          ((1 - t ^ 2) * Wder N t - t * Wsum N t) / Real.sqrt (1 - t ^ 2) := by
        field_simp
        rw [Real.sq_sqrt hpos.le]
        ring
      rw [this]
      exact div_nonpos_of_nonpos_of_nonneg hnum hsqrt.le
  have h0 : u 0 = 1 := by simp [hu, Wsum, Finset.sum_range_succ', ic_zero]
  have := hanti ⟨le_refl 0, by norm_num⟩ ⟨hs0, hs1⟩ hs0
  rw [h0] at this
  simp only [hu] at this
  linarith

/-- Partial sums of the arcsine series. -/
noncomputable def Fsum (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ic n / (n + 1) * s ^ (n + 1)

lemma hasDerivAt_Fsum (N : ℕ) (s : ℝ) : HasDerivAt (Fsum N) (Wsum N s) s := by
  unfold Fsum Wsum
  have : ∀ n ∈ Finset.range (N + 1), HasDerivAt (fun s => ic n / (n + 1) * s ^ (n + 1))
      (ic n * s ^ n) s := by
    intro n _
    have := (hasDerivAt_pow (n + 1) s).const_mul (ic n / (n + 1))
    convert this using 1
    push_cast
    field_simp
  have h := HasDerivAt.fun_sum this
  convert h using 1

lemma Fsum_one_le (N : ℕ) : Fsum N 1 ≤ π / 2 := by
  set G : ℝ → ℝ := fun t => Real.arcsin t - Fsum N t with hG
  have hmono : MonotoneOn G (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · apply ContinuousOn.sub Real.continuous_arcsin.continuousOn
      exact fun t _ => (hasDerivAt_Fsum N t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub
      · exact (Real.hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.2])).differentiableAt
      · exact (hasDerivAt_Fsum N t).differentiableAt
    · intro t ht
      rw [interior_Icc] at ht
      have hd : HasDerivAt G (1 / Real.sqrt (1 - t ^ 2) - Wsum N t) t :=
        (Real.hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.2])).sub
          (hasDerivAt_Fsum N t)
      rw [hd.deriv]
      have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hsqrt : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
      have := Wsum_mul_sqrt_le N ht.1.le ht.2
      rw [sub_nonneg, le_div_iff₀ hsqrt]
      linarith
  have h := hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [hG, Real.arcsin_zero, Real.arcsin_one] at h
  have h0 : Fsum N 0 = 0 := by simp [Fsum]
  rw [h0] at h
  linarith

/-- `∑_{n ≤ K} f_n ≤ π/2`. -/
theorem sum_coeff_fS_le (K : ℕ) : ∑ n ∈ Finset.range K, coeff n fS ≤ π / 2 := by
  have h1 : ∑ n ∈ Finset.range K, coeff n fS ≤
      ∑ n ∈ Finset.range (K + 1 + 1), coeff n fS :=
    Finset.sum_le_sum_of_subset_of_nonneg (by simp; lia) (fun n _ _ => coeff_fS_nonneg n)
  have h2 : ∑ n ∈ Finset.range (K + 1 + 1), coeff n fS = Fsum K 1 := by
    rw [Finset.sum_range_succ', coeff_fS_zero, add_zero, Fsum]
    apply Finset.sum_congr rfl; intro n _; rw [coeff_fS_succ]; simp
  have := Fsum_one_le K
  linarith

end RealRooted.CenteredEulerian
