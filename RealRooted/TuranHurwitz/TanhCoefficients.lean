module

public import RealRooted.TuranHurwitz.TanhKernel
public import RealRooted.TuranHurwitz.KernelCoefficients
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Roots of the base tanh-kernel coefficients

Translation by one moves the sinh coefficient roots from `[-1, 0]` to `[0, 1]`.
After extending scalars, all roots therefore lie in the closed complex unit disk.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The even base coefficient has degree equal to its half-index. -/
theorem natDegree_coeff_even_tanhKernel {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (PowerSeries.coeff (2 * n) (tanhKernel d)).natDegree = n := by
  rw [coeff_even_tanhKernel, natDegree_comp,
    show (X - 1 : ℝ[X]).natDegree = 1 by simpa using natDegree_X_sub_C (1 : ℝ), mul_one]
  exact natDegree_coeff_even_hyperbolicKernel hd n

/-- The real base coefficient is nonzero, splits, and has every root in `[0, 1]`. -/
theorem coeff_even_tanhKernel_roots {d : ℝ} (hd : 0 < d) (n : ℕ) :
    PowerSeries.coeff (2 * n) (tanhKernel d) ≠ 0 ∧
      (PowerSeries.coeff (2 * n) (tanhKernel d)).Splits ∧
      ∀ r ∈ (PowerSeries.coeff (2 * n) (tanhKernel d)).roots,
        r ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hp, hs, hr⟩ := coeff_even_hyperbolicKernel_roots hd n
  rw [coeff_even_tanhKernel]
  have hne : (PowerSeries.coeff (2 * n) (hyperbolicKernel d)).comp (X - 1) ≠ 0 := by
    simpa only [map_neg, map_one, sub_eq_add_neg] using
      (comp_X_add_C_ne_zero_iff (t := (-1 : ℝ))).mpr hp
  refine ⟨hne, by simpa using hs.comp_X_sub_C 1, ?_⟩
  intro r hroot
  have heval := (mem_roots hne).mp hroot
  rw [IsRoot.def, eval_comp, eval_sub, eval_X, eval_one] at heval
  have h := hr (r - 1) ((mem_roots hp).mpr heval)
  constructor <;> linarith [h.1, h.2]

/-- Extending a split interval-rooted real polynomial gives roots in the unit disk. -/
theorem roots_map_real_norm_le_one {p : ℝ[X]} (hs : p.Splits)
    (hr : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1 := by
  rw [hs.roots_map (algebraMap ℝ ℂ)]
  intro z hz
  obtain ⟨r, hroot, rfl⟩ := Multiset.mem_map.mp hz
  change ‖(r : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact hr r hroot

/-- The base complex coefficient has no roots outside the unit disk. -/
theorem coeff_even_tanhKernel_complex_roots {d : ℝ} (hd : 0 < d) (n : ℕ) :
    ∀ z ∈ ((PowerSeries.coeff (2 * n) (tanhKernel d)).map
      (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1 := by
  obtain ⟨_, hs, hr⟩ := coeff_even_tanhKernel_roots hd n
  apply roots_map_real_norm_le_one hs
  intro r hroot
  have h := hr r hroot
  exact ⟨by linarith [h.1], h.2⟩

end RealRooted.TuranHurwitz
