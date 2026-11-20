module

public import RealRooted.TuranHurwitz.TuranCoefficients
public import RealRooted.TuranHurwitz.DiskCoefficients
public import RealRooted.TuranHurwitz.PairedKernel
public import RealRooted.TuranHurwitz.PolynomialPair
import RealRooted.TuranHurwitz.MobiusFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exterior nonvanishing of the normalized Turán expressions

This is Shi's Proposition `lem:RTuran`. Formal coefficient identities connect
the recurrence with the disk coefficient lemma, including repeated roots.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

local notation "S" => complexTanhSeries

/-- The paired weight and a split polynomial give the scalar product kernel. -/
theorem weighted_polynomial_formalFlow_pair (d h : ℝ) {p : ℝ[X]} (hs : p.Splits)
    (u : ℂ) (hur : ∀ j < p.natDegree, u - (indexedRoots p j : ℂ) ≠ 0) :
    (flowWeight d h u * Polynomial.aeval (formalFlow u) p) *
        PowerSeries.rescale (-1)
          (flowWeight d h u * Polynomial.aeval (formalFlow u) p) =
      PowerSeries.C ((Polynomial.aeval u p) ^ 2) *
        scalarDiskKernel d (fun j => pairedParameter u (indexedRoots p j)) p.natDegree (u ^ 2) := by
  rw [map_mul]
  calc
    _ = (flowWeight d h u * PowerSeries.rescale (-1) (flowWeight d h u)) *
        (Polynomial.aeval (formalFlow u) p *
          PowerSeries.rescale (-1) (Polynomial.aeval (formalFlow u) p)) := by ring
    _ = _ := by
      rw [flowWeight_pair, polynomial_formalFlow_pair hs u hur]
      have hbin := binomial_subst_add (-d) (-(p.natDegree : ℝ))
        (-PowerSeries.C (u ^ 2) * S ^ 2) (by simp)
      rw [show -d + -(p.natDegree : ℝ) = -(d + p.natDegree) by ring] at hbin
      calc
        _ = PowerSeries.C ((Polynomial.aeval u p) ^ 2) *
          ((PowerSeries.binomialSeries ℝ d).subst (-(S ^ 2)) *
            ∏ j ∈ Finset.range p.natDegree,
              (1 - PowerSeries.C (pairedParameter u (indexedRoots p j)) * S ^ 2)) *
          ((PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C (u ^ 2) * S ^ 2) *
            (PowerSeries.binomialSeries ℝ (-(p.natDegree : ℝ))).subst
              (-PowerSeries.C (u ^ 2) * S ^ 2)) := by ring
        _ = _ := by rw [hbin]; simp only [scalarDiskKernel]; ring

/-- The indexed roots of a normalized row give disk parameters at every natural index. -/
theorem normalized_pairedParameter_norm_le_one {d h : ℝ} (hd : 0 < d)
    (hlo : -d ≤ h) (hhi : h ≤ d) (m : ℕ) {u : ℂ} (hu : 1 < ‖u‖) (j : ℕ) :
    ‖pairedParameter u (indexedRoots (normalized d h m) j)‖ ≤ 1 := by
  have hs := normalized_splits hd hlo hhi m
  have hr := indexedRoots_mem_Icc hs (normalized_roots_mem_Icc hd hlo hhi m) j
  exact norm_pairedRoot_le_one hu hr.1 hr.2

/-- A normalized row has no zero outside the closed unit disk. -/
theorem aeval_normalized_ne_zero {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (m : ℕ) {u : ℂ} (hu : 1 < ‖u‖) : Polynomial.aeval u (normalized d h m) ≠ 0 := by
  have hp := normalized_ne_zero hd h m
  have hr := roots_map_real_norm_le_one (normalized_splits hd hlo hhi m)
    (normalized_roots_mem_Icc hd hlo hhi m)
  intro heq
  have hroot : u ∈ ((normalized d h m).map (algebraMap ℝ ℂ)).roots := by
    apply (mem_roots (Polynomial.map_ne_zero hp)).mpr
    rw [IsRoot.def, Polynomial.eval_map_algebraMap]
    exact heq
  exact (not_le_of_gt hu) (hr u hroot)

/-- The normalized paired flow is the scalar disk kernel with the polynomial's squared value. -/
theorem normalized_flowRow_pair {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (m : ℕ) {u : ℂ} (hu : 1 < ‖u‖) :
    flowRow d h u m * PowerSeries.rescale (-1) (flowRow d h u m) =
      PowerSeries.C ((Polynomial.aeval u (normalized d h m)) ^ 2) *
        scalarDiskKernel d (fun j => pairedParameter u (indexedRoots (normalized d h m) j))
          m (u ^ 2) := by
  have hs := normalized_splits hd hlo hhi m
  have hur : ∀ j < (normalized d h m).natDegree,
      u - (indexedRoots (normalized d h m) j : ℂ) ≠ 0 := by
    intro j hj heq
    have hr := normalized_roots_mem_Icc hd hlo hhi m _ (indexedRoots_mem hs hj)
    have hnorm : ‖(indexedRoots (normalized d h m) j : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact hr
    rw [sub_eq_zero.mp heq] at hu
    exact (not_le_of_gt hu) hnorm
  have hp := weighted_polynomial_formalFlow_pair d h hs u hur
  rw [(normalized_natDegree_and_leadingCoeff_pos hd h m).1] at hp
  exact hp

/-- The exact normalized Turán kernel identity, stated with the Cauchy-product sign. -/
theorem normalized_turan_kernel {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h) (hhi : h ≤ d)
    (m n : ℕ) {u : ℂ} (hu : 1 < ‖u‖) :
    (-1 : ℂ) ^ n * Polynomial.aeval u (turan m n (normalized d h)) =
      Polynomial.aeval u (normalized d h m) ^ 2 *
        (diskCoefficient d
          (fun j => pairedParameter u (indexedRoots (normalized d h m) j)) n m).eval (u ^ 2) := by
  rw [← coeff_paired_flowRow, normalized_flowRow_pair hd hlo hhi m hu,
    PowerSeries.coeff_C_mul]
  rw [← map_aeval_diskKernel, PowerSeries.coeff_map]
  rfl

/-- Every normalized Turán expression is nonvanishing outside the closed unit disk. -/
theorem aeval_normalized_turan_ne_zero {d h : ℝ} (hd : 0 < d) (hlo : -d ≤ h)
    (hhi : h ≤ d) (m n : ℕ) {u : ℂ} (hu : 1 < ‖u‖) :
    Polynomial.aeval u (turan m n (normalized d h)) ≠ 0 := by
  have hnorm : 1 < ‖u ^ 2‖ := by rw [norm_pow]; nlinarith [norm_nonneg u]
  have hcoef := eval_diskCoefficient_ne_zero hd
    (fun j => pairedParameter u (indexedRoots (normalized d h m) j))
    (normalized_pairedParameter_norm_le_one hd hlo hhi m hu) n m hnorm
  have hrow := aeval_normalized_ne_zero hd hlo hhi m hu
  intro heq
  have hk := normalized_turan_kernel hd hlo hhi m n hu
  rw [heq, mul_zero] at hk
  exact mul_ne_zero (pow_ne_zero 2 hrow) hcoef hk.symm

end RealRooted.TuranHurwitz
