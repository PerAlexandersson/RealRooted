module

public import RealRooted.TuranHurwitz.DiskKernel
public import RealRooted.TuranHurwitz.FormalParity
import Mathlib.Tactic.Ring

/-!
# Scalar evaluation of the paired kernel

The factors with opposite formal times combine by multiplicativity of normalized
binomial powers. The resulting scalar kernel is evaluation of the polynomial kernel.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

local notation "S" => complexTanhSeries

/-- The square of tanh is compatible with complex scalar extension. -/
theorem complexTanhSquare_eq_map : complexTanhSquare = (S ^ 2).map Polynomial.C := by
  rw [complexTanhSeries, ← map_pow]
  apply PowerSeries.ext
  intro n
  simp only [complexTanhSquare, tanhSquarePolynomialSeries,
    PowerSeries.coeff_map]
  change (C (PowerSeries.coeff n (tanhSeries ^ 2))).map (algebraMap ℝ ℂ) =
    C ((algebraMap ℝ ℂ) (PowerSeries.coeff n (tanhSeries ^ 2)))
  exact Polynomial.map_C _

/-- Evaluating the coefficient-polynomial parameter leaves the scalar tanh square. -/
theorem map_aeval_complexTanhSquare (z : ℂ) :
    complexTanhSquare.map (Polynomial.aeval z).toRingHom = S ^ 2 := by
  rw [complexTanhSquare_eq_map]
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map]
  change Polynomial.aeval z (C _) = _
  simp

/-- The kernel after evaluating its polynomial parameter. -/
@[expose] noncomputable def scalarDiskKernel (d : ℝ) (eta : ℕ → ℂ) (ell : ℕ)
    (z : ℂ) : PowerSeries ℂ :=
  (PowerSeries.binomialSeries ℝ d).subst (-(S ^ 2)) *
    (∏ j ∈ Finset.range ell, (1 - PowerSeries.C (eta j) * S ^ 2)) *
      (PowerSeries.binomialSeries ℝ (-(d + ell))).subst (-PowerSeries.C z * S ^ 2)

/-- Evaluation in the polynomial parameter agrees with the scalar kernel formula. -/
theorem map_aeval_diskKernel (d : ℝ) (eta : ℕ → ℂ) (ell : ℕ) (z : ℂ) :
    (diskKernel d eta ell).map (Polynomial.aeval z).toRingHom =
      scalarDiskKernel d eta ell z := by
  let φ : ℂ[X] →ₐ[ℝ] ℂ := (Polynomial.aeval z).restrictScalars ℝ
  have hX : (Polynomial.aeval z).toRingHom (X : ℂ[X]) = z := by
    exact Polynomial.aeval_X _
  have hC (r : ℂ) : (Polynomial.aeval z).toRingHom (C r) = r := by
    change Polynomial.aeval z (C r) = r
    simp
  have hmap (r : ℝ) (g : PowerSeries ℂ[X]) (hg : PowerSeries.constantCoeff g = 0) :
      PowerSeries.map (Polynomial.aeval z).toRingHom
          ((PowerSeries.binomialSeries ℝ r).subst g) =
        (PowerSeries.binomialSeries ℝ r).subst (g.map (Polynomial.aeval z).toRingHom) := by
    exact map_subst_algebraHom φ _ _ (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  rw [diskKernel, diskNumerator_eq_prod, tanhDenominator, map_mul, map_mul]
  rw [hmap _ _ (by simp), hmap _ _ (by simp)]
  simp only [scalarDiskKernel, map_neg, map_mul, map_prod, map_sub, map_one,
    PowerSeries.map_C, map_aeval_complexTanhSquare, hX, hC]

/-- Pairing opposite formal times removes the offset parameter from the weight. -/
theorem flowWeight_pair (d h : ℝ) (u : ℂ) :
    flowWeight d h u * PowerSeries.rescale (-1) (flowWeight d h u) =
      (PowerSeries.binomialSeries ℝ d).subst (-(S ^ 2)) *
        (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C (u ^ 2) * S ^ 2) := by
  rw [rescale_neg_flowWeight, flowWeight]
  have ha := binomial_subst_add ((d + h) / 2) ((d - h) / 2) S (by simp)
  have hb := binomial_subst_add ((d - h) / 2) ((d + h) / 2) (-S) (by simp)
  rw [show (d + h) / 2 + (d - h) / 2 = d by ring] at ha
  rw [show (d - h) / 2 + (d + h) / 2 = d by ring] at hb
  have hc := binomial_subst_mul d S (-S) (by simp) (by simp)
  rw [show S + -S + S * -S = -(S ^ 2) by ring] at hc
  have hd := binomial_subst_mul (-d) (-PowerSeries.C u * S) (PowerSeries.C u * S)
    (by simp) (by simp)
  rw [show -PowerSeries.C u * S + PowerSeries.C u * S +
      (-PowerSeries.C u * S) * (PowerSeries.C u * S) =
      -PowerSeries.C (u ^ 2) * S ^ 2 by rw [map_pow]; ring] at hd
  calc
    _ = ((PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst S *
        (PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst S) *
      ((PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst (-S) *
        (PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst (-S)) *
      ((PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S) *
        (PowerSeries.binomialSeries ℝ (-d)).subst (PowerSeries.C u * S)) := by ring
    _ = _ := by rw [ha, hb, hc, hd]

end RealRooted.TuranHurwitz
