/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialAffineExpansion
import Mathlib.Tactic

/-! Exact parameter coefficients of formal negative powers. -/

public section

namespace PowerSeries

/-- A binomial series with scalar exponent agrees with the version whose
exponent is mapped into its coefficient algebra. -/
theorem binomialSeries_algebraMap {R A : Type*} [CommRing R] [CommRing A]
    [BinomialRing R] [BinomialRing A] [Algebra R A] (r : R) :
    binomialSeries A (algebraMap R A r) = binomialSeries A r := by
  ext n
  simp only [binomialSeries_coeff, Algebra.smul_def, Algebra.algebraMap_self,
    RingHom.id_apply, mul_one]
  exact (Ring.map_choose (algebraMap R A) r n).symm

/-- The exact parameter coefficient of the canonical negative power of
`Q-tB`. Its scalar factor is the rising factorial divided by the factorial,
expressed as `Ring.multichoose`. This is expansion (2.1). -/
theorem coeff_coeff_subst_binomialSeries_neg
    (Q B : PowerSeries ℝ) (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0)
    (κ : ℝ) (n k : ℕ) :
    (coeff n (subst
      (map Polynomial.C Q - C Polynomial.X * map Polynomial.C B - 1)
      (binomialSeries (Polynomial ℝ) (-Polynomial.C κ)))).coeff k =
      Ring.multichoose κ k * coeff n
        (B ^ k * subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ)))) := by
  have hU : constantCoeff (Q - 1) = 0 := by simp [hQ]
  have hV : constantCoeff (-B) = 0 := by simp [hB]
  have h := coeff_coeff_subst_affine_binomialSeries (Q - 1) (-B) hU hV (-κ) n k
  have harg : map Polynomial.C (Q - 1) + C Polynomial.X * map Polynomial.C (-B) =
      map Polynomial.C Q - C Polynomial.X * map Polynomial.C B - 1 := by
    simp only [map_sub, map_one, map_neg]
    ring
  have hbin : binomialSeries (Polynomial ℝ) (-Polynomial.C κ) =
      binomialSeries (Polynomial ℝ) (-κ) := by
    simpa only [Polynomial.algebraMap_eq, map_neg] using
      binomialSeries_algebraMap (A := Polynomial ℝ) (-κ)
  rw [hbin, ← harg, h]
  have hpow : (-B) ^ k = C ((-1 : ℝ) ^ k) * B ^ k := by
    rw [neg_pow, map_pow, map_neg, map_one]
  calc
    _ = ((-1 : ℝ) ^ k * Ring.choose (-κ) k) *
        coeff n (B ^ k * subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ)))) := by
      rw [hpow, show C ((-1 : ℝ) ^ k) * B ^ k *
          subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ))) =
          C ((-1 : ℝ) ^ k) *
            (B ^ k * subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ)))) by ring,
        coeff_C_mul]
      ring
    _ = _ := by rw [Ring.neg_one_pow_mul_choose_neg]

end PowerSeries
