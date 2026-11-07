/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineSubstitution
public import RealRooted.Mathlib.RingTheory.PowerSeries.BivariateBinomial
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Tactic

/-! Coefficients of an affine substitution into a binomial series. -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Multiplication by a fixed series commutes with coefficient extraction
from a valid formal substitution. The sum is automatically finite in every
coefficient, by the existing substitution support theorem. -/
theorem coeff_mul_subst_eq_finsum (P U F : PowerSeries R) (hU : HasSubst U) (n : ℕ) :
    coeff n (P * subst U F) =
      ∑ᶠ m : ℕ, coeff m F * coeff n (P * U ^ m) := by
  have hfin (j : ℕ) :
      (fun m => coeff m F * coeff j (U ^ m)).HasFiniteSupport := by
    simpa only [smul_eq_mul] using coeff_subst_finite' hU F j
  have hfin' (p : ℕ × ℕ) :
      (fun m => coeff p.1 P * (coeff m F * coeff p.2 (U ^ m))).HasFiniteSupport :=
    Function.HasFiniteSupport.mul_right (fun _ => coeff p.1 P) (hfin p.2)
  rw [coeff_mul]
  calc
    _ = ∑ p ∈ Finset.antidiagonal n,
        ∑ᶠ m : ℕ, coeff p.1 P * (coeff m F * coeff p.2 (U ^ m)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [coeff_subst' hU]
      simp only [smul_eq_mul]
      exact mul_finsum' _ _ (hfin p.2)
    _ = ∑ᶠ m : ℕ, ∑ p ∈ Finset.antidiagonal n,
        coeff p.1 P * (coeff m F * coeff p.2 (U ^ m)) :=
      sum_finsum_comm _ _ (fun p _ => hfin' p)
    _ = _ := by
      apply finsum_congr
      intro m
      rw [coeff_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

variable [BinomialRing R]

/-- The exact parameter-coefficient expansion of a generalized binomial
series under an affine substitution. For the negative-power application,
take `U=Q-1`, `V=-B`, and `r=-κ`. -/
theorem coeff_coeff_subst_affine_binomialSeries
    (U V : PowerSeries R) (hU : constantCoeff U = 0) (hV : constantCoeff V = 0)
    (r : R) (n k : ℕ) :
    (coeff n (subst (map Polynomial.C U + C Polynomial.X * map Polynomial.C V)
      (binomialSeries (Polynomial R) r))).coeff k =
      Ring.choose r k *
        coeff n (V ^ k * subst U (binomialSeries R (r - (k : R)))) := by
  let a : Fin 2 → PowerSeries (Polynomial R) := fun s =>
    if s = 0 then C Polynomial.X * map Polynomial.C V else map Polynomial.C U
  let x : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0 + MvPowerSeries.X 1
  have ha : MvPowerSeries.HasSubst a := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    change constantCoeff (a s) = 0
    rw [← coeff_zero_eq_constantCoeff_apply]
    fin_cases s
    · change coeff 0 (C Polynomial.X * map Polynomial.C V) = 0
      rw [coeff_C_mul, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hV, map_zero, mul_zero]
    · change coeff 0 (map Polynomial.C U) = 0
      rw [coeff_map, coeff_zero_eq_constantCoeff_apply, hU, map_zero]
  have hx : HasSubst x := HasSubst.of_constantCoeff_zero (by
    simp [x])
  have hb : HasSubst (map Polynomial.C U + C Polynomial.X * map Polynomial.C V) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff_apply]
      simp only [map_add, coeff_C_mul, coeff_map]
      simp only [coeff_zero_eq_constantCoeff_apply, hU, hV, map_zero,
        mul_zero, add_zero])
  have hbin : binomialSeries (Polynomial R) r =
      map (algebraMap R (Polynomial R)) (binomialSeries R r) := by
    ext j
    simp [binomialSeries_coeff, Algebra.smul_def]
  have hcomp : MvPowerSeries.subst a (subst x (binomialSeries R r)) =
      subst (map Polynomial.C U + C Polynomial.X * map Polynomial.C V)
        (binomialSeries (Polynomial R) r) := by
    rw [subst_def, MvPowerSeries.subst_comp_subst_apply hx.const ha]
    change subst (R := R) (MvPowerSeries.subst a x) (binomialSeries R r) = _
    have hxmap : MvPowerSeries.subst a x =
        map Polynomial.C U + C Polynomial.X * map Polynomial.C V := by
      simp only [x, MvPowerSeries.subst_add ha,
        MvPowerSeries.subst_X ha]
      simp [a, add_comm]
    rw [hxmap, hbin, subst_map_algebraMap _ hb]
  rw [← hcomp, coeff_coeff_subst_affine U V hU hV]
  have hU' : HasSubst U := HasSubst.of_constantCoeff_zero' hU
  have hrhs := coeff_mul_subst_eq_finsum
    (C (Ring.choose r k) * V ^ k) U (binomialSeries R (r - (k : R))) hU' n
  have he (m : ℕ) :
      MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m)
        (subst x (binomialSeries R r)) =
        Ring.choose r k * Ring.choose (r - (k : R)) m := by
    rw [show x = MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 from rfl,
      coeff_subst_add_binomialSeries]
    simp
  simp_rw [he]
  rw [show C (Ring.choose r k) * V ^ k *
      subst U (binomialSeries R (r - (k : R))) =
      C (Ring.choose r k) * (V ^ k *
        subst U (binomialSeries R (r - (k : R)))) by ring,
    coeff_C_mul] at hrhs
  rw [hrhs]
  apply finsum_congr
  intro m
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [show C (Ring.choose r k) * V ^ k * U ^ m =
    C (Ring.choose r k) * (V ^ k * U ^ m) by ring, coeff_C_mul]
  ring

end PowerSeries
