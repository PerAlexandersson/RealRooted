/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-! Canonical formal negative powers from binomial-series substitution. -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- Formal differentiation lowers a binomial exponent by one. -/
theorem derivative_binomialSeries (r : R) :
    derivative (binomialSeries R r) = C r * binomialSeries R (r - 1) := by
  ext n
  have h := Ring.choose_smul_choose r (n := n + 1) (k := 1) (by lia)
  simpa [coeff_derivative, coeff_C_mul, binomialSeries_coeff,
    Ring.choose_one_right, nsmul_eq_mul, smul_eq_mul, mul_comm] using h

/-- The binomial series solves its first-order formal differential
equation over any commutative binomial ring. -/
theorem one_add_X_mul_derivative_binomialSeries (r : R) :
    (1 + X) * derivative (binomialSeries R r) = C r * binomialSeries R r := by
  have hadd : (1 + X) * binomialSeries R (r - 1) = binomialSeries R r := by
    calc
      _ = binomialSeries R (1 : R) * binomialSeries R (r - 1) := by
        rw [show (1 : R) = (1 : ℕ) by simp, binomialSeries_nat]
        simp
      _ = binomialSeries R (1 + (r - 1)) := (binomialSeries_add 1 (r - 1)).symm
      _ = _ := by congr 1; ring
  rw [derivative_binomialSeries]
  calc
    _ = C r * ((1 + X) * binomialSeries R (r - 1)) := by ring
    _ = _ := by rw [hadd]

/-- Substituting `H-1` into the negative binomial series gives a solution
of the formal negative-power differential equation. -/
theorem subst_binomialSeries_neg_ode (κ : R) (H : PowerSeries R)
    (hH : constantCoeff H = 1) :
    H * derivative (subst (H - 1) (binomialSeries R (-κ))) +
      C κ * derivative H * subst (H - 1) (binomialSeries R (-κ)) = 0 := by
  let g : PowerSeries R := H - 1
  have hg : HasSubst g := HasSubst.of_constantCoeff_zero' (by simp [g, hH])
  have hgd : derivative g = derivative H := by simp [g]
  have hmapX : substAlgHom (R := R) hg X = g := substAlgHom_X hg
  have hmapC : substAlgHom (R := R) hg (C (-κ)) = C (-κ) := by
    rw [coe_substAlgHom, subst_C]
    rfl
  have hmapH : substAlgHom (R := R) hg (1 + X) = H := by
    rw [map_add, map_one, hmapX]
    dsimp [g]
    ring
  have heq := congrArg (substAlgHom (R := R) hg)
    (one_add_X_mul_derivative_binomialSeries (-κ))
  rw [map_mul, map_mul, hmapH, hmapC] at heq
  simp only [coe_substAlgHom] at heq
  change H * derivative (subst g (binomialSeries R (-κ))) +
    C κ * derivative H * subst g (binomialSeries R (-κ)) = 0
  rw [derivative_subst hg, hgd]
  calc
    _ = (H * subst g (derivative (binomialSeries R (-κ)))) * derivative H +
        C κ * derivative H * subst g (binomialSeries R (-κ)) := by ring
    _ = 0 := by rw [heq]; simp only [map_neg]; ring

/-- The normalized negative binomial substitution has constant term one. -/
theorem constantCoeff_subst_binomialSeries_neg (κ : R) (H : PowerSeries R)
    (hH : constantCoeff H = 1) :
    constantCoeff (subst (H - 1) (binomialSeries R (-κ))) = 1 := by
  have h := constantCoeff_subst_of_constantCoeff_zero
    (show (H - 1).constantCoeff = 0 by simp [hH]) (binomialSeries R (-κ))
  simpa only [← constantCoeff_eq, binomialSeries_constantCoeff, map_one] using h

end PowerSeries
