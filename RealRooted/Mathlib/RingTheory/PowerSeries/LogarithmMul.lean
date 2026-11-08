/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic

/-! # Additivity of the formal logarithm on normalized products -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The formal logarithm of a normalized series satisfies its logarithmic
derivative identity without choosing an inverse. -/
theorem mul_derivative_logOf (H : PowerSeries R) (hH : constantCoeff H = 1) :
    H * derivative (logOf H) = derivative H := by
  let G := H - 1
  have hg : HasSubst G := HasSubst.of_constantCoeff_zero' (by simp [G, hH])
  have hX : substAlgHom (R := R) hg (1 + X) = H := by
    rw [map_add, map_one, substAlgHom_X hg]
    dsimp [G]
    ring
  have heq := congrArg (substAlgHom (R := R) hg)
    (derivative_log_mul_one_add_X (A := R))
  rw [map_mul, hX, map_one] at heq
  simp only [coe_substAlgHom] at heq
  change H * derivative (subst G (log R)) = derivative H
  rw [derivative_subst hg]
  have hgd : derivative G = derivative H := by simp [G]
  rw [hgd]
  calc
    _ = (subst G (derivative (log R)) * H) * derivative H := by ring
    _ = derivative H := by rw [heq, one_mul]

/-- The formal logarithm is additive on products of normalized series. -/
theorem logOf_mul [HasUniqueDiv R] (H K : PowerSeries R)
    (hH : constantCoeff H = 1) (hK : constantCoeff K = 1) :
    logOf (H * K) = logOf H + logOf K := by
  have hHK : constantCoeff (H * K) = 1 := by simp [hH, hK]
  apply derivative.ext
  · apply (isUnit_iff_constantCoeff.mpr (show IsUnit (constantCoeff (H * K)) by
      rw [hHK]; exact isUnit_one)).mul_left_cancel
    rw [mul_derivative_logOf (H * K) hHK, map_add, mul_add]
    calc
      derivative (H * K) = K * (H * derivative (logOf H)) +
          H * (K * derivative (logOf K)) := by
        rw [mul_derivative_logOf H hH, mul_derivative_logOf K hK,
          derivative.leibniz]
        ring
      _ = _ := by ring
  · rw [constantCoeff_logOf hHK, map_add,
      constantCoeff_logOf hH, constantCoeff_logOf hK, add_zero]

/-- The formal logarithm turns a finite product of normalized series into
the sum of their formal logarithms. -/
theorem logOf_prod [HasUniqueDiv R] {ι : Type*} (s : Finset ι)
    (H : ι → PowerSeries R) (hH : ∀ i ∈ s, constantCoeff (H i) = 1) :
    logOf (∏ i ∈ s, H i) = ∑ i ∈ s, logOf (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logOf_eq]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, logOf_mul _ _ (hH i (by simp)) (by
      simp only [map_prod]
      apply Finset.prod_eq_one
      intro j hj
      exact hH j (Finset.mem_insert_of_mem hj)), Finset.sum_insert hi]
    rw [ih (fun j hj ↦ hH j (Finset.mem_insert_of_mem hj))]

/-- Ring maps between rational algebras preserve the formal logarithm of a
normalized series. -/
theorem map_logOf {S : Type*} [CommRing S] [Algebra ℚ S] (φ : R →+* S)
    (H : PowerSeries R) (hH : constantCoeff H = 1) :
    map φ (logOf H) = logOf (map φ H) := by
  have hG : HasSubst (H - 1) := HasSubst.of_constantCoeff_zero' (by simp [hH])
  rw [logOf_eq, logOf_eq]
  have hm := map_subst hG (h := φ) (log R)
  change map φ (subst (H - 1) (log R)) =
    subst (map φ (H - 1)) (map φ (log R)) at hm
  rw [hm, map_log, map_sub, map_one]

end PowerSeries
