/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.RingTheory.PowerSeries.Log
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerLogLimit
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineNegativePower

/-! Canonical logarithmic coefficient rows and their positive-power limit. -/

public section

open Filter Topology

namespace PowerSeries

/-- The coefficient of degree `n` in `-log(Q(u)-t B(u))`, as a polynomial in `t`.
For the logarithmic interpretation, the denominator must have constant term one. -/
@[expose] noncomputable def affineLogCoeff {R : Type*} [CommRing R] [Algebra ℚ R]
    (Q B : PowerSeries R) (n : ℕ) : Polynomial R :=
  coeff n (-logOf (map Polynomial.C Q - C Polynomial.X * map Polynomial.C B))

/-- Dividing a positive-degree canonical negative-power row by its exponent
and letting that exponent decrease to zero gives the canonical logarithmic row. -/
theorem tendsto_coeff_affineNegativePowerCoeff_div
    (Q B : PowerSeries ℝ) (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0)
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    Tendsto (fun a : ℝ => (affineNegativePowerCoeff a Q B n).coeff k / a)
      (𝓝[>] 0) (𝓝 ((affineLogCoeff Q B n).coeff k)) := by
  let H := map Polynomial.C Q - C Polynomial.X * map Polynomial.C B
  have hH : constantCoeff H = 1 := constantCoeff_map_C_sub_C_X_mul_map_C hQ hB
  exact tendsto_coeff_coeff_subst_binomialSeries_neg_div H hH hn k

end PowerSeries
