module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Real.Basic

public section

open Polynomial

lemma natDegree_derivative_eq {p : ℝ[X]} (hp : 1 ≤ p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  apply le_antisymm (natDegree_derivative_le p)
  apply Polynomial.le_natDegree_of_ne_zero
  have h1 : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel hp
  rw [coeff_derivative, h1]
  have hcast : (↑(p.natDegree - 1) : ℝ) + 1 = ↑p.natDegree := by
    rw [Nat.cast_sub hp]; ring
  rw [hcast]
  exact mul_ne_zero
    (leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hp))
    (Nat.cast_ne_zero.mpr (by lia))
