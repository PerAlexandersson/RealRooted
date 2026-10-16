/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Polynomial.Factorization
public import Mathlib.Tactic

/-!
# A real quadratic divisor of every polynomial of degree at least two

This is the nonmonic corollary of Mathlib's
`Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree`.
-/

public noncomputable section

namespace Polynomial

/-- Every real polynomial of degree at least two has a monic quadratic divisor. -/
theorem exists_monic_natDegree_two_dvd (p : ℝ[X]) (hp : 2 ≤ p.natDegree) :
    ∃ q : ℝ[X], q.Monic ∧ q.natDegree = 2 ∧ q ∣ p := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hmonic : IsMonicOfDegree (normalize p) (p.natDegree - 2 + 2) := by
    refine ⟨?_, monic_normalize hp0⟩
    simp only [natDegree_normalize]
    lia
  obtain ⟨q, r, hq, _, hfactor⟩ :=
    hmonic.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  refine ⟨q, hq.monic, hq.natDegree_eq, ?_⟩
  apply dvd_normalize_iff.mp
  exact ⟨r, hfactor⟩

/-- The coefficient form of a real monic quadratic. -/
theorem Monic.eq_X_sq_add_C_mul_X_add_C {q : ℝ[X]} (hq : q.Monic)
    (hdeg : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  have hlead : q.coeff 2 = 1 := by simpa [hdeg] using hq.coeff_natDegree
  calc
    q = ∑ i ∈ Finset.range 3, C (q.coeff i) * X ^ i := by
      simpa [hdeg] using q.as_sum_range_C_mul_X_pow
    _ = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      simp [Finset.sum_range_succ, hlead]
      ring

/-- A real monic quadratic splits into two real linear factors or a
conjugate-pair factor with positive imaginary parameter. -/
theorem Monic.eq_mul_X_sub_C_or_sq_add_C_sq {q : ℝ[X]} (hq : q.Monic)
    (hdeg : q.natDegree = 2) :
    (∃ a t : ℝ, q = (X - C a) * (X - C t)) ∨
      (∃ a b : ℝ, 0 < b ∧ q = (X - C a) ^ 2 + C (b ^ 2)) := by
  let k := q.coeff 1
  let p := q.coeff 0
  have hshape : q = X ^ 2 + C k * X + C p := Monic.eq_X_sq_add_C_mul_X_add_C hq hdeg
  by_cases hdisc : 0 ≤ k ^ 2 - 4 * p
  · let s := Real.sqrt (k ^ 2 - 4 * p)
    have hs : s ^ 2 = k ^ 2 - 4 * p := Real.sq_sqrt hdisc
    let a := (-k + s) / 2
    let t := (-k - s) / 2
    have hsum : a + t = -k := by dsimp [a, t]; ring
    have hprod : a * t = p := by dsimp [a, t]; nlinarith [hs]
    left
    refine ⟨a, t, ?_⟩
    have hk : k = -(a + t) := by linarith
    calc
      q = X ^ 2 + C k * X + C p := hshape
      _ = (X - C a) * (X - C t) := by
        rw [hk, ← hprod]
        simp only [map_neg, map_add, map_mul]
        ring
  · have hdisc' : 0 < 4 * p - k ^ 2 := by linarith
    let s := Real.sqrt (4 * p - k ^ 2)
    have hs : s ^ 2 = 4 * p - k ^ 2 := Real.sq_sqrt hdisc'.le
    have hspos : 0 < s := Real.sqrt_pos.2 hdisc'
    let a := -k / 2
    let b := s / 2
    have hb : 0 < b := by dsimp [b]; positivity
    have hsum : p = a ^ 2 + b ^ 2 := by dsimp [a, b]; nlinarith [hs]
    have hk : k = -(2 * a) := by dsimp [a]; ring
    right
    refine ⟨a, b, hb, ?_⟩
    calc
      q = X ^ 2 + C k * X + C p := hshape
      _ = (X - C a) ^ 2 + C (b ^ 2) := by
        rw [hk, hsum]
        simp only [map_neg, map_add, map_mul, map_pow, map_ofNat]
        ring

end Polynomial
