/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.RealQuadraticFactor
public import Mathlib.Algebra.Polynomial.Expand
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Tactic

/-!
# A monic even quartic factor of a parity polynomial

Appendix C.4 of `alternating_eulerian_shorter_proof.md`: substitute `X²`
in a monic quadratic divisor of the nonzero parity part.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

private theorem eq_expand_contract_of_even (q : ℝ[X])
    (hq : q.comp (-X) = q) :
    q = expand ℝ 2 (contract 2 q) := by
  ext n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [coeff_expand_mul' (by norm_num : 0 < 2), coeff_contract (by norm_num : 2 ≠ 0)]
    simp only [mul_comm]
  · have heq := congrArg (fun f : ℝ[X] => f.coeff (2 * m + 1)) hq
    rw [coeff_comp_neg_X] at heq
    have hpow : (-1 : ℝ) ^ (2 * m + 1) = -1 := by simp [pow_add, pow_mul]
    rw [hpow] at heq
    have hz : q.coeff (2 * m + 1) = 0 := by linarith
    rw [hz, coeff_expand (by norm_num : 0 < 2)]
    have hnot : ¬2 ∣ 2 * m + 1 := by lia
    simp [hnot]

private theorem eq_X_mul_expand_contract_of_odd (q : ℝ[X])
    (hq : q.comp (-X) = -q) :
    q = X * expand ℝ 2 (contract 2 q.divX) := by
  ext n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have heq := congrArg (fun f : ℝ[X] => f.coeff (2 * m)) hq
    rw [coeff_comp_neg_X, coeff_neg] at heq
    have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by simp [pow_mul]
    rw [hpow] at heq
    have hz : q.coeff (2 * m) = 0 := by linarith
    rw [hz]
    cases m with
    | zero => simp
    | succ m =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by lia, coeff_X_mul,
        coeff_expand (by norm_num : 0 < 2)]
      have hnot : ¬2 ∣ 2 * m + 1 := by lia
      simp [hnot]
  · rw [coeff_X_mul, coeff_expand_mul' (by norm_num : 0 < 2),
      coeff_contract (by norm_num : 2 ≠ 0), coeff_divX]
    simp only [mul_comm]

private theorem monic_quadratic_shape {q : ℝ[X]} (hq : q.Monic)
    (hdeg : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  have hlead : q.coeff 2 = 1 := by simpa [hdeg] using hq.coeff_natDegree
  calc
    q = ∑ i ∈ Finset.range 3, C (q.coeff i) * X ^ i := by
      simpa [hdeg] using q.as_sum_range_C_mul_X_pow
    _ = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      simp [Finset.sum_range_succ, hlead]
      ring

private theorem exists_quartic_dvd_expand (r : ℝ[X]) (hr : 2 ≤ r.natDegree) :
    ∃ k p : ℝ, (X ^ 4 + C k * X ^ 2 + C p : ℝ[X]) ∣ expand ℝ 2 r := by
  obtain ⟨q, hmonic, hdeg, hdiv⟩ := Polynomial.exists_monic_natDegree_two_dvd r hr
  let k := q.coeff 1
  let p := q.coeff 0
  have hshape : q = X ^ 2 + C k * X + C p := monic_quadratic_shape hmonic hdeg
  have hexpand : expand ℝ 2 q = X ^ 4 + C k * X ^ 2 + C p := by
    rw [hshape]
    simp only [map_add, map_mul, map_pow, expand_X, expand_C]
    ring
  obtain ⟨s, hs⟩ := hdiv
  refine ⟨k, p, expand ℝ 2 s, ?_⟩
  rw [← hexpand, hs, map_mul]

/-- Every real even or odd polynomial of degree at least four has a monic even
quartic divisor of the seed form `X⁴ + kX² + p`. -/
theorem exists_even_quartic_divisor_of_parity (q : ℝ[X])
    (hdeg : 4 ≤ q.natDegree)
    (hparity : q.comp (-X) = q ∨ q.comp (-X) = -q) :
    ∃ k p : ℝ, (X ^ 4 + C k * X ^ 2 + C p : ℝ[X]) ∣ q := by
  rcases hparity with heven | hodd
  · have hrepr := eq_expand_contract_of_even q heven
    have hhalf : 2 ≤ (contract 2 q).natDegree := by
      rw [hrepr, natDegree_expand] at hdeg
      lia
    obtain ⟨k, p, hfactor⟩ := exists_quartic_dvd_expand (contract 2 q) hhalf
    exact ⟨k, p, by rwa [hrepr]⟩
  · have hrepr := eq_X_mul_expand_contract_of_odd q hodd
    have hhalf : 2 ≤ (contract 2 q.divX).natDegree := by
      rw [hrepr] at hdeg
      have hupper := natDegree_mul_le
        (p := (X : ℝ[X])) (q := expand ℝ 2 (contract 2 q.divX))
      rw [natDegree_X, natDegree_expand] at hupper
      lia
    obtain ⟨k, p, hfactor⟩ := exists_quartic_dvd_expand (contract 2 q.divX) hhalf
    obtain ⟨s, hs⟩ := hfactor
    refine ⟨k, p, ?_⟩
    rw [hrepr, hs]
    exact ⟨X * s, by ring⟩

end RealRooted.IntervalDifferential
