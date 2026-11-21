module

public import RealRooted.TuranHurwitz.WeightedReciprocals
public import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Positive-weight disk induction

The affine Euler degree lemma and the weighted reciprocal exclusion theorem
give the coefficient lemma's induction step, including constant polynomials.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The normalized positive-weight step in Shi's coefficient induction. -/
@[expose] noncomputable def diskStep (a : ℝ) (eta : ℂ) (p : ℂ[X]) : ℂ[X] :=
  C ((a : ℂ)⁻¹) * (C (a : ℂ) * p + (X - C eta) * p.derivative)

/-- A positive-weight step preserves degree and gives an explicit nonzero top coefficient. -/
theorem diskStep_natDegree_and_leadingCoeff {a : ℝ} (ha : 0 < a) (eta : ℂ)
    {p : ℂ[X]} (hp : p ≠ 0) :
    (diskStep a eta p).natDegree = p.natDegree ∧
      (diskStep a eta p).leadingCoeff =
        (1 + (p.natDegree : ℂ) / (a : ℂ)) * p.leadingCoeff := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hsum : (a : ℂ) + (p.natDegree : ℂ) ≠ 0 := by
    have hreal : a + (p.natDegree : ℝ) ≠ 0 :=
      (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)).ne'
    exact_mod_cast hreal
  have htop : ((a : ℂ) + 1 * (p.natDegree : ℂ)) * p.leadingCoeff ≠ 0 := by
    simpa only [one_mul] using mul_ne_zero hsum (leadingCoeff_ne_zero.mpr hp)
  have hstep := natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
    p (a : ℂ) (-eta) 1 htop
  have hpoly : C (a : ℂ) * p + (C (-eta) + C (1 : ℂ) * X) * p.derivative =
      C (a : ℂ) * p + (X - C eta) * p.derivative := by
    simp only [map_neg, map_one]
    ring
  rw [hpoly] at hstep
  constructor
  · rw [diskStep, natDegree_C_mul (inv_ne_zero haC), hstep.1]
  · rw [diskStep, leadingCoeff_mul, leadingCoeff_C, hstep.2]
    field_simp

/-- A positive-weight step is nonzero. -/
theorem diskStep_ne_zero {a : ℝ} (ha : 0 < a) (eta : ℂ) {p : ℂ[X]} (hp : p ≠ 0) :
    diskStep a eta p ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [(diskStep_natDegree_and_leadingCoeff ha eta hp).2]
  have hpos : 0 < 1 + (p.natDegree : ℝ) / a :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (Nat.cast_nonneg _) ha.le)
  apply mul_ne_zero _ (leadingCoeff_ne_zero.mpr hp)
  exact_mod_cast hpos.ne'

/-- A positive-weight step has no exterior zero when its seed and parameter lie in the disk. -/
theorem eval_diskStep_normalized_ne_zero {a : ℝ} (ha : 0 < a) {eta : ℂ}
    (heta : ‖eta‖ ≤ 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hr : ∀ z ∈ p.roots, ‖z‖ ≤ 1) {z : ℂ} (hz : 1 < ‖z‖) :
    (diskStep a eta p).eval z ≠ 0 := by
  rw [diskStep, eval_mul, eval_C]
  exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'))
    (eval_diskStep_ne_zero hp hr ha heta hz)

/-- Every root remains in the disk after a positive-weight step. -/
theorem diskStep_roots_norm_le_one {a : ℝ} (ha : 0 < a) {eta : ℂ}
    (heta : ‖eta‖ ≤ 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hr : ∀ z ∈ p.roots, ‖z‖ ≤ 1) :
    ∀ z ∈ (diskStep a eta p).roots, ‖z‖ ≤ 1 := by
  intro z hz
  by_contra hnorm
  exact eval_diskStep_normalized_ne_zero ha heta hp hr (lt_of_not_ge hnorm)
    ((mem_roots (diskStep_ne_zero ha eta hp)).mp hz)

end RealRooted.TuranHurwitz
