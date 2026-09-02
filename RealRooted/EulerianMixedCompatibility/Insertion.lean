import RealRooted.Compatibility.Pair
import RealRooted.MaWang.Weak.Endpoint

/-!
# Euler insertion operator

This module owns the reusable algebra, coefficient shape, degree control, and
proper-position API for

`E(c, d) p = (c + (d + 1) X) p + (X - X^2) p'`.

The adjacent mixed-step argument lives in `EulerianMixedCompatibility`; users
that need only the insertion operator should import this module directly.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Euler insertion operator with constant boundary weight `c` and degree
bound `d`. -/
def eulerInsertionStep (c : ℝ) (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C c * p + C ((d : ℝ) + 1) * (X * p) +
    X * p.derivative - X * (X * p.derivative)

theorem eulerInsertionStep_eq (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d p =
      (C c + C ((d : ℝ) + 1) * X) * p +
        (X - X ^ 2) * p.derivative := by
  simp [eulerInsertionStep]
  ring

@[simp] theorem eulerInsertionStep_zero (c : ℝ) (d : ℕ) :
    eulerInsertionStep c d 0 = 0 := by
  simp [eulerInsertionStep]

@[simp] theorem coeff_eulerInsertionStep_zero (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).coeff 0 = c * p.coeff 0 := by
  simp [eulerInsertionStep]

@[simp] theorem coeff_eulerInsertionStep_succ
    (c : ℝ) (d k : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).coeff (k + 1) =
      (c + (k : ℝ) + 1) * p.coeff (k + 1) +
        ((d : ℝ) + 1 - k) * p.coeff k := by
  cases k with
  | zero =>
      simp only [eulerInsertionStep, coeff_sub, coeff_add, coeff_C_mul]
      simp [coeff_X_mul, coeff_derivative]
      ring
  | succ k =>
      simp only [eulerInsertionStep, coeff_sub, coeff_add, coeff_C_mul]
      simp [coeff_X_mul, coeff_derivative]
      ring

theorem eulerInsertionStep_add (c : ℝ) (d : ℕ) (p q : ℝ[X]) :
    eulerInsertionStep c d (p + q) =
      eulerInsertionStep c d p + eulerInsertionStep c d q := by
  simp [eulerInsertionStep, derivative_add]
  ring

theorem eulerInsertionStep_C_mul (c a : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d (C a * p) = C a * eulerInsertionStep c d p := by
  simp [eulerInsertionStep, derivative_mul]
  ring

/-- The Euler insertion step bundled as a real-linear map. -/
def eulerInsertionLinearMap (c : ℝ) (d : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := eulerInsertionStep c d
  map_add' := eulerInsertionStep_add c d
  map_smul' a p := by
    simp only [smul_eq_C_mul]
    exact eulerInsertionStep_C_mul c a d p

@[simp] theorem eulerInsertionLinearMap_apply (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionLinearMap c d p = eulerInsertionStep c d p := rfl

theorem natDegree_eulerInsertionStep_le (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).natDegree ≤ p.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  cases k with
  | zero => lia
  | succ k =>
      rw [coeff_eulerInsertionStep_succ]
      have hpk : p.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      have hpks : p.coeff (k + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      simp [hpk, hpks]

/-- Under the intended degree bound, an Euler insertion step raises degree by
one and retains a positive leading coefficient. -/
theorem eulerInsertionStep_degree_pos
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp_pos : HasPosLeadingCoeff p) :
    (eulerInsertionStep c d p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (eulerInsertionStep c d p) := by
  have hfactor : 0 < (d : ℝ) + 1 - p.natDegree := by
    have hcast : (p.natDegree : ℝ) ≤ d := Nat.cast_le.mpr hpdeg
    linarith
  have hcoeff :
      0 < (eulerInsertionStep c d p).coeff (p.natDegree + 1) := by
    rw [coeff_eulerInsertionStep_succ]
    rw [coeff_eq_zero_of_natDegree_lt (by lia)]
    simp only [mul_zero, zero_add]
    change 0 < ((d : ℝ) + 1 - p.natDegree) * p.leadingCoeff
    exact mul_pos hfactor hp_pos
  have hdeg : (eulerInsertionStep c d p).natDegree = p.natDegree + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_eulerInsertionStep_le c d p) hcoeff.ne'
  refine ⟨hdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdeg]
  exact hcoeff

/-- Nonnegative boundary and coefficient weights preserve coefficient
nonnegativity up to the declared degree bound. -/
theorem HasNonnegCoeffs.eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hc : 0 ≤ c) (hpdeg : p.natDegree ≤ d) :
    HasNonnegCoeffs (eulerInsertionStep c d p) := by
  intro k
  cases k with
  | zero =>
      rw [coeff_eulerInsertionStep_zero]
      exact mul_nonneg hc (hp 0)
  | succ k =>
      rw [coeff_eulerInsertionStep_succ]
      by_cases hk : k ≤ d
      · have hweight : 0 ≤ (d : ℝ) + 1 - k := by
          have hcast : (k : ℝ) ≤ d := Nat.cast_le.mpr hk
          linarith
        exact add_nonneg
          (mul_nonneg (by positivity) (hp (k + 1)))
          (mul_nonneg hweight (hp k))
      · have hdk : d < k := Nat.lt_of_not_ge hk
        have hpk : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hdk)
        have hpks : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by lia))
        simp [hpk, hpks]

/-- An Euler insertion step lies immediately to the right of its input in
proper position. The proof includes the degree-zero boundary case. -/
theorem prec_eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hp_pos : HasPosLeadingCoeff p)
    (hp_splits : p.Splits) (hpdeg : p.natDegree ≤ d) :
    Prec p (eulerInsertionStep c d p) := by
  obtain ⟨hout_deg, hout_pos⟩ :=
    eulerInsertionStep_degree_pos (c := c) hpdeg hp_pos
  by_cases hpdeg0 : p.natDegree = 0
  · have hout_deg1 : (eulerInsertionStep c d p).natDegree = 1 := by lia
    exact prec_degree_zero_right_of_degree_one
      hp_pos.ne_zero hp_splits hout_pos.ne_zero
      (Polynomial.Splits.of_natDegree_le_one (by lia)) hpdeg0 hout_deg1
  · have hpdeg_pos : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hpdeg0
    have hder : Interlaces p.derivative p :=
      interlaces_derivative_of_pos_natDegree
        hp_pos.ne_zero hp_splits hp_pos hpdeg_pos
    have hder_pos : HasPosLeadingCoeff p.derivative :=
      hp_pos.derivative hpdeg0
    rw [eulerInsertionStep_eq]
    refine prec_of_interlaces_evalCoeff_nonpos
      hder hder_pos ?_ ?_ ?_ ?_
    · rw [← eulerInsertionStep_eq]
      exact hout_pos
    · rw [← eulerInsertionStep_eq, hout_deg]
      lia
    · rw [← eulerInsertionStep_eq, hout_deg]
    · intro r hr
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_hasNonnegCoeffs hp r
          ((mem_roots hp_pos.ne_zero).mpr hr)
      simp only [eval_sub, eval_X, eval_pow]
      nlinarith [sq_nonneg r]

theorem splits_eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hp_pos : HasPosLeadingCoeff p)
    (hp_splits : p.Splits) (hpdeg : p.natDegree ≤ d) :
    (eulerInsertionStep c d p).Splits :=
  (prec_eulerInsertionStep hp hp_pos hp_splits hpdeg).2.1.2

/-- Applying one fixed Euler insertion step to both members of a compatible
nonnegative pair in the degree box preserves compatibility. -/
theorem Compatible.map_eulerInsertionStep
    {c : ℝ} {d : ℕ} {f g : ℝ[X]}
    (hfg : Compatible f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ d) (hgdeg : g.natDegree ≤ d) :
    Compatible (eulerInsertionStep c d f) (eulerInsertionStep c d g) := by
  apply hfg.map_linearMap_of_nonneg (eulerInsertionLinearMap c d)
    hf hg hfdeg hgdeg
  intro p hp hpdeg hp_rr
  have hp_pos : HasPosLeadingCoeff p := hp.pos_leadingCoeff hp_rr.1
  exact ⟨(eulerInsertionStep_degree_pos hpdeg hp_pos).2.ne_zero,
    splits_eulerInsertionStep hp hp_pos hp_rr.2 hpdeg⟩

end RealRooted
