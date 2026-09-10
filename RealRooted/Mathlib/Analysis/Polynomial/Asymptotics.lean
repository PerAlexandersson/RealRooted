import Mathlib.Analysis.Polynomial.Basic

/-!
# Asymptotics of polynomial evaluations

This file records asymptotic consequences for polynomial evaluations along
natural arguments.
-/

open Filter

namespace Function

/-- The forward difference with its initial value retained. This is the
causal difference convention for sequences indexed by `ℕ`. -/
def causalFwdDiff {R : Type*} [Sub R] (a : ℕ → R) : ℕ → R
  | 0 => a 0
  | n + 1 => a (n + 1) - a n

end Function

namespace Polynomial

/-- The polynomial transform describing the eventual tail of a causal forward
difference. -/
noncomputable def causalFwdDiffPolynomial (p : ℝ[X]) : ℝ[X] :=
  p - p.comp (X - C 1)

@[simp]
theorem causalFwdDiffPolynomial_zero : causalFwdDiffPolynomial (0 : ℝ[X]) = 0 := by
  simp [causalFwdDiffPolynomial]

@[simp]
theorem causalFwdDiffPolynomial_C (r : ℝ) : causalFwdDiffPolynomial (C r) = 0 := by
  simp [causalFwdDiffPolynomial]

@[simp]
theorem causalFwdDiffPolynomial_iter_zero (k : ℕ) :
    (causalFwdDiffPolynomial^[k]) (0 : ℝ[X]) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih,
      causalFwdDiffPolynomial_zero]

/-- Evaluations of a nonzero real polynomial at two fixed translates of the
natural numbers have ratio tending to one. -/
theorem tendsto_eval_nat_add_div {p : ℝ[X]} (hp : p ≠ 0) (u v : ℝ) :
    Tendsto (fun n : ℕ => p.eval ((n : ℝ) + u) / p.eval ((n : ℝ) + v))
      atTop (nhds 1) := by
  have hu : 0 < (X + C u : ℝ[X]).degree := by simp
  have hv : 0 < (X + C v : ℝ[X]).degree := by simp
  have hdeg : (p.comp (X + C u)).degree = (p.comp (X + C v)).degree := by
    rw [degree_comp hu, degree_comp hv]
    simp
  have h := div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (p.comp (X + C u)) (p.comp (X + C v)) hdeg
  have hnat := h.comp tendsto_natCast_atTop_atTop
  convert hnat using 1 <;>
    simp [Function.comp_def, eval_comp, leadingCoeff_comp, hp]

/-- Evaluations of a nonzero real polynomial at two fixed natural-number
offsets below the argument have ratio tending to one. -/
theorem tendsto_eval_nat_sub_div {p : ℝ[X]} (hp : p ≠ 0) (c d : ℕ) :
    Tendsto (fun n : ℕ => p.eval ((n - c : ℕ) : ℝ) /
      p.eval ((n - d : ℕ) : ℝ)) atTop (nhds 1) := by
  apply (tendsto_eval_nat_add_div hp (-(c : ℝ)) (-(d : ℝ))).congr'
  filter_upwards [eventually_ge_atTop c, eventually_ge_atTop d] with n hcn hdn
  rw [Nat.cast_sub hcn, Nat.cast_sub hdn]
  congr 1

/-- An eventual equality with evaluations of a nonzero polynomial transports
the ratio limit at two fixed natural-number offsets. -/
theorem tendsto_nat_sub_div_of_eventually_eq_eval {a : ℕ → ℝ}
    {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) (c d : ℕ) :
    Tendsto (fun n : ℕ => a (n - c) / a (n - d)) atTop (nhds 1) := by
  apply (tendsto_eval_nat_sub_div hp c d).congr'
  filter_upwards [(tendsto_sub_atTop_nat c).eventually hap,
    (tendsto_sub_atTop_nat d).eventually hap] with n hc hd
  rw [hc, hd]

/-- A sequence which is eventually nonnegative and eventually agrees with
evaluations of a nonzero real polynomial is eventually positive. -/
theorem eventually_pos_of_eventually_nonneg_of_eventually_eq_eval_nat
    {a : ℕ → ℝ} {p : ℝ[X]} (hp : p ≠ 0)
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) :
    ∀ᶠ n in atTop, 0 < a n := by
  have hroot := tendsto_natCast_atTop_atTop.eventually
    (p.eventually_atTop_not_isRoot hp)
  filter_upwards [ha, hap, hroot] with n hnonneg han hn
  apply lt_of_le_of_ne hnonneg
  rw [han]
  exact Ne.symm (by simpa [IsRoot] using hn)

/-- Causal forward differences preserve an eventual polynomial evaluation
tail. The exceptional initial value is immaterial at `atTop`. -/
theorem eventually_eq_eval_causalFwdDiff {a : ℕ → ℝ} {p : ℝ[X]}
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) :
    ∀ᶠ n in atTop, Function.causalFwdDiff a n =
      (causalFwdDiffPolynomial p).eval (n : ℝ) := by
  filter_upwards [hap, (tendsto_sub_atTop_nat 1).eventually hap,
    eventually_gt_atTop 0] with n hn hprev hpos
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hm : a m = p.eval (m : ℝ) := by simpa using hprev
  simp [causalFwdDiffPolynomial, Function.causalFwdDiff, hn, hm, eval_sub,
    eval_comp]

/-- Iterating causal forward differences preserves an eventual polynomial
evaluation tail, while allowing arbitrary finite initial data. -/
theorem eventually_eq_eval_causalFwdDiff_iter {a : ℕ → ℝ} {p : ℝ[X]}
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) (k : ℕ) :
    ∀ᶠ n in atTop, (Function.causalFwdDiff^[k]) a n =
      ((causalFwdDiffPolynomial^[k]) p).eval (n : ℝ) := by
  induction k with
  | zero =>
    change ∀ᶠ n in atTop, a n = p.eval (n : ℝ)
    exact hap
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using
      eventually_eq_eval_causalFwdDiff ih

/-- The eventual polynomial tail of a causal forward difference has lower
degree whenever the original polynomial is nonconstant. -/
theorem natDegree_sub_comp_X_sub_C_lt {p : ℝ[X]} (hp : p.natDegree ≠ 0) :
    (causalFwdDiffPolynomial p).natDegree < p.natDegree := by
  change (p - p.comp (X - C 1)).natDegree < p.natDegree
  have hp0 : p ≠ 0 := by
    intro h
    apply hp
    simp [h]
  by_cases hq : p - p.comp (X - C 1) = 0
  · rw [hq, natDegree_zero]
    exact Nat.pos_of_ne_zero hp
  rw [natDegree_lt_natDegree_iff hq]
  apply degree_sub_lt
  · symm
    rw [degree_comp (by rw [degree_X_sub_C]; decide), degree_X_sub_C, mul_one]
  · exact hp0
  · rw [leadingCoeff_comp (by rw [natDegree_X_sub_C]; decide),
      leadingCoeff_X_sub_C, one_pow, mul_one]

/-- Iterating the polynomial causal-difference transform more often than the
natural degree produces the zero polynomial. -/
theorem causalFwdDiffPolynomial_iter_eq_zero_of_natDegree_lt (p : ℝ[X])
    {k : ℕ} (hk : p.natDegree < k) :
    (causalFwdDiffPolynomial^[k]) p = 0 := by
  induction k generalizing p with
  | zero => exact (Nat.not_lt_zero _ hk).elim
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases hp : p.natDegree = 0
    · have hpC : p = C (p.coeff 0) := by
        apply eq_C_of_degree_le_zero
        exact (natDegree_le_iff_degree_le).mp (le_of_eq hp)
      have hT : causalFwdDiffPolynomial p = 0 := by
        rw [hpC]
        exact causalFwdDiffPolynomial_C _
      rw [hT]
      exact causalFwdDiffPolynomial_iter_zero k
    · exact ih (causalFwdDiffPolynomial p)
        (lt_of_lt_of_le (natDegree_sub_comp_X_sub_C_lt hp)
          (Nat.le_of_lt_succ hk))

end Polynomial
