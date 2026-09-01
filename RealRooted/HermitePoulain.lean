import RealRooted.Basic
import RealRooted.Derivative
import RealRooted.Derivative.LinearCombination

/-!
# Hermite--Poulain differential operators

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainTheorem

Original references include C. Hermite, G. Polya--I. Schur, N. Obreschkoff,
and B. Ya. Levin's account of entire functions.

This module proves the finite-polynomial differential-operator theorem:
if `f` and `g` are real-rooted, then applying `f(D)` to `g` preserves
real-rootedness, allowing the result to vanish. The challenge entry point is a
thin compatibility wrapper.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace HermitePoulain

/-- The finite constant-coefficient differential operator `f(D)` applied to
`g`. -/
abbrev applyAsDifferentialOperator (f g : ℝ[X]) : ℝ[X] :=
  (Finset.range (f.natDegree + 1)).sum fun k =>
    C (f.coeff k) * ((derivative^[k]) g)

theorem applyAsDifferentialOperator_eq_sum_range {f : ℝ[X]} {N : ℕ}
    (hN : f.natDegree < N) (g : ℝ[X]) :
    applyAsDifferentialOperator f g =
      (Finset.range N).sum fun k ↦ C (f.coeff k) * ((derivative^[k]) g) := by
  dsimp [applyAsDifferentialOperator]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) ?_
  rintro k - hk
  have : f.natDegree < k := by simpa using hk
  simp [coeff_eq_zero_of_natDegree_lt this]

/-- The range for `f(D)g` can be truncated at the degree of the input `g`,
even when the symbol `f` has larger degree. -/
theorem applyAsDifferentialOperator_eq_sum_range_right (f g : ℝ[X]) :
    applyAsDifferentialOperator f g =
      (Finset.range (g.natDegree + 1)).sum fun k =>
        C (f.coeff k) * ((derivative^[k]) g) := by
  let N := max (f.natDegree + 1) (g.natDegree + 1)
  have hfN : f.natDegree < N :=
    (Nat.lt_succ_self f.natDegree).trans_le (le_max_left _ _)
  rw [applyAsDifferentialOperator_eq_sum_range hfN]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) ?_
  intro k _ hkg
  have hgk : g.natDegree < k := by simpa using hkg
  rw [Polynomial.iterate_derivative_eq_zero hgk]
  simp

/-- The top-degree coefficient of `f(D)g` comes only from the constant term
of the symbol `f`. -/
theorem coeff_applyAsDifferentialOperator_natDegree (f g : ℝ[X]) :
    (applyAsDifferentialOperator f g).coeff g.natDegree =
      f.coeff 0 * g.coeff g.natDegree := by
  rw [applyAsDifferentialOperator, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_add_of_pos_right hkpos)]
    simp
  · simp

/-- A constant-term-one differential symbol sends a monic polynomial to a
monic polynomial. -/
theorem applyAsDifferentialOperator_monic {f g : ℝ[X]}
    (hf0 : f.coeff 0 = 1) (hg : g.Monic) :
    (applyAsDifferentialOperator f g).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one g.natDegree
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_iterate_derivative g k).trans (Nat.sub_le _ _))
  · rw [coeff_applyAsDifferentialOperator_natDegree, hf0, hg.coeff_natDegree]
    norm_num

/-- A constant-term-one differential symbol preserves the degree of a monic
input. -/
theorem natDegree_applyAsDifferentialOperator {f g : ℝ[X]}
    (hf0 : f.coeff 0 = 1) (hg : g.Monic) :
    (applyAsDifferentialOperator f g).natDegree = g.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_iterate_derivative g k).trans (Nat.sub_le _ _))
  · rw [coeff_applyAsDifferentialOperator_natDegree, hf0, hg.coeff_natDegree]
    norm_num

/-- A constant-term-one differential symbol cannot annihilate a monic input. -/
theorem applyAsDifferentialOperator_ne_zero {f g : ℝ[X]}
    (hf0 : f.coeff 0 = 1) (hg : g.Monic) :
    applyAsDifferentialOperator f g ≠ 0 :=
  (applyAsDifferentialOperator_monic hf0 hg).ne_zero

@[simp] theorem applyAsDifferentialOperator_zero_right (f : ℝ[X]) :
    applyAsDifferentialOperator f 0 = 0 := by
  simp [applyAsDifferentialOperator]

theorem applyAsDifferentialOperator_C (a : ℝ) (g : ℝ[X]) :
    applyAsDifferentialOperator (C a) g = C a * g := by
  simp [applyAsDifferentialOperator]

@[simp] theorem applyAsDifferentialOperator_one (g : ℝ[X]) :
    applyAsDifferentialOperator 1 g = g := by
  simpa using applyAsDifferentialOperator_C 1 g

theorem applyAsDifferentialOperator_X_add_C (a : ℝ) (g : ℝ[X]) :
    applyAsDifferentialOperator (X + C a) g = derivative g + C a * g := by
  simp [applyAsDifferentialOperator_eq_sum_range (N := 2), Finset.sum_range_succ,
    add_comm]

theorem applyAsDifferentialOperator_add (f₁ f₂ g : ℝ[X]) :
    applyAsDifferentialOperator (f₁ + f₂) g =
      applyAsDifferentialOperator f₁ g + applyAsDifferentialOperator f₂ g := by
  let N := (f₁ + f₂).natDegree + f₁.natDegree + f₂.natDegree + 1
  have hN_sum : (f₁ + f₂).natDegree < N := by lia
  have hN_left : f₁.natDegree < N := by lia
  have hN_right : f₂.natDegree < N := by lia
  rw [applyAsDifferentialOperator_eq_sum_range (N := N) hN_sum g,
    applyAsDifferentialOperator_eq_sum_range (N := N) hN_left g,
    applyAsDifferentialOperator_eq_sum_range (N := N) hN_right g,
    ← Finset.sum_add_distrib]
  simp only [coeff_add, C_add, add_mul]

theorem applyAsDifferentialOperator_C_mul (a : ℝ) (f g : ℝ[X]) :
    applyAsDifferentialOperator (C a * f) g =
      C a * applyAsDifferentialOperator f g := by
  let N := (C a * f).natDegree + f.natDegree + 1
  have hN_mul : (C a * f).natDegree < N := by lia
  have hN_f : f.natDegree < N := by lia
  rw [applyAsDifferentialOperator_eq_sum_range (N := N) hN_mul g,
    applyAsDifferentialOperator_eq_sum_range (N := N) hN_f g, Finset.mul_sum]
  simp only [coeff_C_mul, map_mul, mul_assoc]

theorem applyAsDifferentialOperator_X_mul (f g : ℝ[X]) :
    applyAsDifferentialOperator (X * f) g =
      derivative (applyAsDifferentialOperator f g) := by
  have : (X * f).natDegree ≤ X.natDegree + f.natDegree := natDegree_mul_le
  have : (X * f).natDegree < f.natDegree + 2 := by
    rw [natDegree_X] at this
    lia
  rw [applyAsDifferentialOperator_eq_sum_range this g,
    applyAsDifferentialOperator_eq_sum_range (Nat.lt_succ_self _) g,
    Finset.sum_range_succ']
  simp only [coeff_X_mul_zero, coeff_X_mul, C_0, zero_mul, add_zero, map_sum,
    derivative_C_mul, ← Function.iterate_succ_apply' derivative]

theorem applyAsDifferentialOperator_monomial (n : ℕ) (c : ℝ) (g : ℝ[X]) :
    applyAsDifferentialOperator (monomial n c) g =
      C c * (derivative^[n]) g := by
  induction n generalizing g with
  | zero =>
    exact applyAsDifferentialOperator_C c g
  | succ n ih =>
    rw [← X_mul_monomial, applyAsDifferentialOperator_X_mul, ih,
      derivative_C_mul, Function.iterate_succ_apply']

theorem applyAsDifferentialOperator_X_pow_mul (n : ℕ) (f g : ℝ[X]) :
    applyAsDifferentialOperator (X ^ n * f) g =
      (derivative^[n]) (applyAsDifferentialOperator f g) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, applyAsDifferentialOperator_X_mul, ih,
      Function.iterate_succ_apply']

theorem applyAsDifferentialOperator_mul (x y g : ℝ[X]) :
    applyAsDifferentialOperator (x * y) g =
      applyAsDifferentialOperator x (applyAsDifferentialOperator y g) := by
  induction x using Polynomial.induction_on' with
  | add x₁ x₂ ih₁ ih₂ =>
    rw [add_mul, applyAsDifferentialOperator_add, applyAsDifferentialOperator_add,
      ih₁, ih₂]
  | monomial n c =>
    rw [applyAsDifferentialOperator_monomial, ← C_mul_X_pow_eq_monomial,
      mul_assoc, applyAsDifferentialOperator_C_mul,
      applyAsDifferentialOperator_X_pow_mul]

theorem applyAsDifferentialOperator_C_eq_zero_or_splits {a : ℝ} {g : ℝ[X]}
    (hg : g.Splits) :
    applyAsDifferentialOperator (C a) g = 0 ∨
      (applyAsDifferentialOperator (C a) g).Splits := by
  simp [applyAsDifferentialOperator_C, hg]

theorem applyAsDifferentialOperator_X_add_C_eq_zero_or_splits {a : ℝ} {g : ℝ[X]}
    (hg : g.Splits) :
    applyAsDifferentialOperator (X + C a) g = 0 ∨
      (applyAsDifferentialOperator (X + C a) g).Splits := by
  rw [applyAsDifferentialOperator_X_add_C, add_comm]
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using eq_zero_or_splits_derivative (.inr hg)
  · exact .inr (splits_C_mul_add_derivative hg ha)

/-- Hermite--Poulain theorem target, zero-aware because a differential operator
can annihilate a lower-degree polynomial. -/
theorem differential_operator_preserves_real_rooted {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    applyAsDifferentialOperator f g = 0 ∨
      (applyAsDifferentialOperator f g).Splits := by
  have (p : ℝ[X]) (hp : p.Splits) : ∀ ⦃q : ℝ[X]⦄, q.Splits →
      applyAsDifferentialOperator p q = 0 ∨ (applyAsDifferentialOperator p q).Splits := by
    induction hp using Submonoid.closure_induction with
    | mem x hx =>
      intro q hq
      rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact applyAsDifferentialOperator_C_eq_zero_or_splits hq
      · exact applyAsDifferentialOperator_X_add_C_eq_zero_or_splits hq
    | one =>
      intro q hq
      simp [hq]
    | mul x y _ _ ihx ihy =>
      intro q hq
      rw [applyAsDifferentialOperator_mul]
      rcases ihy hq with hy | hy
      · simp [hy]
      · exact ihx hy
  exact this f hf.2 hg.2

/-- Compatibility wrapper for the original challenge-facing theorem name. -/
theorem differentialOperator_preserves_realRooted {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    applyAsDifferentialOperator f g = 0 ∨
      (applyAsDifferentialOperator f g).Splits :=
  differential_operator_preserves_real_rooted hf hg

end HermitePoulain
end RealRooted
