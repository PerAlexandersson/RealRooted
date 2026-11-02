module

public import RealRooted.RootVieta.Newton
public import RealRooted.Interlacing.QuadraticPFPreservers

import Mathlib.Algebra.Order.Chebyshev
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex

/-!
# Newton-sum obstruction for a quadratic differential orbit

We study the orbit starting at one under
`p ↦ X * p'' + ρ X * p' + (X + γ) * p`.  Its first two signed root moments give an
explicit obstruction to splitting over the reals when `5 * ρ ^ 2 < 8`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A polynomial family is the orbit of `rhoGammaOperator` starting at one. -/
@[expose] def IsQuadraticDifferentialOrbit (P : ℕ → ℝ[X]) (ρ γ : ℝ) : Prop :=
  P 0 = 1 ∧ ∀ n, P (n + 1) = rhoGammaOperator ρ γ (P n)

/-- The first signed root moment of the rank-`n` quadratic differential orbit. -/
@[expose] def quadraticOrbitFirstMoment (ρ γ : ℝ) (n : ℕ) : ℝ :=
  n * γ + ρ * n * (n - 1) / 2

/-- The second signed root moment of the rank-`n` quadratic differential orbit. -/
@[expose] def quadraticOrbitSecondMoment (ρ γ : ℝ) (n : ℕ) : ℝ :=
  (ρ ^ 2 - 1) * n * (n - 1) * (2 * n - 1) / 3 +
    (4 * ρ * γ - ρ ^ 2 + 2) * n * (n - 1) / 2 + γ ^ 2 * n

/-- The real rank after which the second Newton-sum obstruction is negative. -/
@[expose] def quadraticOrbitObstructionRank (ρ γ : ℝ) : ℝ :=
  (16 - 7 * ρ ^ 2 + 12 * ρ * γ) / (8 - 5 * ρ ^ 2)

private lemma natDegree_X_mul_secondDerivative_le (p : ℝ[X]) :
    (X * p.derivative.derivative).natDegree ≤ p.natDegree := by
  by_cases hdeg : 2 ≤ p.natDegree
  · calc
      (X * p.derivative.derivative).natDegree ≤
          X.natDegree + p.derivative.derivative.natDegree := natDegree_mul_le
      _ ≤ 1 + (p.natDegree - 1 - 1) := by
        rw [natDegree_X]
        gcongr
        exact (natDegree_derivative_le p.derivative).trans
          (Nat.sub_le_sub_right (natDegree_derivative_le p) 1)
      _ ≤ p.natDegree := by lia
  · have hz : p.derivative.derivative = 0 := by
      simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
        (iterate_derivative_eq_zero (Nat.lt_of_not_ge hdeg) :
          derivative^[2] p = 0)
    simp [hz]

/-- Every row of a quadratic differential orbit is monic of degree its rank. -/
theorem IsQuadraticDifferentialOrbit.monic_and_natDegree_eq
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (n : ℕ) : (P n).Monic ∧ (P n).natDegree = n := by
  induction n with
  | zero => simp [hP.1]
  | succ n ih =>
      let r := X * (P n).derivative.derivative
      have hr : r.natDegree ≤ (P n).natDegree :=
        natDegree_X_mul_secondDerivative_le (P n)
      have htop :
          ((0 : ℝ) * (P n).natDegree + 1) * (P n).leadingCoeff ≠ 0 := by
        simp [ih.1.leadingCoeff]
      have hstep :=
        Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
          (P n) r ρ 0 γ 1 hr htop
      have hform :
          rhoGammaOperator ρ γ (P n) =
            (C ρ * X + C 0 * X ^ 2) * (P n).derivative +
              (C γ + C 1 * X) * P n + r := by
        simp only [rhoGammaOperator, r, map_zero, zero_mul, add_zero,
          map_one, one_mul]
        ring
      rw [hP.2 n, hform]
      constructor
      · rw [Monic, hstep.2, ih.1.leadingCoeff]
        norm_num
      · rw [hstep.1, ih.2]

private lemma coeff_rhoGammaOperator_succ (ρ γ : ℝ) (p : ℝ[X]) (k : ℕ) :
    (rhoGammaOperator ρ γ p).coeff (k + 1) =
      (ρ * (k + 1) + γ) * p.coeff (k + 1) + p.coeff k +
        (k + 1) * (k + 2) * p.coeff (k + 2) := by
  have hform :
      rhoGammaOperator ρ γ p =
        (C ρ * X + C 0 * X ^ 2) * p.derivative +
          (C γ + C 1 * X) * p + X * p.derivative.derivative := by
    simp only [rhoGammaOperator, map_zero, zero_mul, add_zero, map_one,
      one_mul]
    ring
  rw [hform, coeff_add,
    Polynomial.coeff_quadratic_derivative_add_linear_mul_succ,
    coeff_X_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

private lemma coeff_pred_eq_firstMoment {P : ℕ → ℝ[X]} {ρ γ : ℝ}
    (hP : IsQuadraticDifferentialOrbit P ρ γ) {n : ℕ} (hn : 1 ≤ n) :
    (P n).coeff (n - 1) = quadraticOrbitFirstMoment ρ γ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [hP.2 0, hP.1]
      simp [rhoGammaOperator, quadraticOrbitFirstMoment]
  | succ n hn ih =>
      have hshape := hP.monic_and_natDegree_eq n
      have htop : (P n).coeff n = 1 := by
        calc
          (P n).coeff n = (P n).coeff (P n).natDegree := by rw [hshape.2]
          _ = (P n).leadingCoeff := coeff_natDegree
          _ = 1 := hshape.1.leadingCoeff
      have habove : (P n).coeff (n + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (hshape.2.trans_lt (Nat.lt_succ_self n))
      rw [Nat.add_sub_cancel, hP.2 n, ← Nat.sub_add_cancel hn,
        coeff_rhoGammaOperator_succ, Nat.sub_add_cancel hn,
        show n - 1 + 2 = n + 1 by lia, htop, habove, ih]
      rw [quadraticOrbitFirstMoment, quadraticOrbitFirstMoment,
        Nat.cast_sub hn]
      push_cast
      ring

/-- The first Newton sum is the negative of the explicit first signed moment. -/
theorem IsQuadraticDifferentialOrbit.neg_newtonSum_one_eq
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (n : ℕ) : -newtonSum (P n) 1 = quadraticOrbitFirstMoment ρ γ n := by
  by_cases hn : n = 0
  · subst n
    rw [hP.1]
    norm_num [newtonSum, complexNewtonSum, complexRoots,
      quadraticOrbitFirstMoment, Multiset.powerSum]
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hshape := hP.monic_and_natDegree_eq n
    rw [newtonSum_one_eq_neg_nextCoeff hshape.1 (hshape.2.symm ▸ hnpos),
      neg_neg, hshape.2, coeff_pred_eq_firstMoment hP hnpos]

private lemma coeff_pred_pred_eq_moments {P : ℕ → ℝ[X]} {ρ γ : ℝ}
    (hP : IsQuadraticDifferentialOrbit P ρ γ) {n : ℕ} (hn : 2 ≤ n) :
    (P n).coeff (n - 2) =
      (quadraticOrbitFirstMoment ρ γ n ^ 2 - quadraticOrbitSecondMoment ρ γ n) / 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [hP.2 1, hP.2 0, hP.1]
      norm_num [rhoGammaOperator, quadraticOrbitFirstMoment,
        quadraticOrbitSecondMoment]
      ring
  | succ n hn ih =>
      have hshape := hP.monic_and_natDegree_eq n
      have htop : (P n).coeff n = 1 := by
        calc
          (P n).coeff n = (P n).coeff (P n).natDegree := by rw [hshape.2]
          _ = (P n).leadingCoeff := coeff_natDegree
          _ = 1 := hshape.1.leadingCoeff
      have hpred := coeff_pred_eq_firstMoment hP (by lia : 1 ≤ n)
      rw [show n + 1 - 2 = (n - 2) + 1 by lia, hP.2 n,
        coeff_rhoGammaOperator_succ,
        show n - 2 + 1 = n - 1 by lia,
        show n - 2 + 2 = n by lia, hpred, ih, htop]
      rw [quadraticOrbitFirstMoment, quadraticOrbitFirstMoment,
        quadraticOrbitSecondMoment, quadraticOrbitSecondMoment,
        Nat.cast_sub hn]
      push_cast
      ring

/-- The second Newton sum is the explicit second signed moment. -/
theorem IsQuadraticDifferentialOrbit.newtonSum_two_eq
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (n : ℕ) : newtonSum (P n) 2 = quadraticOrbitSecondMoment ρ γ n := by
  by_cases hn : 2 ≤ n
  · have hshape := hP.monic_and_natDegree_eq n
    rw [newtonSum_two_eq_sq_sub_two_mul_nextCoeff hshape.1
      (hshape.2.symm ▸ hn), hshape.2,
      coeff_pred_eq_firstMoment hP (by lia), coeff_pred_pred_eq_moments hP hn]
    ring
  · interval_cases n
    · rw [hP.1]
      norm_num [newtonSum, complexNewtonSum, complexRoots,
        quadraticOrbitSecondMoment, Multiset.powerSum]
    · rw [hP.2 0, hP.1]
      norm_num [rhoGammaOperator, newtonSum, complexNewtonSum,
        complexRoots, quadraticOrbitSecondMoment, Multiset.powerSum]
      norm_cast

/-- Cauchy--Schwarz for the first two Newton sums of a real-splitting polynomial. -/
theorem newtonSum_one_sq_le_natDegree_mul_newtonSum_two_of_splits
    {p : ℝ[X]} (hp : p.Splits) :
    newtonSum p 1 ^ 2 ≤ p.natDegree * newtonSum p 2 := by
  have h := Multiset.sq_sum_le_card_mul_sum_sq p.roots
  rw [newtonSum_eq_roots_powerSum hp, newtonSum_eq_roots_powerSum hp,
    Multiset.powerSum, Multiset.powerSum, hp.natDegree_eq_card_roots]
  simpa using h

/-- The explicit second Newton-sum obstruction for a quadratic differential orbit. -/
theorem IsQuadraticDifferentialOrbit.newtonSum_obstruction_eq
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (n : ℕ) :
    n * newtonSum (P n) 2 - newtonSum (P n) 1 ^ 2 =
      n ^ 2 * (n - 1) / 12 *
        ((5 * ρ ^ 2 - 8) * n + 16 - 7 * ρ ^ 2 + 12 * ρ * γ) := by
  have hfirst := hP.neg_newtonSum_one_eq n
  have hfirst' : newtonSum (P n) 1 = -quadraticOrbitFirstMoment ρ γ n := by
    linarith
  rw [hP.newtonSum_two_eq n, hfirst']
  simp only [quadraticOrbitFirstMoment, quadraticOrbitSecondMoment]
  ring

/-- For nonnegative parameters in the obstructed range, the real threshold is at least two. -/
theorem two_le_quadraticOrbitObstructionRank {ρ γ : ℝ}
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hsmall : 5 * ρ ^ 2 < 8) :
    2 ≤ quadraticOrbitObstructionRank ρ γ := by
  have hden : 0 < 8 - 5 * ρ ^ 2 := by linarith
  rw [quadraticOrbitObstructionRank, le_div_iff₀ hden]
  nlinarith [sq_nonneg ρ, mul_nonneg hρ hγ]

/-- Every rank strictly above the explicit obstruction threshold fails to split over `ℝ`. -/
theorem IsQuadraticDifferentialOrbit.not_splits_of_obstructionRank_lt
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hsmall : 5 * ρ ^ 2 < 8) {n : ℕ}
    (hn : quadraticOrbitObstructionRank ρ γ < n) : ¬(P n).Splits := by
  have hden : 0 < 8 - 5 * ρ ^ 2 := by linarith
  have htwo : (2 : ℝ) < n :=
    (two_le_quadraticOrbitObstructionRank hρ hγ hsmall).trans_lt hn
  have hbound :
      16 - 7 * ρ ^ 2 + 12 * ρ * γ < n * (8 - 5 * ρ ^ 2) := by
    apply (div_lt_iff₀ hden).mp
    simpa only [quadraticOrbitObstructionRank] using hn
  have hinner :
      (5 * ρ ^ 2 - 8) * n + 16 - 7 * ρ ^ 2 + 12 * ρ * γ < 0 := by
    nlinarith
  have hnpos : 0 < (n : ℝ) := by linarith
  have hnsub : 0 < (n : ℝ) - 1 := by linarith
  have hfactor : 0 < (n : ℝ) ^ 2 * (n - 1) / 12 := by positivity
  have hneg :
      n * newtonSum (P n) 2 - newtonSum (P n) 1 ^ 2 < 0 := by
    rw [hP.newtonSum_obstruction_eq n]
    exact mul_neg_of_pos_of_neg hfactor hinner
  intro hsplits
  have hnonneg := newtonSum_one_sq_le_natDegree_mul_newtonSum_two_of_splits hsplits
  rw [(hP.monic_and_natDegree_eq n).2] at hnonneg
  linarith

/-- Above the obstruction threshold, the row has a genuinely nonreal complex zero. -/
theorem IsQuadraticDifferentialOrbit.exists_nonreal_root_of_obstructionRank_lt
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hsmall : 5 * ρ ^ 2 < 8) {n : ℕ}
    (hn : quadraticOrbitObstructionRank ρ γ < n) :
    ∃ z : ℂ, ((P n).map Complex.ofRealHom).eval z = 0 ∧ z.im ≠ 0 := by
  have hnot := hP.not_splits_of_obstructionRank_lt hρ hγ hsmall hn
  have hnotall :
      ¬∀ z : ℂ, ((P n).map Complex.ofRealHom).eval z = 0 → z.im = 0 := by
    intro hall
    exact hnot (Polynomial.splits_of_all_roots_real hall)
  push Not at hnotall
  exact hnotall

/-- In the obstructed parameter range, all sufficiently large rows have a nonreal zero. -/
theorem IsQuadraticDifferentialOrbit.exists_forall_exists_nonreal_root
    {P : ℕ → ℝ[X]} {ρ γ : ℝ} (hP : IsQuadraticDifferentialOrbit P ρ γ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hsmall : 5 * ρ ^ 2 < 8) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ z : ℂ, ((P n).map Complex.ofRealHom).eval z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (quadraticOrbitObstructionRank ρ γ)
  refine ⟨N, fun n hn ↦ hP.exists_nonreal_root_of_obstructionRank_lt hρ hγ hsmall ?_⟩
  exact hN.trans_le (Nat.cast_le.mpr hn)

end RealRooted
