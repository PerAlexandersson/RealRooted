import Mathlib
import RealRooted.OperatorPreservesInterlacing
import RealRooted.Derivative.FamilyClosure
import RealRooted.Basic.Coefficients
import RealRooted.Recurrence.RowModel

/-!
# OEIS A151775

The row polynomials of [OEIS A151775](https://oeis.org/A151775) form an
autonomous orbit under a factored differential operator.  The factorization
proves that every real combination of two consecutive rows splits, and hence
that consecutive rows strictly interlace by Obreschkoff's theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A151775

private def splitFactorDerivative (a : ℝ[X]) (m : ℕ) (f : ℝ[X]) : ℝ[X] :=
  derivative a * f + C (m : ℝ) * a * derivative f

/-- `lowerStep = D_{1+X, 2}`: `lowerStep f = f + 2 (1+X) f'`. -/
private def lowerStep (f : ℝ[X]) : ℝ[X] := f + 2 * (1 + X) * derivative f

/-- `upperStep = D_{X(1+X), 2}`: `upperStep f = (1+2X) f + 2 X (1+X) f'`. -/
private def upperStep (f : ℝ[X]) : ℝ[X] :=
  (1 + 2 * X) * f + 2 * X * (1 + X) * derivative f

/-- The A151775 step `step = upperStep ∘ lowerStep`. -/
private def step (f : ℝ[X]) : ℝ[X] := upperStep (lowerStep f)

/-- The row polynomial of [OEIS A151775](https://oeis.org/A151775), defined by
`P₀ = 1` and the factored differential recurrence `Pₙ₊₁ = upperStep (lowerStep Pₙ)`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => step (polynomial n)

/-- `step f = 4X(1+X)² f'' + 2(1+X)(1+5X) f' + (1+2X) f`. -/
private theorem step_eq (f : ℝ[X]) :
    step f = 4 * X * (1 + X) ^ 2 * derivative (derivative f) +
      2 * (1 + X) * (1 + 5 * X) * derivative f + (1 + 2 * X) * f := by
  simp only [step, upperStep, lowerStep, derivative_add, derivative_mul,
    derivative_X, derivative_one, derivative_ofNat]
  ring

/-- The public A151775 update in expanded second-derivative form. -/
def nextRow (f : ℝ[X]) : ℝ[X] :=
  4 * X * (1 + X) ^ 2 * derivative (derivative f) +
    2 * (1 + X) * (1 + 5 * X) * derivative f + (1 + 2 * X) * f

/-- The model rows satisfy the public A151775 update. -/
theorem polynomial_succ (n : ℕ) : polynomial (n + 1) = nextRow (polynomial n) := by
  rw [polynomial, step_eq]
  rfl

/-- `step` is linear (`ℝ`-linear on the pencil): `step (α f + β g) = α step f + β step g`. -/
private theorem step_pencil (α β : ℝ) (f g : ℝ[X]) :
    step (C α * f + C β * g) = C α * step f + C β * step g := by
  simp only [step, upperStep, lowerStep, derivative_add, derivative_mul,
    derivative_X, derivative_one, derivative_ofNat, derivative_C, derivative_zero]
  ring

/-- **The split-factor derivative operator preserves real-rootedness (or zero).**
Proof: `(a f^m)' = f^(m-1) (a' f + m a f')`; the left side is the derivative of a split
polynomial (derivatives of split real polynomials split, Rolle), and a divisor of a split
polynomial splits. Here `Splits` includes the zero polynomial. -/
private theorem splits_splitFactorDerivative {a f : ℝ[X]}
    (ha : a.Splits) (hf : f.Splits) {m : ℕ}
    (hm : 1 ≤ m) : (splitFactorDerivative a m f).Splits := by
  have key : derivative (a * f ^ m) = f ^ (m - 1) * splitFactorDerivative a m f := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
    simp only [splitFactorDerivative, derivative_mul, derivative_pow_succ, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring
  by_cases hf0 : f = 0
  · subst hf0; simp [splitFactorDerivative]
  by_cases hD : derivative (a * f ^ m) = 0
  · rw [key] at hD
    rcases mul_eq_zero.mp hD with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hf0
    · rw [h]; exact Splits.zero
  have hderivative : (derivative (a * f ^ m)).Splits :=
    (ha.mul (hf.pow m)).derivative
  exact Splits.of_dvd hderivative hD ⟨_, by rw [key, mul_comm]⟩

private theorem splits_lowerStep {f : ℝ[X]} (hf : f.Splits) :
    (lowerStep f).Splits := by
  have h := splits_splitFactorDerivative (a := 1 + X) (m := 2)
    (Splits.of_natDegree_le_one (by compute_degree!)) hf (by norm_num)
  have e : splitFactorDerivative (1 + X) 2 f = lowerStep f := by
    simp only [splitFactorDerivative, lowerStep, derivative_add, derivative_one,
      derivative_X, Nat.cast_ofNat, map_ofNat]
    ring
  rwa [e] at h

private theorem splits_upperStep {f : ℝ[X]} (hf : f.Splits) :
    (upperStep f).Splits := by
  have ha : (X * (1 + X) : ℝ[X]).Splits :=
    (Splits.of_natDegree_le_one (by compute_degree!)).mul
      (Splits.of_natDegree_le_one (by compute_degree!))
  have h := splits_splitFactorDerivative (m := 2) ha hf (by norm_num)
  have e : splitFactorDerivative (X * (1 + X)) 2 f = upperStep f := by
    simp only [splitFactorDerivative, upperStep, derivative_mul, derivative_add,
      derivative_one, derivative_X, Nat.cast_ofNat, map_ofNat]
    ring
  rwa [e] at h

private theorem splits_step {f : ℝ[X]} (hf : f.Splits) : (step f).Splits :=
  splits_upperStep (splits_lowerStep hf)

private lemma coeff_lowerStep (f : ℝ[X]) (n : ℕ) :
    (lowerStep f).coeff n = (1 + 2 * n) * f.coeff n + 2 * (n + 1) * f.coeff (n + 1) := by
  have : lowerStep f = f + C 2 * derivative f + C 2 * (X * derivative f) := by
    simp only [lowerStep, map_ofNat]; ring
  rw [this]
  rcases n with _ | n
  · simp [coeff_derivative]
  · simp [coeff_derivative, coeff_X_mul]; ring

private lemma upperStep_eq (g : ℝ[X]) :
    upperStep g = g + C 2 * (X * g) + C 2 * (X * derivative g) +
      C 2 * (X * (X * derivative g)) := by
  simp only [upperStep, map_ofNat]; ring

private lemma coeff_zero_upperStep (g : ℝ[X]) : (upperStep g).coeff 0 = g.coeff 0 := by
  rw [upperStep_eq]
  simp

private lemma coeff_succ_upperStep (g : ℝ[X]) (n : ℕ) :
    (upperStep g).coeff (n + 1) = (2 * n + 3) * g.coeff (n + 1) + 2 * (n + 1) * g.coeff n := by
  rw [upperStep_eq]
  rcases n with _ | n
  · simp [coeff_derivative]; ring
  · simp [coeff_derivative, coeff_X_mul]; ring

private lemma natDegree_lowerStep {f : ℝ[X]} (hpos : 0 < f.leadingCoeff) :
    (lowerStep f).natDegree = f.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have hk' : f.natDegree < k := by exact_mod_cast hk
    rw [coeff_lowerStep, coeff_eq_zero_of_natDegree_lt hk',
      coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < k + 1)]
    ring
  · rw [coeff_lowerStep,
      coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < f.natDegree + 1)]
    have : 0 < f.coeff f.natDegree := hpos
    positivity

private lemma leadingCoeff_lowerStep_pos {f : ℝ[X]} (hpos : 0 < f.leadingCoeff) :
    0 < (lowerStep f).leadingCoeff := by
  rw [leadingCoeff, natDegree_lowerStep hpos, coeff_lowerStep,
    coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < f.natDegree + 1)]
  have : 0 < f.coeff f.natDegree := hpos
  positivity

private lemma natDegree_upperStep {g : ℝ[X]} (hpos : 0 < g.leadingCoeff) :
    (upperStep g).natDegree = g.natDegree + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have hk' : g.natDegree + 1 < k := by exact_mod_cast hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    rw [coeff_succ_upperStep,
      coeff_eq_zero_of_natDegree_lt (by lia : g.natDegree < j + 1),
      coeff_eq_zero_of_natDegree_lt (by lia : g.natDegree < j)]
    ring
  · rw [coeff_succ_upperStep,
      coeff_eq_zero_of_natDegree_lt (by lia : g.natDegree < g.natDegree + 1)]
    have : 0 < g.coeff g.natDegree := hpos
    positivity

private lemma leadingCoeff_upperStep_pos {g : ℝ[X]} (hpos : 0 < g.leadingCoeff) :
    0 < (upperStep g).leadingCoeff := by
  rw [leadingCoeff, natDegree_upperStep hpos, coeff_succ_upperStep,
    coeff_eq_zero_of_natDegree_lt (by lia : g.natDegree < g.natDegree + 1)]
  have : 0 < g.coeff g.natDegree := hpos
  positivity

private lemma hasNonnegCoeffs_lowerStep {f : ℝ[X]} (h : HasNonnegCoeffs f) :
    HasNonnegCoeffs (lowerStep f) := by
  intro k
  rw [coeff_lowerStep]
  have := h k
  have := h (k + 1)
  positivity

private lemma hasNonnegCoeffs_upperStep {g : ℝ[X]} (h : HasNonnegCoeffs g) :
    HasNonnegCoeffs (upperStep g) := by
  intro k
  rcases k with _ | k
  · rw [coeff_zero_upperStep]
    exact h 0
  · rw [coeff_succ_upperStep]
    have := h k
    have := h (k + 1)
    positivity

private lemma polynomial_props (n : ℕ) :
    (polynomial n).natDegree = n ∧
      HasPosLeadingCoeff (polynomial n) ∧ HasNonnegCoeffs (polynomial n) := by
  induction n with
  | zero =>
    refine ⟨by simp [polynomial], ?_, fun k => ?_⟩
    · simpa [polynomial] using hasPosLeadingCoeff_one
    · simp only [polynomial, coeff_one]
      split_ifs <;> norm_num
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [polynomial, step, natDegree_upperStep (leadingCoeff_lowerStep_pos h2),
        natDegree_lowerStep h2, h1]
    · exact leadingCoeff_upperStep_pos (leadingCoeff_lowerStep_pos h2)
    · exact hasNonnegCoeffs_upperStep (hasNonnegCoeffs_lowerStep h3)

/-- The `n`th A151775 row has degree `n`. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = n :=
  (polynomial_props n).1

/-- Every A151775 row has nonnegative coefficients. -/
theorem hasNonnegCoeffs_polynomial (n : ℕ) : HasNonnegCoeffs (polynomial n) :=
  (polynomial_props n).2.2

/-- **A151775 is real-rooted.** -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  induction n with
  | zero => simp [polynomial]
  | succ n ih => exact splits_step ih

private lemma splits_iterate_step {g : ℝ[X]} (hg : g.Splits) (n : ℕ) :
    (step^[n] g).Splits := by
  induction n with
  | zero => exact hg
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact splits_step ih

private lemma polynomial_pencil_eq (n : ℕ) (α β : ℝ) :
    C α * polynomial n + C β * polynomial (n + 1) = step^[n] (C α + C β * (1 + 2 * X)) := by
  induction n with
  | zero => simp [polynomial, step, upperStep, lowerStep]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, step_pencil]
    rfl

/-- Every real combination of two consecutive A151775 rows splits. -/
theorem allComboRealRooted_polynomial_succ (n : ℕ) :
    AllComboRealRooted (polynomial n) (polynomial (n + 1)) := by
  intro α β
  rw [polynomial_pencil_eq]
  exact splits_iterate_step (Splits.of_natDegree_le_one (by compute_degree!)) n

/-- Consecutive A151775 rows strictly interlace. -/
theorem strictInterl_polynomial_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  have hdegree : (polynomial (n + 1)).natDegree = (polynomial n).natDegree + 1 := by
    rw [natDegree_polynomial, natDegree_polynomial]
  have horientation := strictInterl_of_allComboRealRooted
    (polynomial_props n).2.1.ne_zero (splits_polynomial n)
    (polynomial_props (n + 1)).2.1.ne_zero (splits_polynomial (n + 1))
    (allComboRealRooted_polynomial_succ n) (Or.inl hdegree.symm)
  exact StrictInterl.forward_of_orientation_of_succDegree hdegree horientation

/-- Any sequence with the A151775 initial row and update has interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 2 * X)
    (hrec : ∀ n, P (n + 1) =
      (4 * X + 4 * X ^ 3 + 8 * X ^ 2) * (P n).derivative.derivative +
        (2 + 10 * X ^ 2 + 12 * X) * (P n).derivative + (1 + 2 * X) * P n)
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m, P m = polynomial m := by
    intro m
    induction m with
    | zero => exact hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl)
    | succ m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | _
        · exact hone.trans (by norm_num [polynomial, step, upperStep, lowerStep])
        · rw [hrec, polynomial_succ, ih, nextRow]
          ring
  rw [heq n, heq (n + 1)]
  exact (strictInterl_polynomial_succ n).toInterlaces (by
    rw [natDegree_polynomial, natDegree_polynomial])

end RealRooted.Applications.OEIS.A151775
