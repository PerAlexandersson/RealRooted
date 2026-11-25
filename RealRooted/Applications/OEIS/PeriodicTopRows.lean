module

public import RealRooted.DerivativeRecurrence.MultiLagCancel
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness

/-!
# Remaining periodic-top-coefficient rows

This file closes the A177040 degree problem; the A114580 and A390883 degrees are proved in
the downstream oeis-proofs repository. We identify A177040 with a coupled pair of monic rows
by finite-recurrence uniqueness.
The coupled update makes the degree growth explicit, so no coefficient formula is needed.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowParityDegree

noncomputable section

/-- The downstream A177040 recurrence. -/
def A177040 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 2 + X
  | 3 => 3 + X
  | n + 4 =>
      let r : ℝ := n
      (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * (A177040 (n + 3)).derivative
        + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * (A177040 (n + 2)).derivative
        + (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * (A177040 (n + 1)).derivative
        + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * (A177040 n).derivative
        + (C (2 / 5 - 1 / 5 * r) + C (3 / 5 + 1 / 5 * r) * X) * A177040 (n + 3)
        + (C (2 + 2 / 5 * r) + C (-2 / 5 * r) * X) * A177040 (n + 2)
        + (C (2 / 5 + 1 / 5 * r) + C (-7 / 5 - 1 / 5 * r) * X) * A177040 (n + 1)
        + (C (-13 / 5 - 2 / 5 * r) + C (8 / 5 + 2 / 5 * r) * X) * A177040 n

/-- The order-four update of the A177040 rows. -/
def A177040Next (n : ℕ) (p₃ p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * p₃.derivative
    + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * p₂.derivative
    + (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * p₁.derivative
    + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * p₀.derivative
    + (C (2 / 5 + (-1 / 5) * (n : ℝ)) +
        C (3 / 5 + (1 / 5) * (n : ℝ)) * X) * p₃
    + (C (2 + (2 / 5) * (n : ℝ)) + C ((-2 / 5) * (n : ℝ)) * X) * p₂
    + (C (2 / 5 + (1 / 5) * (n : ℝ)) +
        C (-7 / 5 + (-1 / 5) * (n : ℝ)) * X) * p₁
    + (C (-13 / 5 + (-2 / 5) * (n : ℝ)) +
        C (8 / 5 + (2 / 5) * (n : ℝ)) * X) * p₀

private theorem A177040_step (n : ℕ) :
    A177040 (n + 4) = A177040Next n (A177040 (n + 3))
      (A177040 (n + 2)) (A177040 (n + 1)) (A177040 n) := by
  rw [A177040]
  dsimp only [A177040Next]
  ring_nf

/-- Coupled even and odd rows, with their degree growth explicit. -/
private def modelPair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 1)
  | n + 1 =>
    let e := (modelPair n).1 + X * (modelPair n).2 + 1
    (e, e + (modelPair n).2)

private def evenModel (n : ℕ) : ℝ[X] := (modelPair n).1
private def oddModel (n : ℕ) : ℝ[X] := (modelPair n).2

private lemma evenModel_succ (n : ℕ) :
    evenModel (n + 1) = evenModel n + X * oddModel n + 1 := rfl

private lemma oddModel_succ (n : ℕ) :
    oddModel (n + 1) = evenModel (n + 1) + oddModel n := rfl

/-- The two differential identities needed by the order-four presentation. -/
private lemma model_differential (n : ℕ) :
    X * (X + 4) * (evenModel n).derivative =
        -(((n : ℝ[X]) + 2) * X + 2) * evenModel n +
          2 * ((n : ℝ[X]) + 1) * X * oddModel n + 2 * ((n : ℝ[X]) + 1) ∧
      X * (X + 4) * (oddModel n).derivative =
        (2 * (n : ℝ[X]) + 3) * evenModel n + ((n : ℝ[X]) * X - 4) * oddModel n +
          ((n : ℝ[X]) + 1) := by
  induction n with
  | zero => norm_num [evenModel, oddModel, modelPair]
  | succ n ih =>
    rw [oddModel_succ, evenModel_succ]
    simp only [derivative_add, derivative_mul, derivative_X, derivative_one,
      one_mul, add_zero, Nat.cast_add, Nat.cast_one]
    constructor
    · linear_combination ih.1 + X * ih.2
    · linear_combination ih.1 + (X + 1) * ih.2

private def model (n : ℕ) : ℝ[X] :=
  if n % 2 = 0 then evenModel (n / 2) else oddModel (n / 2)

private lemma model_even (n : ℕ) : model (2 * n) = evenModel n := by
  simp [model]

private lemma model_odd (n : ℕ) : model (2 * n + 1) = oddModel n := by
  simp [model, Nat.add_div]

/-- The coupled rows satisfy the original differential update. -/
private lemma model_step (n : ℕ) :
    model (n + 4) = A177040Next n (model (n + 3)) (model (n + 2))
      (model (n + 1)) (model n) := by
  simp only [A177040Next]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [show 2 * m + 4 = 2 * (m + 2) by lia,
      show 2 * m + 3 = 2 * (m + 1) + 1 by lia,
      show 2 * m + 2 = 2 * (m + 1) by lia, model_even, model_odd]
    rw [oddModel_succ, evenModel_succ, oddModel_succ, evenModel_succ]
    simp only [derivative_add, derivative_mul, derivative_X, derivative_one,
      one_mul, add_zero]
    apply mul_left_cancel₀ (mul_ne_zero X_ne_zero
      (by simpa only [map_ofNat] using (monic_X_add_C (4 : ℝ)).ne_zero))
    apply Polynomial.funext
    intro x
    have he := congrArg (fun p : ℝ[X] => p.eval x) (model_differential m).1
    have ho := congrArg (fun p : ℝ[X] => p.eval x) (model_differential m).2
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      eval_one, eval_ofNat, eval_natCast, eval_neg] at he ho ⊢
    push_cast
    linear_combination
      ((2 / 5 : ℝ) * (1 - x) * 3 * x) * he +
        ((2 / 5 : ℝ) * (1 - x) * x * (x - 2)) * ho
  · simp only [show 2 * m + 1 + 4 = 2 * (m + 2) + 1 by lia,
      show 2 * m + 1 + 3 = 2 * (m + 2) by lia,
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by lia,
      show 2 * m + 1 + 1 = 2 * (m + 1) by lia, model_even, model_odd]
    rw [oddModel_succ, evenModel_succ, oddModel_succ, evenModel_succ]
    simp only [derivative_add, derivative_mul, derivative_X, derivative_one,
      one_mul, add_zero]
    apply mul_left_cancel₀ (mul_ne_zero X_ne_zero
      (by simpa only [map_ofNat] using (monic_X_add_C (4 : ℝ)).ne_zero))
    apply Polynomial.funext
    intro x
    have he := congrArg (fun p : ℝ[X] => p.eval x) (model_differential m).1
    have ho := congrArg (fun p : ℝ[X] => p.eval x) (model_differential m).2
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      eval_one, eval_ofNat, eval_natCast, eval_neg] at he ho ⊢
    push_cast
    linear_combination
      ((-2 / 5 : ℝ) * x ^ 2 * (1 - x)) * he +
        ((-2 / 5 : ℝ) * x * (1 - x) * (x ^ 2 + x - 4)) * ho

/-- Each coupled row is bounded by its index and has top coefficient one. -/
private lemma model_top (n : ℕ) :
    ((evenModel n).natDegree ≤ n ∧ (evenModel n).coeff n = 1) ∧
      ((oddModel n).natDegree ≤ n ∧ (oddModel n).coeff n = 1) := by
  induction n with
  | zero => simp [evenModel, oddModel, modelPair]
  | succ n ih =>
    have he : (evenModel (n + 1)).natDegree ≤ n + 1 := by
      rw [evenModel_succ]
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
      refine (natDegree_add_le _ _).trans (max_le (by lia) ?_)
      exact natDegree_mul_le.trans (by rw [natDegree_X]; lia)
    have hec : (evenModel (n + 1)).coeff (n + 1) = 1 := by
      rw [evenModel_succ, coeff_add, coeff_add, coeff_X_mul, ih.2.2,
        coeff_eq_zero_of_natDegree_lt (ih.1.1.trans_lt (Nat.lt_succ_self n))]
      simp [coeff_one]
    have ho : (oddModel (n + 1)).natDegree ≤ n + 1 := by
      rw [oddModel_succ]
      exact (natDegree_add_le _ _).trans (max_le he (by lia))
    have hoc : (oddModel (n + 1)).coeff (n + 1) = 1 := by
      rw [oddModel_succ, coeff_add, hec,
        coeff_eq_zero_of_natDegree_lt (ih.2.1.trans_lt (Nat.lt_succ_self n)), add_zero]
    exact ⟨⟨he, hec⟩, ⟨ho, hoc⟩⟩

private lemma model_top_row (n : ℕ) :
    (model n).natDegree ≤ n / 2 ∧ (model n).coeff (n / 2) = 1 := by
  unfold model
  split_ifs
  · exact (model_top (n / 2)).1
  · exact (model_top (n / 2)).2

private lemma A177040_eq_model (n : ℕ) : A177040 n = model n := by
  exact sequence_eq_of_same_lag_four_recurrence A177040Next
    (by norm_num [A177040, model, evenModel, oddModel, modelPair])
    (by norm_num [A177040, model, evenModel, oddModel, modelPair])
    (by norm_num [A177040, model, evenModel, oddModel, modelPair]; ring)
    (by norm_num [A177040, model, evenModel, oddModel, modelPair]; ring)
    A177040_step model_step n

private lemma A177040_monic_natDegree (n : ℕ) :
    (A177040 n).Monic ∧ (A177040 n).natDegree = n / 2 := by
  rw [A177040_eq_model]
  obtain ⟨hdeg, hcoeff⟩ := model_top_row n
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hdeg hcoeff,
    natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; norm_num)⟩

/-- The A177040 row indexed by `n` has degree `n / 2` and positive leading
coefficient.  The proof transfers the top coefficients of the coupled even and odd model. -/
theorem A177040_natDegree_eq_and_leadingCoeff_pos (n : ℕ) :
    (A177040 n).natDegree = n / 2 ∧ 0 < (A177040 n).leadingCoeff := by
  obtain ⟨hm, hd⟩ := A177040_monic_natDegree n
  exact ⟨hd, by rw [hm.leadingCoeff]; norm_num⟩

/-- The natural degree of the A177040 row indexed by `n` is `n / 2`. -/
theorem A177040_natDegree (n : ℕ) : (A177040 n).natDegree = n / 2 :=
  (A177040_natDegree_eq_and_leadingCoeff_pos n).1

/-- Every A177040 row has leading coefficient one. -/
theorem A177040_leadingCoeff (n : ℕ) : (A177040 n).leadingCoeff = 1 := by
  exact (A177040_monic_natDegree n).1.leadingCoeff

/-- The A177040 row indexed by `n` has positive leading coefficient. -/
theorem A177040_leadingCoeff_pos (n : ℕ) : 0 < (A177040 n).leadingCoeff := by
  rw [A177040_leadingCoeff]
  norm_num

/-- The initial window and order-four update uniquely determine A177040. -/
private theorem A177040_eq_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 4, P i = A177040 i)
    (hrec : ∀ n, P (n + 4) =
      A177040Next n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    : ∀ m, P m = A177040 m := by
  exact sequence_eq_of_same_finite_recurrence
    (k := 4) (op := fun n w => A177040Next n (w 3) (w 2) (w 1) (w 0))
    hinit hrec A177040_step

/-- Any sequence satisfying the A177040 initial window and update has degree `n / 2`. -/
@[rr_row_model]
theorem A177040_natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 4, P i = A177040 i)
    (hrec : ∀ n, P (n + 4) =
      A177040Next n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).natDegree = n / 2 := by
  rw [A177040_eq_of_recurrence hinit hrec n]
  exact A177040_natDegree n

/-- Any sequence satisfying the A177040 initial window and update has positive leaders. -/
@[rr_row_model]
theorem A177040_leadingCoeff_pos_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 4, P i = A177040 i)
    (hrec : ∀ n, P (n + 4) =
      A177040Next n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) : 0 < (P n).leadingCoeff := by
  rw [A177040_eq_of_recurrence hinit hrec n]
  exact A177040_leadingCoeff_pos n


end

end RealRooted.Tactic.RowParityDegree
