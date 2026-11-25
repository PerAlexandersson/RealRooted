module

import Mathlib.Analysis.Polynomial.Basic
public import RealRooted.Basic
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
public import RealRooted.Basic.ProperPosition
import RealRooted.MaWang.Strong
import RealRooted.Linear

/-!
# Adjacent strict interlacing for OEIS A259454

The polynomial family is defined by Riordan's compact row recurrence. Its first rows are

`1`, `1 + 3 * X`, and `1 + 6 * X + 7 * X ^ 2`.

The generated downstream definition instead uses a lag-three differential recurrence with
rational coefficients. The second half of this file proves that recurrence defines the same
family.

Mathematically, these are rook polynomials of the board with cells
`(i,i)`, `(i,i+1)`, and `(i,i+2)`.  Equivalently they are matching-generating
polynomials of the corresponding banded bipartite graphs.  General matching
polynomial real-rootedness proves splitting, but the missing content here is
the sharper adjacent interlacing as the board grows by one row and one column.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.A259454

/-- Riordan's compact recurrence for the A259454 row polynomials. -/
def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 6 * X + 7 * X ^ 2
  | n + 3 =>
      (1 + 2 * X) * row (n + 2) + X * row (n + 1) -
        X ^ 3 * row n + X ^ (n + 3)

/-! ## Auxiliary development

We introduce four auxiliary polynomial families `pS, pA, pE, pC` (a transfer-matrix
refinement of the rows; combinatorially they are rook polynomials of the board with
the last one or two columns removed).  `pS n = row n`, and the key identity
`pE n * pA n - pS n * pC n = X ^ 2 * (pA (n-1) ^ 2 + ...)` is a sum of squares. -/

/-- The four-state transfer recursion. -/
private def quad : ℕ → ℝ[X] × ℝ[X] × ℝ[X] × ℝ[X]
  | 0 => (1, 1, 1, 1)
  | n + 1 =>
    let q := quad n
    ((1 + X) * q.1 + X * q.2.1 + X * q.2.2.1, q.1 + X * q.2.1 + X * q.2.2.1,
      (1 + X) * q.2.1 + X * q.2.2.2, q.2.1 + X * q.2.2.2)

private def pS (n : ℕ) : ℝ[X] := (quad n).1
private def pA (n : ℕ) : ℝ[X] := (quad n).2.1
private def pE (n : ℕ) : ℝ[X] := (quad n).2.2.1
private def pC (n : ℕ) : ℝ[X] := (quad n).2.2.2

private lemma pS_zero : pS 0 = 1 := rfl
private lemma pA_zero : pA 0 = 1 := rfl
private lemma pE_zero : pE 0 = 1 := rfl
private lemma pC_zero : pC 0 = 1 := rfl
private lemma pS_succ (n : ℕ) : pS (n + 1) = (1 + X) * pS n + X * pA n + X * pE n := rfl
private lemma pA_succ (n : ℕ) : pA (n + 1) = pS n + X * pA n + X * pE n := rfl
private lemma pE_succ (n : ℕ) : pE (n + 1) = (1 + X) * pA n + X * pC n := rfl
private lemma pC_succ (n : ℕ) : pC (n + 1) = pA n + X * pC n := rfl

private lemma pA_succ' (n : ℕ) : pA (n + 1) = pS (n + 1) - X * pS n := by
  rw [pA_succ, pS_succ]; ring

private lemma pC_succ' (n : ℕ) : pC (n + 1) = pS n + X ^ (n + 1) := by
  induction n with
  | zero => rw [pC_succ, pA_zero, pC_zero, pS_zero]; ring
  | succ n ih => rw [pC_succ, ih, pA_succ']; ring

private lemma pS_rec (n : ℕ) : pS (n + 3) =
    (1 + 2 * X) * pS (n + 2) + X * pS (n + 1) - X ^ 3 * pS n + X ^ (n + 3) := by
  rw [pS_succ (n + 2), pA_succ' (n + 1), pE_succ (n + 1), pA_succ' n, pC_succ' n]
  ring

private lemma pS_eq_row (n : ℕ) : pS n = row n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rw [pS_succ, pS_zero, pA_zero, pE_zero, row]; ring
    | 2, _ =>
      rw [pS_succ, pS_succ, pA_succ, pE_succ, pS_zero, pA_zero, pE_zero, pC_zero, row]; ring
    | n + 3, ih =>
      rw [pS_rec, ih n (by lia), ih (n + 1) (by lia), ih (n + 2) (by lia), row]

private lemma deg_facts (n : ℕ) :
    (pS n).natDegree ≤ n ∧ (pA n).natDegree ≤ n ∧ (pE n).natDegree ≤ n ∧
      (pC n).natDegree ≤ n ∧ 1 ≤ (pS n).coeff n ∧ 1 ≤ (pA n).coeff n ∧
      1 ≤ (pE n).coeff n ∧ 1 ≤ (pC n).coeff n := by
  induction n with
  | zero => simp [pS_zero, pA_zero, pE_zero, pC_zero]
  | succ n ih =>
    obtain ⟨hS, hA, hE, hC, cS, cA, cE, cC⟩ := ih
    have z : ∀ p : ℝ[X], p.natDegree ≤ n → p.coeff (n + 1) = 0 := fun p hp =>
      coeff_eq_zero_of_natDegree_lt (by lia)
    rw [pS_succ, pA_succ, pE_succ, pC_succ]
    refine ⟨by compute_degree; lia, by compute_degree; lia,
      by compute_degree; lia, by compute_degree; lia,
      ?_, ?_, ?_, ?_⟩ <;>
    simp only [add_mul, one_mul, coeff_add, coeff_X_mul, z _ hS, z _ hA] <;>
    linarith

/-- The sum-of-squares identity. -/
private lemma delta_succ (n : ℕ) : pE (n + 1) * pA (n + 1) - pS (n + 1) * pC (n + 1) =
    X ^ 2 * (pA n ^ 2 + (pE n * pA n - pS n * pC n)) := by
  rw [pE_succ, pA_succ, pS_succ, pC_succ]; ring

private lemma delta_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ (pE n * pA n - pS n * pC n).eval t := by
  induction n with
  | zero => simp [pE_zero, pA_zero, pS_zero, pC_zero]
  | succ n ih =>
    rw [delta_succ]
    simp only [eval_mul, eval_pow, eval_X, eval_add] at ih ⊢
    positivity

private lemma pS_natDegree (n : ℕ) : (pS n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (deg_facts n).1 (by linarith [(deg_facts n).2.2.2.2.1])

private lemma pS_leadingCoeff_pos (n : ℕ) : 0 < (pS n).leadingCoeff := by
  rw [leadingCoeff, pS_natDegree]; linarith [(deg_facts n).2.2.2.2.1]

private lemma pS_ne_zero (n : ℕ) : pS n ≠ 0 :=
  leadingCoeff_ne_zero.mp (pS_leadingCoeff_pos n).ne'

private lemma pS_eval_zero (n : ℕ) : (pS n).eval 0 = 1 := by
  induction n with
  | zero => simp [pS_zero]
  | succ n ih => simp [pS_succ, ih]

/-- The transfer matrix has nonnegative polynomial entries. -/
private lemma quad_nonneg (n : ℕ) :
    HasNonnegCoeffs (pS n) ∧ HasNonnegCoeffs (pA n) ∧
      HasNonnegCoeffs (pE n) ∧ HasNonnegCoeffs (pC n) := by
  have hX := hasNonnegCoeffs_X
  have hlin := hasNonnegCoeffs_one.add hX
  induction n with
  | zero => simp only [pS_zero, pA_zero, pE_zero, pC_zero]; exact
      ⟨hasNonnegCoeffs_one, hasNonnegCoeffs_one, hasNonnegCoeffs_one, hasNonnegCoeffs_one⟩
  | succ n ih =>
      rw [pS_succ, pA_succ, pE_succ, pC_succ]
      exact ⟨((hlin.mul ih.1).add (hX.mul ih.2.1)).add (hX.mul ih.2.2.1),
        (ih.1.add (hX.mul ih.2.1)).add (hX.mul ih.2.2.1),
        (hlin.mul ih.2.1).add (hX.mul ih.2.2.2), ih.2.1.add (hX.mul ih.2.2.2)⟩

/-- The positive constant term excludes the endpoint zero. -/
private lemma pS_root_neg {n : ℕ} {r : ℝ} (hr : (pS n).IsRoot r) : r < 0 := by
  refine lt_of_le_of_ne
    (isRoot_nonpos_of_hasNonnegCoeffs (quad_nonneg n).1 (pS_ne_zero n) hr) ?_
  rintro rfl
  have h := hr.eq_zero
  rw [pS_eval_zero] at h
  norm_num at h

/-- The sum-of-squares identity gives the strict Liu--Wang sign condition. -/
private lemma pS_eval_mul_neg (n : ℕ) {r : ℝ} (hr : (pS (n + 1)).IsRoot r)
    (hprev : ¬ (pS n).IsRoot r) :
    (pS (n + 2)).eval r * (pS n).eval r < 0 := by
  have hneg := pS_root_neg hr
  have hD := delta_nonneg (n + 1) r
  have hA : (pA (n + 1)).eval r = -r * (pS n).eval r := by
    rw [pA_succ']
    simp only [eval_sub, eval_mul, eval_X, hr.eq_zero, zero_sub, neg_mul]
  have hF : (pS (n + 2)).eval r =
      r * (pA (n + 1)).eval r + r * (pE (n + 1)).eval r := by
    rw [pS_succ (n + 1)]
    simp only [eval_add, eval_mul, eval_one, eval_X, hr.eq_zero, mul_zero, zero_add]
  simp only [eval_sub, eval_mul, hr.eq_zero, zero_mul, sub_zero] at hD
  have hAne : (pA (n + 1)).eval r ≠ 0 := by
    rw [hA]
    exact mul_ne_zero (neg_ne_zero.mpr hneg.ne) hprev
  calc
    (pS (n + 2)).eval r * (pS n).eval r =
        -((pA (n + 1)).eval r ^ 2 +
          (pE (n + 1)).eval r * (pA (n + 1)).eval r) := by
      rw [hF]
      linear_combination ((pA (n + 1)).eval r + (pE (n + 1)).eval r) * hA
    _ < 0 := by nlinarith [sq_pos_of_ne_zero hAne]

/-- Apply the general strict sign step instead of constructing roots and root lists. -/
private lemma pS_interlaces_and_no_common (n : ℕ) :
    Interlaces (pS n) (pS (n + 1)) ∧
      ∀ r, (pS (n + 1)).IsRoot r → ¬ (pS n).IsRoot r := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [pS_zero]
        exact interlaces_one_linear (by rw [pS_natDegree])
      · intro r _ hr
        simp only [pS_zero, Polynomial.IsRoot, eval_one, one_ne_zero] at hr
  | succ n ih =>
      have hsign := fun r hr => pS_eval_mul_neg n hr (ih.2 r hr)
      have hi := MaWang.strictInterl_of_interlaces_eval_mul_neg_succ ih.1
        (pS_leadingCoeff_pos n) (pS_leadingCoeff_pos (n + 2))
        (by rw [pS_natDegree, pS_natDegree]) hsign
      refine ⟨hi.toInterlaces (by rw [pS_natDegree, pS_natDegree]), ?_⟩
      intro r hr hrprev
      have h := hsign r hrprev
      rw [hr.eq_zero, zero_mul] at h
      exact (lt_irrefl 0) h

/-- Consecutive A259454 rows are in strict proper position.

The sum-of-squares argument was found by Aristotle (Harmonic); the interlacing
step uses the general strict Liu--Wang sign theorem. -/
theorem row_strictInterl_succ (n : ℕ) : StrictInterl (row n) (row (n + 1)) := by
  rw [← pS_eq_row, ← pS_eq_row]
  exact (pS_interlaces_and_no_common n).1.toStrictInterl

/-- The A259454 row indexed by `n` has degree `n`. -/
theorem row_natDegree (n : ℕ) : (row n).natDegree = n := by
  simpa only [← pS_eq_row] using pS_natDegree n

/-- Consecutive A259454 rows interlace. -/
theorem row_interlaces_succ (n : ℕ) : Interlaces (row n) (row (n + 1)) :=
  (row_strictInterl_succ n).toInterlaces (by simp only [row_natDegree])

/-! ## Bridge from the generated differential recurrence -/

/-- The lag-three differential update in the generated A259454 presentation. -/
def nextRow (n : ℕ) (p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C ((10 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X +
      C ((26 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 2) * p₂.derivative +
    (C ((-3 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X +
      C ((-10 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 2 +
      C ((-33 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 3) * p₁.derivative +
    (C ((1 / (-3 + -1 * (n : ℝ))) * (-27 / 7 + (-10 / 7) * (n : ℝ))) +
      C ((1 / (-3 + -1 * (n : ℝ))) * (-101 / 7 + (-40 / 7) * (n : ℝ))) * X) * p₂ +
    (C ((1 / (-3 + -1 * (n : ℝ))) * (6 / 7 + (3 / 7) * (n : ℝ))) +
      C ((1 / (-3 + -1 * (n : ℝ))) * (5 / 7 + (n : ℝ))) * X +
      C ((1 / (-3 + -1 * (n : ℝ))) * (40 / 7 + (33 / 7) * (n : ℝ))) * X ^ 2) * p₁ +
    (C ((3 / 7) * (1 / (-3 + -1 * (n : ℝ))) * (4 + (n : ℝ))) * X ^ 2 +
      C ((1 / (-3 + -1 * (n : ℝ))) * (4 + (n : ℝ))) * X ^ 3) * p₀

private def literalRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 6 * X + 7 * X ^ 2
  | n + 3 => nextRow n (literalRows (n + 2)) (literalRows (n + 1)) (literalRows n)

private def compactRHS (n : ℕ) : ℝ[X] :=
  (1 + 2 * X) * literalRows (n + 2) + X * literalRows (n + 1) -
    X ^ 3 * literalRows n + X ^ (n + 3)

private def clearedRHS (n : ℕ) : ℝ[X] :=
  (C (-10) * X + C (-26) * X ^ 2) * (literalRows (n + 2)).derivative +
    (C 3 * X + C 10 * X ^ 2 + C 33 * X ^ 3) *
      (literalRows (n + 1)).derivative +
    (C (10 * (n : ℝ) + 27) + C (40 * (n : ℝ) + 101) * X) *
      literalRows (n + 2) -
    (C (3 * (n : ℝ) + 6) + C (7 * (n : ℝ) + 5) * X +
      C (33 * (n : ℝ) + 40) * X ^ 2) * literalRows (n + 1) -
    (C (3 * ((n : ℝ) + 4)) * X ^ 2 + C (7 * ((n : ℝ) + 4)) * X ^ 3) * literalRows n

private lemma clearedRHS_eq_scale_nextRow (n : ℕ) :
    clearedRHS n = C (7 * ((n : ℝ) + 3)) *
      nextRow n (literalRows (n + 2)) (literalRows (n + 1)) (literalRows n) := by
  have : (-3 : ℝ) - (n : ℝ) ≠ 0 := by grind
  unfold nextRow clearedRHS
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
  grind

private lemma literalRows_step (n : ℕ) :
    literalRows (n + 3) =
      nextRow n (literalRows (n + 2)) (literalRows (n + 1)) (literalRows n) := by
  rw [literalRows]

private lemma literalRows_compact_recurrence (n : ℕ) :
    literalRows (n + 3) =
      (1 + 2 * X) * literalRows (n + 2) + X * literalRows (n + 1) -
        X ^ 3 * literalRows n + X ^ (n + 3) := by
  have hraw : nextRow n (literalRows (n + 2)) (literalRows (n + 1))
      (literalRows n) = compactRHS n := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      match n with
      | 0 =>
        apply Polynomial.funext
        intro x
        simp [nextRow, compactRHS, literalRows]
        ring
      | 1 | 2 =>
        apply Polynomial.funext
        intro x
        simp [nextRow, compactRHS, literalRows]
        grind
      | k + 3 =>
        have hcc := ih (k + 2) (by lia)
        have hc := ih (k + 1) (by lia)
        have hp := ih k (by lia)
        have scaled (i : ℕ)
            (hi : nextRow i (literalRows (i + 2)) (literalRows (i + 1))
              (literalRows i) = compactRHS i) :
            clearedRHS i = C (7 * ((i : ℝ) + 3)) * compactRHS i := by
          rw [clearedRHS_eq_scale_nextRow, hi]
        have hccN := scaled (k + 2) hcc
        have hcN := scaled (k + 1) hc
        have hpN := scaled k hp
        have hrr := (literalRows_step (k + 2)).trans hcc
        have hr := (literalRows_step (k + 1)).trans hc
        have hrp := (literalRows_step k).trans hp
        unfold compactRHS at hrr hr hrp
        have hscale : C (7 * (((k + 3 : ℕ) : ℝ) + 3)) ≠ (0 : ℝ[X]) := by
          rw [C_ne_zero]
          positivity
        apply mul_left_cancel₀ hscale
        rw [← clearedRHS_eq_scale_nextRow (k + 3)]
        unfold clearedRHS compactRHS at hccN hcN hpN ⊢
        norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hrr hr hrp hccN hcN hpN ⊢
        rw [hr, hrp] at hccN
        rw [hrp] at hcN
        rw [hrr, hr, hrp]
        simp only [derivative_add, derivative_sub, derivative_mul,
          derivative_pow, derivative_X, derivative_one, derivative_ofNat,
          zero_mul, zero_add, Nat.cast_add] at hccN hcN hpN ⊢
        apply Polynomial.funext
        intro x
        have hccx := congrArg (Polynomial.eval x) hccN
        have hcx := congrArg (Polynomial.eval x) hcN
        have hpx := congrArg (Polynomial.eval x) hpN
        simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
          eval_one, eval_ofNat] at hccx hcx hpx ⊢
        norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hccx hcx hpx ⊢
        linear_combination (-x ^ 3) * hpx + x * hcx + (1 + 2 * x) * hccx
  simpa [compactRHS] using (literalRows_step n).trans hraw

private lemma literalRows_eq_row : ∀ n : ℕ, literalRows n = row n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 => rfl
    | k + 3 =>
      rw [literalRows_compact_recurrence, row,
        ih k (by lia), ih (k + 1) (by lia), ih (k + 2) (by lia)]

/-- Every sequence with the generated A259454 initial rows and differential recurrence equals
Riordan's compact row family. -/
theorem eq_row_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X)
    (htwo : P 2 = 1 + 6 * X + 7 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) : P n = row n := by
  rw [← literalRows_eq_row]
  exact sequence_eq_of_same_lag_three_recurrence nextRow
    (by simpa only [literalRows] using hzero)
    (by simpa only [literalRows] using hone)
    (by simpa only [literalRows] using htwo)
    hrec literalRows_step n

/-- Every sequence with the generated A259454 recurrence has interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X)
    (htwo : P 2 = 1 + 6 * X + 7 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  rw [eq_row_of_recurrence hzero hone htwo hrec,
    eq_row_of_recurrence hzero hone htwo hrec]
  exact row_interlaces_succ n

end RealRooted.A259454
