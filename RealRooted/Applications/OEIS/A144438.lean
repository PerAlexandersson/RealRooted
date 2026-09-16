import RealRooted.DerivativeRecurrence.SecondOrderInterlacing

/-!
# The deco Eulerian recurrence and OEIS A144438

This file studies the polynomial sequence defined by

`D 0 = 1`, `D 1 = 1 + X`, and

`D (n + 2) = X (1 - X) (D (n + 1))' + (1 + (n + 2) X) D (n + 1) + X D n`.

The definition gives an algebraic facade for OEIS A144438. With local index
`m`, the corresponding OEIS row is `m + 1` and the deco-polyomino height used
in the literature is `m + 2`. No combinatorial identification is asserted
here: the checked connection is the initial values and recurrence alone.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The recurrence-defined deco Eulerian polynomial sequence. -/
def decoEulerian : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (X - X ^ 2) * (decoEulerian (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * decoEulerian (n + 1) + X * decoEulerian n

@[simp]
theorem decoEulerian_zero : decoEulerian 0 = 1 := rfl

@[simp]
theorem decoEulerian_one : decoEulerian 1 = 1 + X := rfl

/-- The defining second-order derivative recurrence. -/
theorem decoEulerian_recurrence (n : ℕ) :
    decoEulerian (n + 2) =
      (X - X ^ 2) * (decoEulerian (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * decoEulerian (n + 1) +
          X * decoEulerian n := rfl

/-- The first nontrivial row. -/
theorem decoEulerian_two : decoEulerian 2 = 1 + 5 * X + X ^ 2 := by
  norm_num [decoEulerian, map_ofNat]
  ring_nf

/-- The next row, included as a recurrence normalization check. -/
theorem decoEulerian_three :
    decoEulerian 3 = 1 + 14 * X + 14 * X ^ 2 + X ^ 3 := by
  norm_num [decoEulerian, map_ofNat]
  ring_nf

private theorem decoEulerian_affine_recurrence (n : ℕ) :
    decoEulerian (n + 2) =
      (C 1 * X + C (-1) * X ^ 2) * (decoEulerian (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * decoEulerian (n + 1) +
          (C 1 * X) * decoEulerian n := by
  simpa only [map_one, map_neg, one_mul, neg_one_mul, sub_eq_add_neg] using
    decoEulerian_recurrence n

/-- The complete rankwise certificate obtained from the independent-lag
second-order recurrence theorem. -/
theorem decoEulerian_certificate (n : ℕ) :
    AffineLagSecondOrderCertificate decoEulerian n := by
  exact affine_lag_second_order_derivative_certificate_of_nonneg_lag
    decoEulerian 1 1 (by norm_num) (by norm_num) decoEulerian_zero
      decoEulerian_one (by
        intro m
        simpa only [one_mul, one_add_one_eq_two] using
          decoEulerian_affine_recurrence m) n

/-- Every deco Eulerian polynomial has degree equal to its local index. -/
@[simp]
theorem decoEulerian_natDegree (n : ℕ) : (decoEulerian n).natDegree = n :=
  (decoEulerian_certificate n).natDegree

/-- Every deco Eulerian polynomial is monic. -/
theorem decoEulerian_monic (n : ℕ) : (decoEulerian n).Monic := by
  exact monic_of_second_order_derivative decoEulerian 1 1
    (fun m => (2 : ℝ) + m) decoEulerian_zero decoEulerian_one
      decoEulerian_affine_recurrence (by intro m; ring) n

/-- Every deco Eulerian polynomial has nonnegative coefficients. -/
theorem decoEulerian_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (decoEulerian n) :=
  (decoEulerian_certificate n).nonnegCoeffs

/-- Every deco Eulerian polynomial has constant coefficient one. -/
@[simp]
theorem decoEulerian_coeff_zero (n : ℕ) : (decoEulerian n).coeff 0 = 1 :=
  (decoEulerian_certificate n).coeff_zero

/-- Specialized coefficient recurrence used to prove positivity throughout
the coefficient support. -/
theorem decoEulerian_coeff_succ_succ (n k : ℕ) :
    (decoEulerian (n + 2)).coeff (k + 1) =
      ((k : ℝ) + 2) * (decoEulerian (n + 1)).coeff (k + 1) +
        ((n : ℝ) + 2 - k) * (decoEulerian (n + 1)).coeff k +
          (decoEulerian n).coeff k := by
  rw [second_order_derivative_coeff_succ_succ decoEulerian 1 1
    (fun m => (2 : ℝ) + m) decoEulerian_affine_recurrence]
  ring

/-- Every coefficient in the degree support is strictly positive. -/
theorem decoEulerian_coeff_pos_of_le :
    ∀ n k : ℕ, k ≤ n → 0 < (decoEulerian n).coeff k := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by lia
      subst k
      simp
  | one =>
      intro k hk
      interval_cases k <;> norm_num [decoEulerian, coeff_add, coeff_one, coeff_X]
  | more n ih0 ih1 =>
      intro k hk
      rcases k with _ | k
      · simp
      · rw [decoEulerian_coeff_succ_succ]
        have hk_le : k ≤ n + 1 := by lia
        have hk_real : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk_le
        have hfirst :
            0 ≤ ((k : ℝ) + 2) * (decoEulerian (n + 1)).coeff (k + 1) :=
          mul_nonneg (by positivity)
            ((decoEulerian_certificate (n + 1)).nonnegCoeffs (k + 1))
        have hmiddle :
            0 < ((n : ℝ) + 2 - k) * (decoEulerian (n + 1)).coeff k :=
          mul_pos (by linarith) (ih1 k hk_le)
        have hlast : 0 ≤ (decoEulerian n).coeff k :=
          (decoEulerian_certificate n).nonnegCoeffs k
        linarith

/-- Coefficients are positive exactly on the interval from zero through the
degree. -/
theorem decoEulerian_coeff_pos_iff (n k : ℕ) :
    0 < (decoEulerian n).coeff k ↔ k ≤ n := by
  constructor
  · intro hpos
    by_contra hle
    have hzero : (decoEulerian n).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [decoEulerian_natDegree]; lia)
    linarith
  · exact decoEulerian_coeff_pos_of_le n k

/-- Deco Eulerian polynomials are nonzero. -/
theorem decoEulerian_ne_zero (n : ℕ) : decoEulerian n ≠ 0 :=
  (decoEulerian_monic n).ne_zero

/-- Consecutive deco Eulerian polynomials are in proper position and have no
common real root. -/
theorem decoEulerian_prec_and_noCommonRoot (n : ℕ) :
    StrictInterl (decoEulerian n) (decoEulerian (n + 1)) ∧
      ∀ r : ℝ, (decoEulerian (n + 1)).IsRoot r →
        ¬ (decoEulerian n).IsRoot r :=
  ⟨(decoEulerian_certificate n).prec_succ,
    (decoEulerian_certificate n).noCommonRoot_succ⟩

/-- Every deco Eulerian polynomial splits over the reals. -/
theorem decoEulerian_splits (n : ℕ) : (decoEulerian n).Splits :=
  (decoEulerian_certificate n).splits

/-- Consecutive deco Eulerian polynomials are in proper position. -/
theorem decoEulerian_prec (n : ℕ) :
    StrictInterl (decoEulerian n) (decoEulerian (n + 1)) :=
  (decoEulerian_certificate n).prec_succ

/-- Consecutive deco Eulerian polynomials interlace with degree difference
one. -/
theorem decoEulerian_interlaces (n : ℕ) :
    Interlaces (decoEulerian n) (decoEulerian (n + 1)) :=
  (decoEulerian_certificate n).interlaces_succ

/-- Consecutive deco Eulerian polynomials have no common real root. -/
theorem decoEulerian_noCommonRoot (n : ℕ) (r : ℝ)
    (hr : (decoEulerian (n + 1)).IsRoot r) :
    ¬ (decoEulerian n).IsRoot r :=
  (decoEulerian_certificate n).noCommonRoot_succ r hr

/-- All real roots of a deco Eulerian polynomial are strictly negative. -/
theorem decoEulerian_root_neg (n : ℕ) {r : ℝ}
    (hr : (decoEulerian n).IsRoot r) : r < 0 :=
  (decoEulerian_certificate n).roots_neg r hr

/-- Deco Eulerian polynomials have only simple roots. -/
theorem decoEulerian_hasSimpleRoots (n : ℕ) : HasSimpleRoots (decoEulerian n) :=
  (decoEulerian_certificate n).simpleRoots

/-- The reversed prefix through rank `n`. -/
def decoEulerianPrefix (n : ℕ) : List ℝ[X] :=
  (List.range (n + 1)).reverse.map decoEulerian

/-- Every reversed finite prefix is a Sturm sequence. -/
theorem decoEulerian_isSturmSeq (n : ℕ) : IsSturmSeq (decoEulerianPrefix n) := by
  exact isSturmSeq_affine_lag_second_order_derivative_of_nonneg_lag
    decoEulerian 1 1 (by norm_num) (by norm_num) decoEulerian_zero
      decoEulerian_one (by
        intro m
        simpa only [one_mul, one_add_one_eq_two] using
          decoEulerian_affine_recurrence m) n

/-- Algebraic OEIS A144438 facade. External row `m + 1` is represented by
`A144438 m`; this name does not assert a combinatorial interpretation. -/
abbrev A144438 : ℕ → ℝ[X] := decoEulerian

@[simp]
theorem A144438_zero : A144438 0 = 1 := decoEulerian_zero

@[simp]
theorem A144438_one : A144438 1 = 1 + X := decoEulerian_one

/-- The exact recurrence bridge for the algebraic A144438 facade. -/
theorem A144438_recurrence (n : ℕ) :
    A144438 (n + 2) =
      (X - X ^ 2) * (A144438 (n + 1)).derivative +
        (C 1 + C ((2 : ℝ) + n) * X) * A144438 (n + 1) + X * A144438 n :=
  decoEulerian_recurrence n

/-- The full recurrence certificate exposed through the algebraic A144438
facade. -/
theorem A144438_certificate (n : ℕ) :
    AffineLagSecondOrderCertificate A144438 n :=
  decoEulerian_certificate n

/-- The A144438 polynomial at local rank `n` has degree `n`. -/
theorem A144438_natDegree (n : ℕ) : (A144438 n).natDegree = n :=
  decoEulerian_natDegree n

/-- Every A144438 polynomial is monic. -/
theorem A144438_monic (n : ℕ) : (A144438 n).Monic :=
  decoEulerian_monic n

/-- Every A144438 polynomial has nonnegative coefficients. -/
theorem A144438_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (A144438 n) :=
  decoEulerian_hasNonnegCoeffs n

/-- Every A144438 polynomial has constant coefficient one. -/
@[simp]
theorem A144438_coeff_zero (n : ℕ) : (A144438 n).coeff 0 = 1 :=
  decoEulerian_coeff_zero n

/-- Coefficients inside the degree support are strictly positive. -/
theorem A144438_coeff_pos_of_le (n k : ℕ) (hk : k ≤ n) :
    0 < (A144438 n).coeff k :=
  decoEulerian_coeff_pos_of_le n k hk

/-- A coefficient is positive exactly when its index lies in the degree
support. -/
theorem A144438_coeff_pos_iff (n k : ℕ) :
    0 < (A144438 n).coeff k ↔ k ≤ n :=
  decoEulerian_coeff_pos_iff n k

/-- Every A144438 polynomial is nonzero. -/
theorem A144438_ne_zero (n : ℕ) : A144438 n ≠ 0 :=
  decoEulerian_ne_zero n

/-- Every A144438 polynomial splits over the reals. -/
theorem A144438_splits (n : ℕ) : (A144438 n).Splits :=
  decoEulerian_splits n

/-- Consecutive A144438 polynomials are in proper position. -/
theorem A144438_prec (n : ℕ) : StrictInterl (A144438 n) (A144438 (n + 1)) :=
  decoEulerian_prec n

/-- Consecutive A144438 polynomials interlace. -/
theorem A144438_interlaces (n : ℕ) :
    Interlaces (A144438 n) (A144438 (n + 1)) :=
  decoEulerian_interlaces n

/-- Consecutive A144438 polynomials have no common real root. -/
theorem A144438_noCommonRoot (n : ℕ) (r : ℝ)
    (hr : (A144438 (n + 1)).IsRoot r) :
    ¬ (A144438 n).IsRoot r :=
  decoEulerian_noCommonRoot n r hr

/-- Every real root of an A144438 polynomial is strictly negative. -/
theorem A144438_root_neg (n : ℕ) {r : ℝ}
    (hr : (A144438 n).IsRoot r) : r < 0 :=
  decoEulerian_root_neg n hr

/-- Every A144438 polynomial has simple roots. -/
theorem A144438_hasSimpleRoots (n : ℕ) : HasSimpleRoots (A144438 n) :=
  decoEulerian_hasSimpleRoots n

end RealRooted.Applications.OEIS
