module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.IrreducibleDef
public import RealRooted.Basic.Coefficients

/-!
# Big descents of 132-avoiding permutations: the recurrence family

This file defines the polynomial family `B_N` by the positive recurrence

`B_(n+2) = 1 + B_(n+1) + t sum_(i<n) B_(i+1)
  + t sum_(i<n) B_(i+1) B_(n-i)
  + t^2 sum_(k<n) sum_(i<k) B_(i+1) B_(k-i)`.

The recurrence is defined over an arbitrary commutative semiring.  We prove that its
natural-number coefficients are positive precisely through degree `2 * (N - 1) / 3`.
The identification with the big-descent enumerator of 132-avoiding permutations is a
separate combinatorial-model obligation and is not asserted here.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RealRooted.BigDescents132

variable {R : Type*} [CommSemiring R]

/-- The recursion behind `bigDescentPoly`, before it is sealed by `irreducible_def`. -/
def bigDescentPolyAux : ℕ → R[X]
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      1 + bigDescentPolyAux (n + 1) +
      X * ∑ i : Fin n, bigDescentPolyAux (i.1 + 1) +
      X * ∑ i : Fin n, bigDescentPolyAux (i.1 + 1) * bigDescentPolyAux (n - i.1) +
      X ^ 2 * ∑ k : Fin n, ∑ i : Fin k.1,
        bigDescentPolyAux (i.1 + 1) * bigDescentPolyAux (k.1 - i.1)

/-- The recurrence-defined 132 big-descent polynomial family. -/
irreducible_def bigDescentPoly (n : ℕ) : R[X] := bigDescentPolyAux n

@[simp]
theorem bigDescentPoly_zero : bigDescentPoly 0 = (1 : R[X]) := by
  rw [bigDescentPoly_def, bigDescentPolyAux]

@[simp]
theorem bigDescentPoly_one : bigDescentPoly 1 = (1 : R[X]) := by
  rw [bigDescentPoly_def, bigDescentPolyAux]

/-- The division-free positive recurrence for the 132 big-descent family. -/
theorem bigDescentPoly_add_two (n : ℕ) :
    bigDescentPoly (n + 2) =
      1 + bigDescentPoly (n + 1) +
      X * ∑ i ∈ range n, bigDescentPoly (i + 1) +
      X * ∑ i ∈ range n, bigDescentPoly (i + 1) * bigDescentPoly (n - i) +
      X ^ 2 * ∑ k ∈ range n, ∑ i ∈ range k,
        bigDescentPoly (i + 1) * (bigDescentPoly (k - i) : R[X]) := by
  simp only [bigDescentPoly_def]
  rw [bigDescentPolyAux]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (bigDescentPolyAux (i + 1) : R[X]))]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ bigDescentPolyAux (i + 1) * bigDescentPolyAux (n - i))]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ ∑ i : Fin k,
      bigDescentPolyAux (i.1 + 1) * bigDescentPolyAux (k - i.1))]
  refine congrArg (fun p : R[X] ↦
    1 + bigDescentPolyAux (n + 1) + X * ∑ i ∈ range n, bigDescentPolyAux (i + 1) +
      X * ∑ i ∈ range n, bigDescentPolyAux (i + 1) * bigDescentPolyAux (n - i) +
      X ^ 2 * p) ?_
  refine sum_congr rfl fun k hk ↦ ?_
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ bigDescentPolyAux (i + 1) * bigDescentPolyAux (k - i))]

/-! ### Small values -/

theorem bigDescentPoly_two : bigDescentPoly 2 = (2 : R[X]) := by
  rw [bigDescentPoly_add_two (R := R) 0]
  norm_num

theorem bigDescentPoly_three : bigDescentPoly 3 = (3 + 2 * X : R[X]) := by
  rw [bigDescentPoly_add_two (R := R) 1]
  simp [bigDescentPoly_two]
  ring

theorem bigDescentPoly_four : bigDescentPoly 4 = (4 + 9 * X + X ^ 2 : R[X]) := by
  rw [bigDescentPoly_add_two (R := R) 2]
  simp [sum_range_succ, bigDescentPoly_two, bigDescentPoly_three]
  ring

theorem bigDescentPoly_five : bigDescentPoly 5 = (5 + 25 * X + 12 * X ^ 2 : R[X]) := by
  rw [bigDescentPoly_add_two (R := R) 3]
  simp [sum_range_succ, bigDescentPoly_two, bigDescentPoly_three, bigDescentPoly_four]
  ring

theorem bigDescentPoly_six :
    bigDescentPoly 6 = (6 + 55 * X + 64 * X ^ 2 + 7 * X ^ 3 : R[X]) := by
  rw [bigDescentPoly_add_two (R := R) 4]
  simp [sum_range_succ, bigDescentPoly_two, bigDescentPoly_three, bigDescentPoly_four,
    bigDescentPoly_five]
  ring

/-! ### Compatibility with ring homomorphisms -/

variable {S : Type*} [CommSemiring S] (f : R →+* S)

@[simp]
theorem map_bigDescentPoly (n : ℕ) :
    (bigDescentPoly n : R[X]).map f = bigDescentPoly n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      rw [bigDescentPoly_add_two, bigDescentPoly_add_two]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_one, map_X, Polynomial.map_sum]
      rw [ih (n + 1) (by lia)]
      congr 2
      · congr 2
        refine sum_congr rfl fun i hi ↦ ?_
        rw [ih (i + 1) (by have := mem_range.mp hi; lia)]
      · congr 1
        refine sum_congr rfl fun i hi ↦ ?_
        have hi' := mem_range.mp hi
        rw [ih (i + 1) (by lia), ih (n - i) (by lia)]
      · refine sum_congr rfl fun k hk ↦ ?_
        have hk' := mem_range.mp hk
        refine sum_congr rfl fun i hi ↦ ?_
        have hi' := mem_range.mp hi
        rw [ih (i + 1) (by lia), ih (k - i) (by lia)]

variable (R)

/-- Coefficients over any semiring are casts of the natural-number coefficients. -/
theorem coeff_bigDescentPoly_eq_cast (n k : ℕ) :
    (bigDescentPoly n : R[X]).coeff k = ((bigDescentPoly n : ℕ[X]).coeff k : R) := by
  rw [← map_bigDescentPoly (Nat.castRingHom R) n, coeff_map]
  rfl

variable {R}

/-! ### Evaluation at zero -/

/-- The constant coefficient of `B_(n+1)` is `n+1`. -/
theorem eval_zero_bigDescentPoly_succ (n : ℕ) :
    (bigDescentPoly (n + 1) : R[X]).eval 0 = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by lia, bigDescentPoly_add_two]
    simp [ih, Nat.cast_add, Nat.cast_one, add_comm]

/-! ### Degree upper bound -/

/-- The degree of `B_N` is at most `floor(2(N-1)/3)` over any commutative semiring. -/
theorem natDegree_bigDescentPoly_le (N : ℕ) :
    (bigDescentPoly N : R[X]).natDegree ≤ 2 * (N - 1) / 3 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp
    | 1 => simp
    | 2 => rw [bigDescentPoly_two]; simp
    | 3 => rw [bigDescentPoly_three]; compute_degree
    | n + 4 =>
      rw [show n + 4 = (n + 2) + 2 by lia, bigDescentPoly_add_two]
      refine natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_add_le_of_degree_le (by simp) ?_) ?_) ?_) ?_
      · exact (ih (n + 3) (by lia)).trans (by lia)
      · refine natDegree_mul_le.trans ?_
        have hX := natDegree_X_le (R := R)
        have hs : (∑ i ∈ range (n + 2), bigDescentPoly (i + 1) : R[X]).natDegree ≤
            2 * (n + 4 - 1) / 3 - 1 := by
          refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
          have hi' := mem_range.mp hi
          exact (ih (i + 1) (by lia)).trans (by lia)
        lia
      · refine natDegree_mul_le.trans ?_
        have hX := natDegree_X_le (R := R)
        have hs :
            (∑ i ∈ range (n + 2), bigDescentPoly (i + 1) *
              (bigDescentPoly (n + 2 - i) : R[X])).natDegree ≤
                2 * (n + 4 - 1) / 3 - 1 := by
          refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ natDegree_mul_le.trans ?_
          have hi' := mem_range.mp hi
          have h1 := ih (i + 1) (by lia)
          have h2 := ih (n + 2 - i) (by lia)
          lia
        lia
      · refine natDegree_mul_le.trans ?_
        have hX2 := natDegree_X_pow_le (R := R) 2
        have hs :
            (∑ k ∈ range (n + 2), ∑ i ∈ range k,
              bigDescentPoly (i + 1) * (bigDescentPoly (k - i) : R[X])).natDegree ≤
                2 * (n + 4 - 1) / 3 - 2 := by
          refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
          refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ natDegree_mul_le.trans ?_
          have hk' := mem_range.mp hk
          have hi' := mem_range.mp hi
          have h1 := ih (i + 1) (by lia)
          have h2 := ih (k - i) (by lia)
          lia
        lia

/-! ### Exact positive support -/

/-- The coefficient at the predicted top degree is positive over `ℕ`. -/
theorem coeff_bigDescentPoly_top_pos (N : ℕ) :
    0 < (bigDescentPoly N : ℕ[X]).coeff (2 * (N - 1) / 3) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp
    | 1 => simp
    | 2 => rw [bigDescentPoly_two]; norm_num
    | 3 => rw [bigDescentPoly_three]; norm_num
    | n + 4 =>
      rw [show n + 4 = (n + 2) + 2 by lia, bigDescentPoly_add_two]
      simp only [coeff_add]
      refine lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
      rw [show 2 * (n + 4 - 1) / 3 = 2 * (n + 1 - 1) / 3 + 2 by lia,
        coeff_X_pow_mul, finsetSum_coeff]
      refine lt_of_lt_of_le ?_ (single_le_sum (fun k _ ↦ Nat.zero_le _)
        (mem_range.mpr (by lia : n + 1 < n + 2)))
      rw [finsetSum_coeff]
      refine lt_of_lt_of_le ?_ (single_le_sum (fun i _ ↦ Nat.zero_le _)
        (mem_range.mpr (by lia : 0 < n + 1)))
      simp only [Nat.zero_add, Nat.sub_zero, bigDescentPoly_one, one_mul]
      exact ih (n + 1) (by lia)

/-- The coefficients of `B_N` are positive exactly on its predicted support. -/
theorem coeff_bigDescentPoly_pos_iff (N k : ℕ) :
    0 < (bigDescentPoly N : ℕ[X]).coeff k ↔ k ≤ 2 * (N - 1) / 3 := by
  constructor
  · intro hk
    by_contra hle
    push Not at hle
    rw [coeff_eq_zero_of_natDegree_lt
      ((natDegree_bigDescentPoly_le N).trans_lt hle)] at hk
    exact (Nat.not_lt_zero 0) hk
  · intro hk
    induction N using Nat.strong_induction_on generalizing k with
    | _ N ih =>
      match N with
      | 0 =>
        have : k = 0 := by lia
        subst k
        simp
      | 1 =>
        have : k = 0 := by lia
        subst k
        simp
      | n + 2 =>
        by_cases hprev : k ≤ 2 * (n + 1 - 1) / 3
        · rw [bigDescentPoly_add_two]
          simp only [coeff_add]
          have hpos := ih (n + 1) (by lia) k hprev
          lia
        · have htop : k = 2 * (n + 2 - 1) / 3 := by
            push Not at hprev
            have hstep : 2 * (n + 2 - 1) / 3 ≤ 2 * (n + 1 - 1) / 3 + 1 := by lia
            lia
          rw [htop]
          exact coeff_bigDescentPoly_top_pos (n + 2)

section CharZero

variable [CharZero R]

/-- In characteristic zero, `B_N` has degree `floor(2(N-1)/3)`. -/
theorem natDegree_bigDescentPoly (N : ℕ) :
    (bigDescentPoly N : R[X]).natDegree = 2 * (N - 1) / 3 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_bigDescentPoly_le N) ?_
  rw [coeff_bigDescentPoly_eq_cast]
  exact Nat.cast_ne_zero.mpr (coeff_bigDescentPoly_top_pos N).ne'

theorem bigDescentPoly_ne_zero (N : ℕ) : (bigDescentPoly N : R[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  match N with
  | 0 => simp at this
  | n + 1 =>
    rw [eval_zero_bigDescentPoly_succ, eval_zero] at this
    have hn : (((n + 1 : ℕ) : R)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    exact hn (by simpa [Nat.cast_add, Nat.cast_one] using this)

end CharZero

/-! ### Real-coefficient consequences -/

theorem hasNonnegCoeffs_bigDescentPoly (N : ℕ) :
    HasNonnegCoeffs (bigDescentPoly N : ℝ[X]) := by
  intro k
  rw [coeff_bigDescentPoly_eq_cast]
  positivity

theorem hasPosLeadingCoeff_bigDescentPoly (N : ℕ) :
    HasPosLeadingCoeff (bigDescentPoly N : ℝ[X]) :=
  (hasNonnegCoeffs_bigDescentPoly N).pos_leadingCoeff (bigDescentPoly_ne_zero N)

theorem coeff_zero_bigDescentPoly_pos (N : ℕ) :
    0 < (bigDescentPoly N : ℝ[X]).coeff 0 := by
  rw [coeff_bigDescentPoly_eq_cast]
  exact_mod_cast (coeff_bigDescentPoly_pos_iff N 0).mpr (Nat.zero_le _)

end RealRooted.BigDescents132
