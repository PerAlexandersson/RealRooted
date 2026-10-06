import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.IrreducibleDef

/-!
# Big descents of 321-avoiding permutations: the polynomial families

A big descent of a permutation `π` is an index `i` with `π(i) > π(i + 1) + 1`.
Elizalde, Rivera and Zhuang (*Counting pattern-avoiding permutations by big
descents*, arXiv:2408.15111) show that the big-descent polynomials `A_n(t)` of
321-avoiding permutations satisfy
`∑ A_n x^n = 1 / (1 - I)` with first-return series
`I = x + x^2 + t x^2 (M - 1)`, where `M = 1 + 2 x M + t x^2 M^2`.

This file defines the families by these finite recurrences over an arbitrary
commutative semiring:

* `motzkinRef k`: the reference polynomials `M_0 = 1`, `M_1 = 2` and
  `M_k = 2 M_(k-1) + t ∑_(i+j=k-2) M_i M_j`, the coefficients of `M`;
* `firstReturn j`: the first-return terms `I_1 = I_2 = 1`, `I_j = t M_(j-2)`;
* `bigDescentPoly n`: the convolution `A_0 = 1`, `A_n = ∑_(j=1)^n I_j A_(n-j)`.

The identification of `bigDescentPoly n` with the big-descent enumerator of
321-avoiding permutations is the cited theorem of Elizalde, Rivera and Zhuang;
it is not formalized here.

Both recursive families are `irreducible_def`s: the kernel ignores the elaborator's
irreducibility, and unfolding a well-founded recursion at a literal index costs exponential
time and memory. Use the equation lemmas `motzkinRef_add_two`, `bigDescentPoly_succ`.

## Main results

* `natDegree_motzkinRef`, `natDegree_bigDescentPoly`: `deg M_k = ⌊k/2⌋` and
  `deg A_(n+3) = ⌊(n + 3)/2⌋`, with positive top coefficients.
* `eval_zero_motzkinRef`, `eval_zero_bigDescentPoly`: `M_k(0) = 2^k` and `A_n(0) = F_(n+1)`.
* `map_motzkinRef`, `map_bigDescentPoly`: compatibility with ring homomorphisms.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.BigDescents321

variable {R : Type*} [CommSemiring R]

/-- The recursion `M_0 = 1`, `M_1 = 2`, `M_(k+2) = 2 M_(k+1) + t ∑_(i ≤ k) M_i M_(k-i)`. -/
private def motzkinRefAux : ℕ → R[X]
  | 0 => 1
  | 1 => 2
  | k + 2 => 2 * motzkinRefAux (k + 1) +
      X * ∑ i : Fin (k + 1), motzkinRefAux i.1 * motzkinRefAux (k - i.1)

/-- The reference Motzkin polynomials, the coefficients of `M = 1 + 2xM + tx²M²`:
`M_0 = 1`, `M_1 = 2` and `M_(k+2) = 2 M_(k+1) + t ∑_(i ≤ k) M_i M_(k-i)`. -/
irreducible_def motzkinRef (k : ℕ) : R[X] := motzkinRefAux k

@[simp]
theorem motzkinRef_zero : motzkinRef 0 = (1 : R[X]) := by
  rw [motzkinRef_def, motzkinRefAux]

@[simp]
theorem motzkinRef_one : motzkinRef 1 = (2 : R[X]) := by
  rw [motzkinRef_def, motzkinRefAux]

theorem motzkinRef_add_two (k : ℕ) :
    motzkinRef (k + 2) = 2 * motzkinRef (k + 1) +
      X * ∑ i ∈ range (k + 1), motzkinRef i * (motzkinRef (k - i) : R[X]) := by
  simp only [motzkinRef_def]
  rw [motzkinRefAux, Fin.sum_univ_eq_sum_range
    (fun i ↦ motzkinRefAux i * (motzkinRefAux (k - i) : R[X]))]

/-- The first-return polynomials: `I_1 = I_2 = 1` and `I_j = t M_(j-2)` for
`j ≥ 3`. -/
def firstReturn : ℕ → R[X]
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | j + 3 => X * motzkinRef (j + 1)

/-- The convolution `A_0 = 1`, `A_n = ∑_(j=1)^n I_j A_(n-j)`, by well-founded recursion. -/
private def bigDescentPolyAux : ℕ → R[X]
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1), firstReturn (j.1 + 1) * bigDescentPolyAux (n - j.1)

/-- The recurrence-defined big-descent polynomials: `A_0 = 1` and
`A_n = ∑_(j=1)^n I_j A_(n-j)`. -/
irreducible_def bigDescentPoly (n : ℕ) : R[X] := bigDescentPolyAux n

@[simp]
theorem bigDescentPoly_zero : bigDescentPoly 0 = (1 : R[X]) := by
  rw [bigDescentPoly_def, bigDescentPolyAux]

theorem bigDescentPoly_succ (n : ℕ) :
    bigDescentPoly (n + 1) =
      ∑ j ∈ range (n + 1), firstReturn (j + 1) * (bigDescentPoly (n - j) : R[X]) := by
  simp only [bigDescentPoly_def]
  rw [bigDescentPolyAux, Fin.sum_univ_eq_sum_range
    (fun j ↦ firstReturn (j + 1) * (bigDescentPolyAux (n - j) : R[X]))]

@[simp] theorem firstReturn_zero : firstReturn 0 = (0 : R[X]) := rfl
@[simp] theorem firstReturn_one : firstReturn 1 = (1 : R[X]) := rfl
@[simp] theorem firstReturn_two : firstReturn 2 = (1 : R[X]) := rfl

theorem firstReturn_add_three (j : ℕ) :
    firstReturn (j + 3) = (X * motzkinRef (j + 1) : R[X]) := rfl

/-! ### Compatibility with ring homomorphisms -/

section Map

variable {S : Type*} [CommSemiring S] (f : R →+* S)

@[simp]
theorem map_motzkinRef (k : ℕ) : (motzkinRef k : R[X]).map f = motzkinRef k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [motzkinRef_add_two, motzkinRef_add_two, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_mul, Polynomial.map_sum, ih _ (by lia), map_X, Polynomial.map_ofNat]
      congr 2
      refine sum_congr rfl fun i hi ↦ ?_
      have := mem_range.mp hi
      rw [Polynomial.map_mul, ih _ (by lia), ih _ (by lia)]

@[simp]
theorem map_firstReturn (j : ℕ) : (firstReturn j : R[X]).map f = firstReturn j := by
  match j with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | j + 3 => simp [firstReturn_add_three]

@[simp]
theorem map_bigDescentPoly (n : ℕ) :
    (bigDescentPoly n : R[X]).map f = bigDescentPoly n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [bigDescentPoly_succ, bigDescentPoly_succ, Polynomial.map_sum]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [Polynomial.map_mul, map_firstReturn, ih _ (by lia)]

end Map

/-! ### Small values and evaluation at zero -/

theorem bigDescentPoly_one : bigDescentPoly 1 = (1 : R[X]) := by
  simp [bigDescentPoly_succ]

theorem bigDescentPoly_two : bigDescentPoly 2 = (2 : R[X]) := by
  simp [bigDescentPoly_succ, sum_range_succ]
  norm_num

theorem bigDescentPoly_three : bigDescentPoly 3 = (3 + 2 * X : R[X]) := by
  simp [bigDescentPoly_succ, sum_range_succ, firstReturn_add_three]
  ring

theorem eval_zero_motzkinRef (k : ℕ) : (motzkinRef k : R[X]).eval 0 = 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [motzkinRef_add_two, eval_add, eval_mul, eval_mul, eval_X, zero_mul, add_zero,
        ih _ (by lia)]
      simp [pow_succ]
      ring

theorem eval_zero_firstReturn (j : ℕ) :
    (firstReturn j : R[X]).eval 0 = if j = 1 ∨ j = 2 then 1 else 0 := by
  match j with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | j + 3 => simp [firstReturn_add_three]

/-- `A_n(0)` is the Fibonacci number `F_(n+1)`. -/
theorem eval_zero_bigDescentPoly (n : ℕ) :
    (bigDescentPoly n : R[X]).eval 0 = (n + 1).fib := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [bigDescentPoly_one]
    | n + 2 =>
      rw [bigDescentPoly_succ, eval_finsetSum, sum_range_succ', sum_range_succ']
      have hrest : ∑ j ∈ range n,
          (firstReturn (j + 1 + 1 + 1) * (bigDescentPoly (n + 1 - (j + 1 + 1)) : R[X])).eval 0
            = 0 := by
        refine sum_eq_zero fun j _ ↦ ?_
        rw [eval_mul, eval_zero_firstReturn]
        simp
      rw [hrest, eval_mul, eval_mul, eval_zero_firstReturn, eval_zero_firstReturn,
        ih _ (by lia), ih _ (by lia), Nat.fib_add_two (n := n + 1)]
      simp [Nat.cast_add, add_comm]

/-! ### Degrees -/

theorem natDegree_motzkinRef_le (k : ℕ) : (motzkinRef k : R[X]).natDegree ≤ k / 2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [motzkinRef_add_two]
      refine natDegree_add_le_of_degree_le ?_ ?_
      · refine natDegree_mul_le.trans ?_
        have := ih (k + 1) (by lia)
        have h2 : (2 : R[X]).natDegree = 0 := natDegree_ofNat 2
        lia
      · refine natDegree_mul_le.trans ?_
        have hX := natDegree_X_le (R := R)
        have hs : (∑ i ∈ range (k + 1), motzkinRef i * (motzkinRef (k - i) : R[X])).natDegree ≤
            k / 2 := by
          refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ natDegree_mul_le.trans ?_
          have := mem_range.mp hi
          have h1 := ih i (by lia)
          have h2 := ih (k - i) (by lia)
          lia
        lia

theorem natDegree_firstReturn_le (j : ℕ) : (firstReturn j : R[X]).natDegree ≤ j / 2 := by
  match j with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | j + 3 =>
    rw [firstReturn_add_three]
    refine natDegree_mul_le.trans ?_
    have := natDegree_motzkinRef_le (R := R) (j + 1)
    have hX := natDegree_X_le (R := R)
    lia

theorem natDegree_bigDescentPoly_le (n : ℕ) :
    (bigDescentPoly n : R[X]).natDegree ≤ n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [bigDescentPoly_succ]
      refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ natDegree_mul_le.trans ?_
      have h1 := natDegree_firstReturn_le (R := R) (j + 1)
      have h2 := ih (n - j) (by lia)
      have hj' := mem_range.mp hj
      lia

/-! ### Top coefficients -/

/-- Coefficients over any semiring are casts of the natural-number coefficients. -/
theorem coeff_motzkinRef_eq_cast (k i : ℕ) :
    (motzkinRef k : R[X]).coeff i = ((motzkinRef k : ℕ[X]).coeff i : R) := by
  rw [← map_motzkinRef (Nat.castRingHom R) k, coeff_map]
  rfl

theorem coeff_bigDescentPoly_eq_cast (n i : ℕ) :
    (bigDescentPoly n : R[X]).coeff i = ((bigDescentPoly n : ℕ[X]).coeff i : R) := by
  rw [← map_bigDescentPoly (Nat.castRingHom R) n, coeff_map]
  rfl

/-- The top coefficient of `M_k`, at index `k / 2`, is positive. -/
theorem coeff_motzkinRef_half_pos (k : ℕ) : 0 < (motzkinRef k : ℕ[X]).coeff (k / 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [motzkinRef_add_two, coeff_add]
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · -- `k` even: the term `t M_0 M_k` reaches the top
        rw [show (m + m + 2) / 2 = (m + m) / 2 + 1 by lia, coeff_X_mul, finsetSum_coeff]
        refine lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
        refine lt_of_lt_of_le ?_ (single_le_sum (fun i _ ↦ Nat.zero_le _)
          (mem_range.mpr (Nat.succ_pos (m + m))))
        rw [Nat.sub_zero, motzkinRef_zero, one_mul]
        exact ih (m + m) (by lia)
      · -- `k` odd: the term `2 M_(k+1)` reaches the top
        rw [show (2 * m + 1 + 2) / 2 = (2 * m + 1 + 1) / 2 by lia]
        refine lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
        rw [show (2 : ℕ[X]) = C 2 from rfl, coeff_C_mul]
        exact Nat.mul_pos (by norm_num) (ih _ (by lia))

/-- The top coefficient of `A_(n+3)`, at index `(n + 3) / 2`, is positive. -/
theorem coeff_bigDescentPoly_half_pos (n : ℕ) :
    0 < (bigDescentPoly (n + 3) : ℕ[X]).coeff ((n + 3) / 2) := by
  rw [bigDescentPoly_succ, finsetSum_coeff]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun j _ ↦ Nat.zero_le _)
    (mem_range.mpr (Nat.lt_succ_self (n + 2))))
  rw [Nat.sub_self, bigDescentPoly_zero, mul_one, show n + 2 + 1 = n + 3 by lia,
    firstReturn_add_three, show (n + 3) / 2 = (n + 1) / 2 + 1 by lia, coeff_X_mul]
  exact coeff_motzkinRef_half_pos (n + 1)

section CharZero

variable [CharZero R]

/-- `deg M_k = ⌊k/2⌋`. -/
theorem natDegree_motzkinRef (k : ℕ) : (motzkinRef k : R[X]).natDegree = k / 2 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_motzkinRef_le k) ?_
  rw [coeff_motzkinRef_eq_cast]
  exact Nat.cast_ne_zero.mpr (coeff_motzkinRef_half_pos k).ne'

/-- `deg A_(n+3) = ⌊(n + 3)/2⌋`. -/
theorem natDegree_bigDescentPoly (n : ℕ) :
    (bigDescentPoly (n + 3) : R[X]).natDegree = (n + 3) / 2 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_bigDescentPoly_le _) ?_
  rw [coeff_bigDescentPoly_eq_cast]
  exact Nat.cast_ne_zero.mpr (coeff_bigDescentPoly_half_pos n).ne'

theorem bigDescentPoly_ne_zero (n : ℕ) : (bigDescentPoly n : R[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  rw [eval_zero_bigDescentPoly, eval_zero] at this
  exact (Nat.fib_pos.mpr (Nat.succ_pos n)).ne' (by exact_mod_cast this)

theorem motzkinRef_ne_zero (k : ℕ) : (motzkinRef k : R[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  rw [eval_zero_motzkinRef, eval_zero] at this
  have h2 : ((2 ^ k : ℕ) : R) = 0 := by push_cast; exact this
  exact (pow_ne_zero k two_ne_zero) (Nat.cast_eq_zero.mp h2)

end CharZero

end RealRooted.BigDescents321
