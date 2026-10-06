import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
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

This file defines the families by finite recurrences over an arbitrary
commutative semiring:

* `motzkinRef k`: the reference polynomials
  `M_k(t) = ∑_a binom(k, 2a) Cat_a 2^(k - 2a) t^a`;
* `firstReturn j`: the first-return terms `I_1 = I_2 = 1`, `I_j = t M_(j-2)`;
* `bigDescentPoly n`: the convolution `A_0 = 1`, `A_n = ∑_(j=1)^n I_j A_(n-j)`.

The identification of `bigDescentPoly n` with the big-descent enumerator of
321-avoiding permutations is the cited theorem of Elizalde, Rivera and Zhuang;
it is not formalized here.

## Main results

* `natDegree_bigDescentPoly`: `deg A_(n+3) = (n + 3) / 2`.
* `eval_zero_bigDescentPoly`: `A_n(0) = F_(n+1)`.
* `map_bigDescentPoly`: the families are compatible with ring homomorphisms.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.BigDescents321

variable {R : Type*} [CommSemiring R]

/-- The reference Motzkin polynomial
`M_k(t) = ∑_a binom(k, 2a) Cat_a 2^(k - 2a) t^a`.

Like `bigDescentPoly`, it is irreducible also for the kernel, since unfolding it at a
literal index would evaluate the well-founded `catalan`. Use `motzkinRef_def`. -/
irreducible_def motzkinRef (k : ℕ) : R[X] :=
  ∑ a ∈ range (k / 2 + 1),
    ((k.choose (2 * a) * catalan a * 2 ^ (k - 2 * a) : ℕ) : R[X]) * X ^ a

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
`A_n = ∑_(j=1)^n I_j A_(n-j)`.

The definition is irreducible, also for the kernel: unfolding the well-founded recursion
at a literal index costs exponential time and memory. Use `bigDescentPoly_zero` and
`bigDescentPoly_succ` instead. -/
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
  simp only [motzkinRef_def, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_natCast,
    Polynomial.map_pow, map_X]

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

theorem motzkinRef_zero : motzkinRef 0 = (1 : R[X]) := by
  simp [motzkinRef_def]

theorem motzkinRef_one : motzkinRef 1 = (2 : R[X]) := by
  simp [motzkinRef_def]

theorem bigDescentPoly_three : bigDescentPoly 3 = (3 + 2 * X : R[X]) := by
  simp [bigDescentPoly_succ, sum_range_succ, firstReturn_add_three, motzkinRef_one]
  ring

theorem eval_zero_motzkinRef (k : ℕ) : (motzkinRef k : R[X]).eval 0 = 2 ^ k := by
  rw [motzkinRef_def, eval_finsetSum, sum_eq_single 0]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

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
  rw [motzkinRef_def]
  refine natDegree_sum_le_of_forall_le _ _ fun a ha ↦ ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_natCast, zero_add]
  exact (natDegree_X_pow_le a).trans (Nat.lt_succ_iff.mp (mem_range.mp ha))

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

/-! ### Coefficients -/

theorem coeff_motzkinRef (k a : ℕ) :
    (motzkinRef k : R[X]).coeff a =
      ((k.choose (2 * a) * catalan a * 2 ^ (k - 2 * a) : ℕ) : R) := by
  rw [motzkinRef_def, finsetSum_coeff]
  simp only [coeff_natCast_mul, coeff_X_pow]
  rw [sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro ha
    rw [mem_range, Nat.lt_succ_iff, not_le] at ha
    rw [Nat.choose_eq_zero_of_lt (by lia)]
    simp

theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, mul_zero] at h
    lia
  · exact h0

/-- The top coefficient of `M_k`, at index `k / 2`, is positive. -/
theorem coeff_motzkinRef_half_pos (k : ℕ) : 0 < (motzkinRef k : ℕ[X]).coeff (k / 2) := by
  rw [coeff_motzkinRef, Nat.cast_id]
  have h1 : 0 < k.choose (2 * (k / 2)) := Nat.choose_pos (by lia)
  have h2 := catalan_pos (k / 2)
  positivity

/-- Coefficients of the families over any semiring are casts of their natural-number
coefficients. -/
theorem coeff_bigDescentPoly_eq_cast (n i : ℕ) :
    (bigDescentPoly n : R[X]).coeff i = ((bigDescentPoly n : ℕ[X]).coeff i : R) := by
  rw [← map_bigDescentPoly (Nat.castRingHom R) n, coeff_map]
  rfl

theorem coeff_motzkinRef_eq_cast (k i : ℕ) :
    (motzkinRef k : R[X]).coeff i = ((motzkinRef k : ℕ[X]).coeff i : R) := by
  rw [← map_motzkinRef (Nat.castRingHom R) k, coeff_map]
  rfl

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

theorem natDegree_motzkinRef (k : ℕ) : (motzkinRef k : R[X]).natDegree = k / 2 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_motzkinRef_le k) ?_
  rw [coeff_motzkinRef_eq_cast]
  exact Nat.cast_ne_zero.mpr (coeff_motzkinRef_half_pos k).ne'

/-- `deg A_(n+3) = (n + 3) / 2`. -/
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

end CharZero

end RealRooted.BigDescents321
