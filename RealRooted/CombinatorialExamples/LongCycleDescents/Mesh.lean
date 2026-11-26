/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Coefficients
public import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Tactic

/-!
# Small integer sign certificates for descent polynomials

We evaluate ascending integer coefficient lists at dyadic nodes, then use the
library's strict sign-change theorem. No stored coefficient rows enter the checker.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset

/-- An exact rational with a denominator that is a power of two. -/
structure Dyadic where
  /-- The signed numerator. -/
  numer : ℤ
  /-- The exponent of the power-of-two denominator. -/
  shift : ℕ
  deriving Inhabited

namespace Dyadic

/-- The zero dyadic number. -/
def zero : Dyadic := ⟨0, 0⟩

/-- Interpret a dyadic number as a real number. -/
noncomputable def value (x : Dyadic) : ℝ := (x.numer : ℝ) / (2 : ℝ) ^ x.shift

/-- The zero dyadic number represents real zero. -/
@[simp] theorem value_zero : zero.value = 0 := by simp [zero, value]

/-- Compare dyadic numbers by exact shifted-integer cross multiplication. -/
def less (a b : Dyadic) : Bool :=
  decide ((a.numer <<< b.shift) < (b.numer <<< a.shift))

/-- The shifted-integer comparison agrees with the real order. -/
theorem less_iff (a b : Dyadic) : a.less b = true ↔ a.value < b.value := by
  simp only [less, decide_eq_true_eq, value, lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ b.shift)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ a.shift)]
  simp only [Int.shiftLeft_eq]
  exact_mod_cast (Iff.rfl :
    (a.numer : ℝ) * (2 : ℝ) ^ b.shift < (b.numer : ℝ) * (2 : ℝ) ^ a.shift ↔ _)

end Dyadic

/-- Homogenized Horner recursion with a supplied exponent for the denominator. -/
def dyadicHorner (x : Dyadic) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | n, a :: as => (a <<< (x.shift * n)) + x.numer * dyadicHorner x (n - 1) as

/-- Integer Horner evaluation with denominator `2 ^ (x.shift * cs.length)`. -/
def homogeneous (x : Dyadic) (cs : List ℤ) : ℤ := dyadicHorner x cs.length cs

/-- Homogenized integer Horner evaluation clears a positive dyadic denominator. -/
theorem homogeneous_eq_eval (x : Dyadic) (cs : List ℤ) :
    (homogeneous x cs : ℝ) = (2 : ℝ) ^ (x.shift * cs.length) * (coefficientPolynomial cs).eval
      x.value := by
  induction cs with
  | nil => simp [homogeneous, dyadicHorner, coefficientPolynomial]
  | cons a as ih =>
    change (↑((a <<< (x.shift * (as.length + 1))) + x.numer * homogeneous x as) : ℝ) = _
    rw [Int.shiftLeft_eq]
    push_cast
    rw [ih]
    simp only [List.length_cons, coefficientPolynomial, eval_add, eval_C, eval_mul, eval_X,
      Dyadic.value]
    rw [Nat.mul_succ, pow_add]
    have hd : (2 : ℝ) ^ x.shift ≠ 0 := by positivity
    field_simp

/-- Check a prescribed strict sign using only integer arithmetic. -/
def positiveAt (negative : Bool) (cs : List ℤ) (x : Dyadic) : Bool :=
  if negative then decide (homogeneous x cs < 0) else decide (0 < homogeneous x cs)

/-- The integer sign checker has exactly the prescribed real-evaluation meaning. -/
theorem positiveAt_iff (negative : Bool) (cs : List ℤ) (x : Dyadic) :
    positiveAt negative cs x = true ↔
      if negative then (coefficientPolynomial cs).eval x.value < 0 else 0 <
        (coefficientPolynomial cs).eval x.value := by
  have hp : 0 < (2 : ℝ) ^ (x.shift * cs.length) := by positivity
  cases negative <;> simp only [positiveAt, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  · rw [← Int.cast_pos (R := ℝ), homogeneous_eq_eval]
    exact mul_pos_iff_of_pos_left hp
  · rw [← Int.cast_lt (R := ℝ), Int.cast_zero, homogeneous_eq_eval]
    exact ⟨fun h ↦ (mul_neg_iff.mp h).elim (fun H ↦ H.2)
      (fun H ↦ ((not_lt_of_ge hp.le) H.1).elim), mul_neg_of_pos_of_neg hp⟩

/-- An ascending list bounds its polynomial degree by one less than its length. -/
theorem natDegree_coefficientPolynomial_le (cs : List ℤ) : (coefficientPolynomial cs).natDegree
  ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a as ih =>
    cases as with
    | nil => simp [coefficientPolynomial]
    | cons b bs =>
      rw [coefficientPolynomial]
      apply (natDegree_add_le _ _).trans
      rw [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
      have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := coefficientPolynomial (b :: bs))
      simp only [natDegree_X, List.length_cons] at h ih ⊢
      lia

/-- Check the signs, strict order, and negative location of a complete quotient grid. -/
def negativeMesh (cs : List ℤ) (nodes : Array Dyadic) : Bool :=
  decide (0 < nodes.size ∧ nodes.size = cs.length) &&
  positiveAt false cs Dyadic.zero &&
  (List.range nodes.size).all (fun i ↦
    (nodes.getD i Dyadic.zero).less Dyadic.zero &&
      positiveAt (decide ((nodes.size - 1 - i) % 2 = 1)) cs
        (nodes.getD i Dyadic.zero)) &&
  (List.range (nodes.size - 1)).all (fun i ↦
    (nodes.getD i Dyadic.zero).less (nodes.getD (i + 1) Dyadic.zero))

/-- A successful grid check makes the quotient positive at zero. -/
theorem negativeMesh_eval_zero_pos {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) : 0 < (coefficientPolynomial cs).eval 0 := by
  have hz := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2
  simpa only [Bool.false_eq_true, ite_false, Dyadic.value_zero] using
    (positiveAt_iff false cs Dyadic.zero).mp hz

/-- Every checked grid value has the prescribed alternating strict sign. -/
theorem negativeMesh_sign {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) {i : ℕ} (hi : i < nodes.size) :
    if (nodes.size - 1 - i) % 2 = 1 then
      (coefficientPolynomial cs).eval (nodes.getD i Dyadic.zero).value < 0 else
      0 < (coefficientPolynomial cs).eval (nodes.getD i Dyadic.zero).value := by
  have values := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have sign := (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp values i (List.mem_range.mpr hi))).2
  simpa only [decide_eq_true_eq] using (positiveAt_iff _ _ _).mp sign

/-- The number of checked nodes equals the coefficient-list length and is positive. -/
theorem negativeMesh_size {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) : 0 < nodes.size ∧ nodes.size = cs.length := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1

/-- Every checked mesh node lies strictly to the left of zero. -/
theorem negativeMesh_node_neg {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) {i : ℕ} (hi : i < nodes.size) :
    (nodes.getD i Dyadic.zero).value < 0 := by
  have values := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have neg := (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp values i (List.mem_range.mpr hi))).1
  simpa only [Dyadic.value_zero] using (Dyadic.less_iff _ _).mp neg

/-- A checked mesh is strictly increasing when indexed by the interval endpoints. -/
theorem negativeMesh_strictMono {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) :
    StrictMono (fun i : Fin (nodes.size - 1 + 1) ↦
      (nodes.getD i.val Dyadic.zero).value) := by
  have order := (Bool.and_eq_true_iff.mp h).2
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact (Dyadic.less_iff _ _).mp
    (List.all_eq_true.mp order i.val (List.mem_range.mpr i.isLt))

/-- Alternating strict signs on the dyadic grid give opposite signs across every gap. -/
theorem eval_mul_eval_neg_of_alternating_signs {p : ℝ[X]} {nodes : Array Dyadic}
    (sign : ∀ i < nodes.size, if (nodes.size - 1 - i) % 2 = 1 then
      p.eval (nodes.getD i Dyadic.zero).value < 0 else
      0 < p.eval (nodes.getD i Dyadic.zero).value) (i : Fin (nodes.size - 1)) :
    p.eval (nodes.getD i.val Dyadic.zero).value *
      p.eval (nodes.getD (i.val + 1) Dyadic.zero).value < 0 := by
  have hi := i.isLt
  have a := sign i.val (by lia)
  have b := sign (i.val + 1) (by lia)
  by_cases parity : (nodes.size - 1 - i.val) % 2 = 1
  · have next : (nodes.size - 1 - (i.val + 1)) % 2 ≠ 1 := by lia
    rw [ite_eq_left parity] at a
    rw [ite_eq_right next] at b
    exact mul_neg_of_neg_of_pos a b
  · have next : (nodes.size - 1 - (i.val + 1)) % 2 = 1 := by lia
    rw [ite_eq_right parity] at a
    rw [ite_eq_left next] at b
    exact mul_neg_of_pos_of_neg a b

/-- A checked quotient has exactly one root in each open interval of the common grid. -/
theorem negativeMesh_ordered_roots {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) :
    ∃ r : Fin (nodes.size - 1) → ℝ, StrictMono r ∧
      (∀ i, (nodes.getD i.val Dyadic.zero).value < r i ∧
        r i < (nodes.getD (i.val + 1) Dyadic.zero).value ∧
        (coefficientPolynomial cs).IsRoot (r i)) ∧
      ∀ z ∈ (coefficientPolynomial cs).roots, ∃ i, z = r i := by
  have pos := negativeMesh_eval_zero_pos h
  have nonzero : coefficientPolynomial cs ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at pos
    exact lt_irrefl _ pos
  exact (Polynomial.splits_nodup_ordered_roots_of_strict_sign_changes nonzero
    ((natDegree_coefficientPolynomial_le cs).trans_eq
      (congrArg (· - 1) (negativeMesh_size h).2.symm)) _
    (negativeMesh_strictMono h) (eval_mul_eval_neg_of_alternating_signs (fun _ hi ↦
      negativeMesh_sign h hi))).2

/-- A sound sign grid yields all simple negative roots of its quotient polynomial. -/
theorem negativeMesh_splits {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) :
    (coefficientPolynomial cs).natDegree = nodes.size - 1 ∧
      (coefficientPolynomial cs).Splits ∧ (coefficientPolynomial cs).roots.Nodup ∧
      ∀ z ∈ (coefficientPolynomial cs).roots, z < 0 := by
  have pos := negativeMesh_eval_zero_pos h
  have nonzero : coefficientPolynomial cs ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at pos
    exact lt_irrefl _ pos
  have result := Polynomial.splits_nodup_roots_of_strict_sign_changes nonzero
    ((natDegree_coefficientPolynomial_le cs).trans_eq
      (congrArg (· - 1) (negativeMesh_size h).2.symm)) _
    (negativeMesh_strictMono h) (eval_mul_eval_neg_of_alternating_signs (fun _ hi ↦
      negativeMesh_sign h hi))
  refine ⟨result.1, result.2.1, result.2.2.1, ?_⟩
  intro z hz
  exact (result.2.2.2 z hz).2.trans
    (negativeMesh_node_neg h (Nat.sub_lt (negativeMesh_size h).1 (by decide)))

end RealRooted.LongCycleDescents.Necklace
