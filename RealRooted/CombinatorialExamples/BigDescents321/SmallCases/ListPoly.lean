import Mathlib.Algebra.Polynomial.Basic

/-!
# Integer coefficient lists as polynomials

A verified shadow of polynomial arithmetic on coefficient lists, used to check large
literal polynomial identities by kernel computation instead of `ring`.

`ofList l` reads `l : List ℤ` as a polynomial, constant term first, in Horner form.
`addList` and `mulList` are computable, and `ofList` turns them into polynomial addition
and multiplication. An identity between polynomial expressions built from `ofList` thus
reduces to an equality of integer lists, which `decide` checks.
-/

open Polynomial

namespace RealRooted.BigDescents321.SmallCases

variable {R : Type*} [CommRing R]

/-- The polynomial with coefficient list `l`, constant term first. -/
noncomputable def ofList : List ℤ → R[X]
  | [] => 0
  | a :: l => C (a : R) + X * ofList l

/-- Coefficientwise sum of coefficient lists. -/
def addList : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addList l m

/-- Product of coefficient lists. -/
def mulList : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l, m => addList (m.map (a * ·)) (0 :: mulList l m)

@[simp]
theorem ofList_nil : (ofList [] : R[X]) = 0 := rfl

theorem ofList_cons (a : ℤ) (l : List ℤ) :
    (ofList (a :: l) : R[X]) = C (a : R) + X * ofList l := rfl

theorem ofList_singleton (a : ℤ) : (ofList [a] : R[X]) = C (a : R) := by
  simp [ofList_cons]

theorem ofList_zero_cons (l : List ℤ) : (ofList (0 :: l) : R[X]) = X * ofList l := by
  simp [ofList_cons]

theorem ofList_replicate_zero (m : ℕ) : (ofList (List.replicate m 0) : R[X]) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, ofList_zero_cons, ih, mul_zero]

theorem ofList_cons_replicate_zero (a : ℤ) (m : ℕ) :
    (ofList (a :: List.replicate m 0) : R[X]) = C (a : R) := by
  rw [ofList_cons, ofList_replicate_zero, mul_zero, add_zero]

theorem ofList_addList (l m : List ℤ) :
    (ofList (addList l m) : R[X]) = ofList l + ofList m := by
  induction l generalizing m with
  | nil => simp [addList]
  | cons a l ih =>
    cases m with
    | nil => simp [addList]
    | cons b m =>
      simp only [addList, ofList_cons, ih, Int.cast_add, C_add]
      ring

theorem ofList_map_mul (a : ℤ) (l : List ℤ) :
    (ofList (l.map (a * ·)) : R[X]) = C (a : R) * ofList l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, ofList_cons, ih, Int.cast_mul, C_mul]
    ring

theorem ofList_mulList (l m : List ℤ) :
    (ofList (mulList l m) : R[X]) = ofList l * ofList m := by
  induction l with
  | nil => simp [mulList]
  | cons a l ih =>
    rw [mulList, ofList_addList, ofList_map_mul, ofList_zero_cons, ih, ofList_cons]
    ring

end RealRooted.BigDescents321.SmallCases
