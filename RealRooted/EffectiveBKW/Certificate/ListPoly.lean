module

public import RealRooted.CombinatorialExamples.BigDescents321.SmallCases.ListPoly
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Integer lists for effective BKW certificates

We reuse the checked arithmetic from `BigDescents321.SmallCases.ListPoly`.
Rational endpoints are unreduced integer/natural pairs; all checkers validate the
positive denominator. Coefficients are in ascending order.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open Polynomial
open BigDescents321.SmallCases

/-- A rational endpoint, whose denominator is validated by the consuming checker. -/
structure QNum where
  /-- Numerator. -/
  num : ℤ
  /-- Denominator. -/
  den : ℕ
  deriving DecidableEq, Repr

/-- The real value of a rational endpoint. -/
noncomputable def QNum.val (q : QNum) : ℝ := q.num / q.den

/-- A valid denominator. -/
def QNum.valid (q : QNum) : Bool := decide (0 < q.den)

/-- Rational comparison without division. -/
def QNum.lt (a b : QNum) : Bool := decide (a.num * b.den < b.num * a.den)

/-- Rational weak comparison without division. -/
def QNum.le (a b : QNum) : Bool := decide (a.num * b.den ≤ b.num * a.den)

/-- Soundness of strict rational comparison. -/
theorem QNum.lt_sound {a b : QNum} (ha : a.valid = true) (hb : b.valid = true)
    (h : a.lt b = true) : a.val < b.val := by
  have ha' : (0 : ℝ) < a.den := by exact_mod_cast (of_decide_eq_true ha : 0 < a.den)
  have hb' : (0 : ℝ) < b.den := by exact_mod_cast (of_decide_eq_true hb : 0 < b.den)
  apply (div_lt_div_iff₀ ha' hb').mpr
  exact_mod_cast (of_decide_eq_true h : a.num * b.den < b.num * a.den)

/-- Soundness of weak rational comparison. -/
theorem QNum.le_sound {a b : QNum} (ha : a.valid = true) (hb : b.valid = true)
    (h : a.le b = true) : a.val ≤ b.val := by
  have ha' : (0 : ℝ) < a.den := by exact_mod_cast (of_decide_eq_true ha : 0 < a.den)
  have hb' : (0 : ℝ) < b.den := by exact_mod_cast (of_decide_eq_true hb : 0 < b.den)
  apply (div_le_div_iff₀ ha' hb').mpr
  exact_mod_cast (of_decide_eq_true h : a.num * b.den ≤ b.num * a.den)

/-- Integer coefficients, constant coefficient first. -/
abbrev IntPoly := List ℤ

namespace IntPoly

/-- Interpret an integer coefficient list as a real polynomial. -/
noncomputable def polynomial (p : IntPoly) : ℝ[X] := ofList p

/-- Real evaluation. -/
noncomputable def eval (p : IntPoly) (x : ℝ) : ℝ := p.polynomial.eval x

/-- Evaluation commutes with the reused list addition. -/
theorem eval_addList (p q : IntPoly) (x : ℝ) :
    eval (addList p q) x = p.eval x + q.eval x := by
  simp [eval, polynomial, ofList_addList]

/-- Evaluation commutes with the reused list multiplication. -/
theorem eval_mulList (p q : IntPoly) (x : ℝ) :
    eval (mulList p q) x = p.eval x * q.eval x := by
  simp [eval, polynomial, ofList_mulList]

/-- Integer Horner evaluation, scaled by `den ^ p.length`. -/
def evalScaled : IntPoly → ℤ → ℕ → ℤ
  | [], _, _ => 0
  | a :: p, num, den => a * (den : ℤ) ^ (p.length + 1) + num * evalScaled p num den

/-- The scaling in integer Horner evaluation is positive at valid endpoints. -/
theorem evalScaled_eq (p : IntPoly) (q : QNum) (hq : q.valid = true) :
    (p.evalScaled q.num q.den : ℝ) = (q.den : ℝ) ^ p.length * p.eval q.val := by
  have hd : (q.den : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (of_decide_eq_true hq : 0 < q.den))
  induction p with
  | nil => simp [evalScaled, eval, polynomial]
  | cons a p ih =>
    simp only [evalScaled, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      List.length_cons, ih, eval, polynomial, ofList_cons, eval_add, eval_C, eval_mul,
      eval_X, QNum.val, pow_succ]
    field_simp

/-- A zero test that tolerates trailing zero coefficients. -/
def eqCheck (p q : IntPoly) : Bool := (addList p (q.map (-1 * ·))).all (· == 0)

private theorem ofList_eq_zero_of_all {p : IntPoly} (h : p.all (· == 0) = true) :
    (ofList p : ℝ[X]) = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [ofList_cons, h.1, ih h.2]

/-- Integer-list equality checks imply polynomial equality. -/
theorem eqCheck_sound {p q : IntPoly} (h : p.eqCheck q = true) :
    p.polynomial = q.polynomial := by
  have hz := ofList_eq_zero_of_all h
  rw [ofList_addList, ofList_map_mul] at hz
  simpa [polynomial] using eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hz)

/-- Multiplication by an integer. -/
def scale (a : ℤ) (p : IntPoly) : IntPoly := p.map (a * ·)

/-- Evaluation commutes with integer scaling. -/
theorem eval_scale (a : ℤ) (p : IntPoly) (x : ℝ) :
    (scale a p).eval x = a * p.eval x := by
  simp [scale, eval, polynomial, ofList_map_mul]

/-- Powers using the existing checked multiplication. -/
def pow (p : IntPoly) : ℕ → IntPoly
  | 0 => [1]
  | n + 1 => mulList p (pow p n)

/-- Evaluation commutes with list powers. -/
theorem eval_pow (p : IntPoly) (n : ℕ) (x : ℝ) :
    (p.pow n).eval x = p.eval x ^ n := by
  induction n with
  | zero => simp [pow, eval, polynomial, ofList_singleton]
  | succ n ih =>
    simp only [pow, eval, polynomial, ofList_mulList, eval_mul] at *
    rw [ih, pow_succ']

/-- The derivative coefficient list, with its current exponent. -/
def derivativeFrom : ℕ → IntPoly → IntPoly
  | _, [] => []
  | n, a :: p => (n : ℤ) * a :: derivativeFrom (n + 1) p

/-- Formal derivative on integer lists. -/
def derivative (p : IntPoly) : IntPoly := derivativeFrom 1 p.tail

end IntPoly

/-- Bivariate coefficients: outer index in `y`, inner index in `t`. -/
abbrev IntPoly2 := List IntPoly

namespace IntPoly2

/-- Evaluation of a bivariate integer list. -/
noncomputable def eval : IntPoly2 → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: f, t, y => p.eval t + y * eval f t y

/-- Addition of bivariate integer lists. -/
def add : IntPoly2 → IntPoly2 → IntPoly2
  | [], g => g
  | p :: f, [] => p :: f
  | p :: f, q :: g => addList p q :: add f g

/-- Multiply each coefficient polynomial by a univariate polynomial. -/
def scale (p : IntPoly) (f : IntPoly2) : IntPoly2 := f.map (mulList p)

/-- Multiplication of bivariate integer lists. -/
def mul : IntPoly2 → IntPoly2 → IntPoly2
  | [], _ => []
  | p :: f, g => add (scale p g) ([] :: mul f g)

/-- Evaluation commutes with bivariate addition. -/
theorem eval_add (f g : IntPoly2) (t y : ℝ) :
    (add f g).eval t y = f.eval t y + g.eval t y := by
  induction f generalizing g with
  | nil => simp [add, eval]
  | cons p f ih =>
    cases g with
    | nil => simp [add, eval]
    | cons q g =>
      simp only [add, eval, ih, IntPoly.eval, IntPoly.polynomial, ofList_addList,
        Polynomial.eval_add]
      ring

/-- Evaluation commutes with multiplication of coefficient polynomials. -/
theorem eval_scale (p : IntPoly) (f : IntPoly2) (t y : ℝ) :
    (scale p f).eval t y = p.eval t * f.eval t y := by
  induction f with
  | nil => simp [scale, eval]
  | cons q f ih =>
    simp only [scale] at ih
    simp only [scale, List.map_cons, eval, ih, IntPoly.eval, IntPoly.polynomial,
      ofList_mulList, Polynomial.eval_mul]
    ring

/-- Evaluation commutes with bivariate multiplication. -/
theorem eval_mul (f g : IntPoly2) (t y : ℝ) :
    (mul f g).eval t y = f.eval t y * g.eval t y := by
  induction f with
  | nil => simp [mul, eval]
  | cons p f ih =>
    simp only [mul, eval_add, eval_scale, eval, ih, IntPoly.eval, IntPoly.polynomial,
      ofList_nil, Polynomial.eval_zero, zero_add]
    ring

/-- Integer scaling of every coefficient. -/
def smul (a : ℤ) (f : IntPoly2) : IntPoly2 := f.map (IntPoly.scale a)

/-- Bivariate equality test, tolerating trailing zeros in either variable. -/
def eqCheck (f g : IntPoly2) : Bool :=
  (add f (smul (-1) g)).all (fun p => p.eqCheck [])

/-- Evaluation commutes with integer scaling. -/
theorem eval_smul (a : ℤ) (f : IntPoly2) (t y : ℝ) :
    (smul a f).eval t y = a * f.eval t y := by
  induction f with
  | nil => simp [smul, eval]
  | cons p f ih =>
    simp only [smul] at ih
    simp only [smul, List.map_cons, eval, IntPoly.eval_scale, ih]
    ring

/-- Soundness of bivariate equality checks. -/
theorem eqCheck_sound {f g : IntPoly2} (h : eqCheck f g = true) (t y : ℝ) :
    f.eval t y = g.eval t y := by
  have hz : ∀ k : IntPoly2, k.all (fun p => p.eqCheck []) = true → k.eval t y = 0 := by
    intro k hk
    induction k with
    | nil => rfl
    | cons p k ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hk
      have hp := congrArg (Polynomial.eval t) (IntPoly.eqCheck_sound hk.1)
      simp only [IntPoly.polynomial, ofList_nil, Polynomial.eval_zero] at hp
      simp [eval, IntPoly.eval, IntPoly.polynomial, hp, ih hk.2]
  have he := hz _ h
  rw [eval_add, eval_smul] at he
  norm_num only [Int.cast_neg, Int.cast_one] at he
  linarith

end IntPoly2
end RealRooted.EffectiveBKW
