import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Algebra.Order.Ring.Cast

/-!
# A reflected checker for large polynomial identities

The universal certificate of issue #1143 is an identity between integer polynomials in three
variables with several hundred terms and coefficients of about seventy digits. It is checked
by kernel reduction, using the core normalizer `Lean.Grind.CommRing.Expr.toPoly_k`, whose
soundness theorem `Lean.Grind.CommRing.Expr.denote_toPoly` is proved in core Lean.

* `check l r` is a kernel-reducible Boolean test that `l - r` normalizes to zero, and
  `check_sound` turns `check l r = true` into `l.denote ctx = r.denote ctx` in every
  commutative ring.
* `subst` substitutes expressions for variables, with `denote_subst`.
* `PosB` recognizes expressions built from nonnegative numerals and variables by `+`, `*`
  and `^`; `denote_nonneg` says that they are nonnegative at nonnegative arguments.
* `termsExpr` and `termsFn` turn a list of terms `(a, b, c, z)`, meaning `z R^a X^b k^c`,
  into an expression and into a function.
-/

namespace RealRooted.BigDescents321.Reflect

open Lean.Grind.CommRing

/-- Kernel-reducible Boolean checker: `l - r` normalizes to the zero polynomial. -/
noncomputable def check (l r : Expr) : Bool := (l.sub r).toPoly_k.beq' (.num 0)

/-- Soundness of `check` in any commutative ring. -/
theorem check_sound {α : Type*} [CommRing α] (ctx : Context α) {l r : Expr}
    (h : check l r = true) : l.denote ctx = r.denote ctx := by
  have h' : (l.sub r).toPoly = .num 0 := by simpa [check] using h
  have := Expr.denote_toPoly ctx (l.sub r)
  rw [h'] at this
  simp only [Poly.denote, Expr.denote] at this
  rw [Int.cast_zero] at this
  exact sub_eq_zero.mp this.symm

/-- Substitute the expression `σ i` for each variable `i`. -/
def subst (σ : ℕ → Expr) : Expr → Expr
  | .num k => .num k
  | .natCast k => .natCast k
  | .intCast k => .intCast k
  | .var i => σ i
  | .neg a => .neg (subst σ a)
  | .add a b => .add (subst σ a) (subst σ b)
  | .sub a b => .sub (subst σ a) (subst σ b)
  | .mul a b => .mul (subst σ a) (subst σ b)
  | .pow a k => .pow (subst σ a) k

theorem denote_subst {α : Type*} [CommRing α] (ctx ctx' : Context α) (σ : ℕ → Expr)
    (hσ : ∀ i, ctx'.get i = (σ i).denote ctx) (e : Expr) :
    (subst σ e).denote ctx = e.denote ctx' := by
  induction e with
  | var i => exact (hσ i).symm
  | neg a ih => simp only [subst, Expr.denote] at *; rw [ih]
  | add a b iha ihb => simp only [subst, Expr.denote] at *; rw [iha, ihb]
  | sub a b iha ihb => simp only [subst, Expr.denote] at *; rw [iha, ihb]
  | mul a b iha ihb => simp only [subst, Expr.denote] at *; rw [iha, ihb]
  | pow a k ih => simp only [subst, Expr.denote] at *; rw [ih]
  | _ => rfl

/-- Syntactic positivity: only nonnegative numerals, variables, `+`, `*` and `^`. -/
def PosB : Expr → Bool
  | .num k => decide (0 ≤ k)
  | .natCast _ => true
  | .var _ => true
  | .add a b => PosB a && PosB b
  | .mul a b => PosB a && PosB b
  | .pow a _ => PosB a
  | _ => false

theorem denote_nonneg {α : Type*} [CommRing α] [PartialOrder α] [IsOrderedRing α]
    (ctx : Context α) (hctx : ∀ i, 0 ≤ ctx.get i) :
    ∀ e : Expr, PosB e = true → 0 ≤ e.denote ctx
  | .num k, h => by
      have hk : 0 ≤ k := by simpa [PosB] using h
      have : Expr.denote ctx (.num k) = (k : α) := denoteInt_eq k
      rw [this]
      exact Int.cast_nonneg hk
  | .natCast k, _ => Nat.cast_nonneg k
  | .var i, _ => hctx i
  | .add a b, h => by
      simp only [PosB, Bool.and_eq_true] at h
      exact add_nonneg (denote_nonneg ctx hctx a h.1) (denote_nonneg ctx hctx b h.2)
  | .mul a b, h => by
      simp only [PosB, Bool.and_eq_true] at h
      exact mul_nonneg (denote_nonneg ctx hctx a h.1) (denote_nonneg ctx hctx b h.2)
  | .pow a k, h => pow_nonneg (denote_nonneg ctx hctx a h) k
  | .neg _, h | .sub _ _, h | .intCast _, h => by simp [PosB] at h

section Denote

variable {α : Type*} [CommRing α]

@[simp] theorem denote_num (ctx : Context α) (z : ℤ) : (Expr.num z).denote ctx = (z : α) :=
  denoteInt_eq z

@[simp] theorem denote_var (ctx : Context α) (i : ℕ) : (Expr.var i).denote ctx = ctx.get i :=
  rfl

@[simp] theorem denote_add (ctx : Context α) (a b : Expr) :
    (Expr.add a b).denote ctx = a.denote ctx + b.denote ctx := rfl

@[simp] theorem denote_sub (ctx : Context α) (a b : Expr) :
    (Expr.sub a b).denote ctx = a.denote ctx - b.denote ctx := rfl

@[simp] theorem denote_mul (ctx : Context α) (a b : Expr) :
    (Expr.mul a b).denote ctx = a.denote ctx * b.denote ctx := rfl

@[simp] theorem denote_pow (ctx : Context α) (a : Expr) (n : ℕ) :
    (Expr.pow a n).denote ctx = a.denote ctx ^ n := rfl

/-- The expression `∑ z r^a x^b k^c` over the terms `(a, b, c, z)` of `l`. -/
def termsExpr (r x k : Expr) (l : List (ℕ × ℕ × ℕ × ℤ)) : Expr :=
  l.foldr (fun t acc ↦ .add (.mul (.num t.2.2.2)
    (.mul (.pow r t.1) (.mul (.pow x t.2.1) (.pow k t.2.2.1)))) acc) (.num 0)

/-- The polynomial function `∑ z R^a X^b k^c` over the terms `(a, b, c, z)` of `l`. -/
def termsFn (l : List (ℕ × ℕ × ℕ × ℤ)) (R X k : α) : α :=
  l.foldr (fun t acc ↦ (t.2.2.2 : α) * (R ^ t.1 * (X ^ t.2.1 * k ^ t.2.2.1)) + acc) 0

theorem termsFn_append (l₁ l₂ : List (ℕ × ℕ × ℕ × ℤ)) (R X k : α) :
    termsFn (l₁ ++ l₂) R X k = termsFn l₁ R X k + termsFn l₂ R X k := by
  induction l₁ with
  | nil => simp [termsFn]
  | cons t l ih =>
    simp only [termsFn, List.cons_append, List.foldr_cons] at *
    rw [ih, add_assoc]

theorem denote_termsExpr (ctx : Context α) (r x k : Expr) (l : List (ℕ × ℕ × ℕ × ℤ)) :
    (termsExpr r x k l).denote ctx =
      termsFn l (r.denote ctx) (x.denote ctx) (k.denote ctx) := by
  induction l with
  | nil => simp [termsExpr, termsFn]
  | cons t l ih =>
    simp only [termsExpr, termsFn, List.foldr_cons] at *
    simp only [denote_add, denote_mul, denote_pow, denote_num, ih]

end Denote

section Context

variable {α : Type*}

/-- The context with variables `0, 1, 2` equal to `R, X, k`. -/
def ctx3 (R X k : α) : Context α := .branch 1 (.leaf R) (.branch 2 (.leaf X) (.leaf k))

/-- The context with variables `0, 1, 2, 3` equal to `S, X, K, T`. -/
def ctx4 (S X K T : α) : Context α :=
  .branch 2 (.branch 1 (.leaf S) (.leaf X)) (.branch 3 (.leaf K) (.leaf T))

@[simp] theorem ctx3_zero (R X k : α) : (ctx3 R X k).get 0 = R := rfl
@[simp] theorem ctx3_one (R X k : α) : (ctx3 R X k).get 1 = X := rfl
@[simp] theorem ctx3_two (R X k : α) : (ctx3 R X k).get 2 = k := rfl

theorem ctx4_get (S X K T : α) (i : ℕ) :
    (ctx4 S X K T).get i = if i = 0 then S else if i = 1 then X else if i = 2 then K else T := by
  rcases i with _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  · have h2 : Nat.ble 2 (i + 1 + 1 + 1) = true := by rw [Nat.ble_eq]; lia
    have h3 : Nat.ble 3 (i + 1 + 1 + 1) = true := by rw [Nat.ble_eq]; lia
    simp only [ctx4, Lean.RArray.get, h2, h3]
    simp

end Context

theorem ctx4_nonneg {α : Type*} [CommRing α] [PartialOrder α] {S X K T : α} (hS : 0 ≤ S)
    (hX : 0 ≤ X) (hK : 0 ≤ K) (hT : 0 ≤ T) (i : ℕ) : 0 ≤ (ctx4 S X K T).get i := by
  rw [ctx4_get]
  split_ifs <;> assumption

end RealRooted.BigDescents321.Reflect
