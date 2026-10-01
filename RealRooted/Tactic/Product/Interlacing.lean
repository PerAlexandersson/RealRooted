import RealRooted.ProductSequence.Interlacing
import RealRooted.QuadraticRoot
import Mathlib.Tactic.ComputeDegree

/-!
# Tactics for product sequences

For a sequence defined by a product recurrence

```lean
def P : ℕ → ℝ[X]
  | 0 => base
  | n + 1 => (linear factor, possibly depending on n) * P n
```

* `rr_product_interlaces` closes `Interlaces (P n) (P (n + 1))`;
* `rr_product_natDegree` closes `(P n).natDegree = d`, where `d` simplifies to
  `(base).natDegree + n`.

The tactics read `P` off the goal, let `rfl` infer the linear factor from the
definition, prove the factor has degree one with `compute_degree!`, and prove the
base row is nonzero and splits by `simp [P]`, falling back to `Splits.one` and
`Splits.of_natDegree_le_one`.  They are backed by
`RealRooted.productSequence_interlaces` and `RealRooted.productSequence_natDegree`,
which need no sign conditions on the factors.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted

/-- A degree-two real polynomial with nonnegative discriminant splits. -/
theorem splits_of_natDegree_eq_two_of_discrim_nonneg {p : ℝ[X]} (h : p.natDegree = 2)
    (hd : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)) : p.Splits := by
  have ha : p.coeff 2 ≠ 0 := by
    have := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt (n := 0)
      (by rw [h]; norm_num))
    rwa [Polynomial.leadingCoeff, h] at this
  have hp : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    ext n
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    rcases n with _ | _ | _ | n
    · simp
    · simp
    · simp
    · simp only [Nat.reduceEqDiff, ↓reduceIte, mul_zero, add_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [h]; lia)
  rw [hp]
  exact quadraticPoly_splits_of_discrim_nonneg ha hd

end RealRooted

namespace RealRooted.Tactic

/-- Is `c` a constant of type `ℕ → ℝ[X]`? -/
def isPolySeqConst (c : Name) (us : List Level) : MetaM Bool := do
  let ty ← whnfR (← inferType (.const c us))
  match ty with
  | .forallE _ dom body _ =>
      return dom.isConstOf ``Nat && !body.hasLooseBVars &&
        (← whnfR body).getAppFn.isConstOf ``Polynomial
  | _ => return false

/-- The first constant `P : ℕ → ℝ[X]` applied to an argument in `e`. -/
partial def findPolySeqConst? (e : Expr) : MetaM (Option Name) := do
  match e with
  | .app (.const c us) a =>
      if ← isPolySeqConst c us then return some c else findPolySeqConst? a
  | .app f a =>
      if let some r ← findPolySeqConst? f then return some r
      findPolySeqConst? a
  | .mdata _ b => findPolySeqConst? b
  | _ => return none

/-- Discharge the side goals of the product-sequence theorems.

Every alternative ends in `done` and avoids nested `by` blocks, which would
recover from errors and make `first` commit to a failing branch. -/
def productSideGoals (P : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| all_goals first
    | (intro k; beta_reduce; compute_degree!; done)
    | (intro k; beta_reduce; compute_degree <;>
        first
          | (lia; done)
          | (norm_num; done)
          | (refine ne_of_gt ?_; positivity)
          | (refine ne_of_lt ?_; nlinarith [sq_nonneg ((k : ℝ) + 1)])
          | (intro h; nlinarith [sq_nonneg ((k : ℝ) + 1), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
          | (simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
             refine ⟨?_, ?_⟩ <;> (intro h; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
          | (field_simp; intro h; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
    | (simp [$P:ident]; done)
    | (simp only [$P:ident]; exact Polynomial.Splits.one)
    | (simp only [$P:ident]; refine Polynomial.Splits.of_natDegree_le_one ?_
       compute_degree!; done)
    | (simp only [$P:ident]
       refine RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg ?_ ?_
       · compute_degree!; done
       · simp [discrim, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
         try norm_num
         done)
    | (simp only [$P:ident]; intro h
       have h' := congrArg (fun p : ℝ[X] => p.coeff 0) h
       simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow] at h'; done)
    | fail "rr_product: could not discharge a side goal \
        (factor degree, or base row nonzero / splits)"))

elab "rr_product_interlaces" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt
    | throwError "rr_product_interlaces: no sequence `P : ℕ → ℝ[X]` found in the goal"
  let Pid := mkIdent P
  evalTactic (← `(tactic|
    refine RealRooted.productSequence_interlaces (P := $Pid) ?_ ?_ ?_ (fun _ => rfl) _))
  productSideGoals Pid

elab "rr_product_natDegree" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some P ← findPolySeqConst? tgt
    | throwError "rr_product_natDegree: no sequence `P : ℕ → ℝ[X]` found in the goal"
  let Pid := mkIdent P
  evalTactic (← `(tactic|
    rw [RealRooted.productSequence_natDegree (P := $Pid) ?_ ?_ ?_ (fun _ => rfl)]))
  -- close the main degree goal `(P 0).natDegree + n = rhs`, trying base degrees `0, …, 6`
  evalTactic (← `(tactic| first
    | (have hbase : ($Pid 0).natDegree = 0 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)
    | (have hbase : ($Pid 0).natDegree = 1 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)
    | (have hbase : ($Pid 0).natDegree = 2 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)
    | (have hbase : ($Pid 0).natDegree = 3 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)
    | (have hbase : ($Pid 0).natDegree = 4 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)
    | (have hbase : ($Pid 0).natDegree = 5 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)
    | (have hbase : ($Pid 0).natDegree = 6 :=
          (by simp only [$Pid:ident]; first | rfl | (simp; done) | (compute_degree!; done) | fail)
       rw [hbase]; first | lia | ring | simp)))
  productSideGoals Pid

end RealRooted.Tactic
