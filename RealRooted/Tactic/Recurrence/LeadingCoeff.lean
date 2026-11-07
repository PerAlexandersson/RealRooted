module

public import RealRooted.Tactic.Recurrence.RowSide
public import RealRooted.Tactic.SideGoals
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Algebraic leading-coefficient positivity

Decompose polynomial expressions using sum, product, power, composition and derivative laws.
Recurrence tactics handle the factors. Nonnegative leaders allow zero derivative
summands without requiring the entire polynomial to have nonnegative coefficients.
No named polynomial family is used by this route.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Prove a nonnegative leading coefficient by algebraic closure and row positivity. -/
syntax (name := rrRowLeadingCoeffNonneg) "rr_row_leadingCoeff_nonneg" : tactic

/-- Decompose a polynomial expression into smaller leading-coefficient goals.
Only nonrecursive wrappers are unfolded; opaque rows are left to recurrence routes. -/
def algebraRowLeadingCoeff (positive : Bool := true) : TacticM Cert := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let mut p ← match target.getAppFnArgs with
    | (``RealRooted.HasPosLeadingCoeff, #[p]) => pure p
    | (op, #[_, _, _, rhs]) =>
        unless (op == ``LT.lt || op == ``LE.le) && rhs.isAppOf ``Polynomial.leadingCoeff do
          throwError "expected a leading-coefficient sign goal"
        pure rhs.getAppArgs.back!
    | _ => throwError "expected a leading-coefficient sign goal"
  let original := p
  for _ in [:8] do
    let some unfolded ← unfoldRowCoeff? p | break
    p := unfolded
  if p.isAppOf ``ite || p.isAppOf ``dite ||
      (← matchMatcherApp? p (alsoCasesOn := true)).isSome then
    let defs ← rowCoeffDefs target
    let lctx ← getLCtx
    let defs := defs.filter fun name =>
      lctx.any fun decl => decl.type.getUsedConstants.contains name
    let args : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← defs.mapM fun name =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
    let finish ← if positive then `(tactic| rr_row_leadingCoeff_pos)
      else `(tactic| rr_row_leadingCoeff_nonneg)
    let cleanup ← `(tactic| (rr_row_unfold; split <;> simp_all only))
    if ← rowSucceeds (do evalTactic cleanup; evalTactic (← `(tactic| done))) then
      return #[cleanup]
    let simpleCases ← `(tactic|
      (rr_row_unfold; split <;> simp_all only <;> $finish:tactic))
    if ← rowSucceeds (evalTactic simpleCases) then return #[simpleCases]
    let cases ← `(tactic|
      (rr_row_unfold; split <;> simp_all only [$args,*] <;> $finish:tactic))
    if ← rowSucceeds (evalTactic cases) then return #[cases]
  let poly ← certTerm p
  let change ← if positive then
    `(tactic| change 0 < ($poly : Polynomial ℝ).leadingCoeff)
    else `(tactic| change 0 ≤ ($poly : Polynomial ℝ).leadingCoeff)
  evalTactic change
  let monicity ← if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HPow.hPow,
      ``Neg.neg, ``Polynomial.C, ``Polynomial.X].any p.getAppFn.isConstOf then
      `(tactic| first | assumption | monicity!)
    else `(tactic| assumption)
  let basic ← `(tactic|
    first
    | assumption
    | (simp only [Polynomial.leadingCoeff_X, Polynomial.leadingCoeff_one,
        Polynomial.leadingCoeff_zero, Polynomial.leadingCoeff_C, pow_zero,
        Polynomial.leadingCoeff_X_add_C, Polynomial.leadingCoeff_X_sub_C];
        rr_row_unfold; first | positivity | norm_num | assumption)
    | (have hm : ($poly : Polynomial ℝ).Monic := by $monicity:tactic
       rw [hm.leadingCoeff]
       norm_num))
  if ← rowSucceeds (do evalTactic basic; evalTactic (← `(tactic| done))) then
    return #[change, ← `(tactic| ($basic:tactic; done))]
  let nonneg ← if positive then
      `(tactic| exact RealRooted.HasNonnegCoeffs.pos_leadingCoeff
        (by rr_row_unfold; rr_nonneg_coeffs) (by assumption))
    else
      `(tactic| exact (show RealRooted.HasNonnegCoeffs $poly from
        by rr_row_unfold; rr_nonneg_coeffs) _)
  if ← rowSucceeds (evalTactic nonneg) then return #[change, nonneg]
  if let .ok cert ← rowAttempt (explicitPolynomialLeadingCoeff none positive) then
    return cert
  let op := p.getAppFn
  let derivative := op.isConstOf ``Polynomial.derivative ||
    (p.isAppOfArity ``DFunLike.coe 6 &&
      p.getAppArgs[4]!.isAppOf ``Polynomial.derivative)
  if positive && derivative then
    let parent ← certTerm p.getAppArgs.back!
    let nonzeroDerivative ← `(tactic| (
      have hd : ($parent : ℝ[X]).derivative ≠ 0 := by assumption
      have hp : ($parent : ℝ[X]) ≠ 0 := by
        intro h
        exact hd (by simp [h])
      exact RealRooted.HasPosLeadingCoeff.derivative
        (by rr_row_leadingCoeff_pos) (Polynomial.derivative_ne_zero.mp hd)))
    if ← rowSucceeds (evalTactic nonzeroDerivative) then
      return #[change, nonzeroDerivative]
  let step ← if op.isConstOf ``HAdd.hAdd then
      if positive then `(tactic|
        first
        | exact Polynomial.leadingCoeff_add_pos_of_pos_of_nonneg
            (by rr_row_leadingCoeff_pos) (by rr_row_leadingCoeff_nonneg)
        | exact Polynomial.leadingCoeff_add_pos_of_nonneg_of_pos
            (by rr_row_leadingCoeff_nonneg) (by rr_row_leadingCoeff_pos))
      else `(tactic| exact Polynomial.leadingCoeff_add_nonneg
        (by rr_row_leadingCoeff_nonneg) (by rr_row_leadingCoeff_nonneg))
    else if op.isConstOf ``HMul.hMul then
      if positive then `(tactic|
        (rw [Polynomial.leadingCoeff_mul]
         exact mul_pos (by rr_row_leadingCoeff_pos) (by rr_row_leadingCoeff_pos)))
      else `(tactic|
        (rw [Polynomial.leadingCoeff_mul]
         exact mul_nonneg (by rr_row_leadingCoeff_nonneg) (by rr_row_leadingCoeff_nonneg)))
    else if op.isConstOf ``HPow.hPow then
      if positive then `(tactic|
        (rw [Polynomial.leadingCoeff_pow]
         exact pow_pos (by rr_row_leadingCoeff_pos) _))
      else `(tactic|
        (rw [Polynomial.leadingCoeff_pow]
         exact pow_nonneg (by rr_row_leadingCoeff_nonneg) _))
    else if op.isConstOf ``Polynomial.comp then
      let inner ← certTerm p.getAppArgs.back!
      let nonconstant ← match ← explicitPolynomialDegree? p.getAppArgs.back! with
        | some degree => `(by
            first
            | assumption
            | (simp; done)
            | (have hd : ($inner : Polynomial ℝ).natDegree = $(rowNumLit degree) := by
                 compute_degree!; positivity
               rw [hd]
               positivity))
        | none => `(by first | assumption | (simp; done))
      if positive then `(tactic|
        (rw [Polynomial.leadingCoeff_comp $nonconstant]
         exact mul_pos (by rr_row_leadingCoeff_pos)
           (pow_pos (by rr_row_leadingCoeff_pos) _)))
      else `(tactic|
        (rw [Polynomial.leadingCoeff_comp $nonconstant]
         exact mul_nonneg (by rr_row_leadingCoeff_nonneg)
           (pow_nonneg (by rr_row_leadingCoeff_nonneg) _)))
    else if derivative then
      if positive then `(tactic|
        (rw [Polynomial.leadingCoeff_derivative]
         exact mul_pos (by rr_row_leadingCoeff_pos) (by positivity)))
      else `(tactic|
        (rw [Polynomial.leadingCoeff_derivative]
         exact mul_nonneg (by rr_row_leadingCoeff_nonneg) (Nat.cast_nonneg _)))
    else if op.isConstOf ``Finset.prod then
      if positive then `(tactic|
        (rw [Polynomial.leadingCoeff_prod]
         apply Finset.prod_pos; intro i hi; rr_row_leadingCoeff_pos))
      else `(tactic|
        (rw [Polynomial.leadingCoeff_prod]
         apply Finset.prod_nonneg; intro i hi; rr_row_leadingCoeff_nonneg))
    else if !positive then
      `(tactic| exact le_of_lt (by rr_row_leadingCoeff_pos))
    else if p != original then
      `(tactic| rr_row_leadingCoeff_pos)
    else throwError "no algebraic leading-coefficient decomposition"
  evalTactic step
  evalTactic (← `(tactic| done))
  return #[change, step]

elab_rules : tactic
  | `(tactic| rr_row_leadingCoeff_nonneg) => discard <| algebraRowLeadingCoeff false

end RealRooted.Tactic
