module

public import RealRooted.BasisTransform
public import RealRooted.Hadamard.Basic
public import RealRooted.DerivativeRecurrence.FiniteLagCoefficients
public import RealRooted.Tactic.SideGoals
public import RealRooted.Tactic.Recurrence.RowSide

/-!
# Coefficient positivity from recurrences and polynomial operations

Pair the derivative and multiplication summands at each lag, then propagate
nonnegative coefficients together with an affine degree envelope. Rational probes
choose the envelope only; every degree and sign obligation is proved symbolically.
The same certificate feeds structural closure rules for polynomial operations and
coefficient-weighted finite sums. No named polynomial family is recognized.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Select an affine degree envelope from exact samples of the multipliers and base rows.
The returned numbers are candidates; the generated theorem application checks all indices. -/
private def coefficientEnvelope (L : LinRecData) : MetaM (Nat × Nat) := do
  let mut d := 0
  for (j, i, c) in L.sampleTerms do
    for n in [0:3] do
      let some a ← evalCoeffAt? c n | throwError "cannot sample a recurrence multiplier"
      let gap := L.offset - j
      d := max d ((a.natDegree - i + gap - 1) / gap)
  let some base ← linRecBaseRowsOf? L | throwError "cannot sample initial rows"
  let mut D := 0
  for j in [0:base.size] do
    D := max D (base[j]!.natDegree - d * j)
  return (D, d)

/-- Group all multiplier expressions of derivative order `order` by their row lag. -/
private def pairedCoefficients (L : LinRecData) (order : Nat) : TacticM Term := do
  let n := mkIdent `rr_n
  let j := mkIdent `rr_j
  let mut body : Term ← `(0)
  for lag in (List.range L.offset).reverse do
    let mut summand : Term ← `(0)
    for (l, i, c) in L.terms do
      if l == lag && i == order then
        let c ← certTerm c
        summand ← `($summand + ($c) $n)
    body ← `(if $j = $(rowNumLit lag) then $summand else $body)
  `(fun ($n : ℕ) ($j : ℕ) => ($body : ℝ[X]))

/-- Discharge the coefficient-multiplier inequalities after splitting the finite lags.
Natural-number bounds are retained over the reals for linear and polynomial arithmetic. -/
elab (name := rrRowCoefficientMultipliers) "rr_row_coefficient_multipliers" : tactic => do
  evalTactic (← `(tactic| (
    intro n j hj i r hr
    have hr' := (Nat.cast_le (α := ℝ)).mpr hr
    interval_cases j <;>
      simp only [ite_true, ite_false, Nat.reduceEqDiff, zero_add, add_zero,
        Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
        Polynomial.coeff_zero, Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat,
        Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ] <;>
      norm_num <;>
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
        Nat.cast_one, zero_add, one_mul] at hr' <;>
      split_ifs <;> first | positivity | (exfalso; lia) | nlinarith)))

/-- Build the shared coefficient certificate for a finite-lag differential recurrence. -/
private def coefficientRowNonnegTerm : TacticM Term := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let p ← match tgt.getAppFnArgs with
    | (``RealRooted.HasNonnegCoeffs, #[p]) => pure p
    | (``RealRooted.HasPosLeadingCoeff, #[p]) => pure p
    | (``LT.lt, #[_, _, _, rhs]) =>
      unless rhs.isAppOf ``Polynomial.leadingCoeff do
        throwError "expected a leading-coefficient goal"
      pure rhs.appArg!
    | _ => throwError "expected a polynomial coefficient sign goal"
  let p := (← Core.betaReduce p).consumeMData
  let some f ← findPolySeqApp? p | throwError "no polynomial family in the goal"
  unless p.getAppFn.isConstOf f.name && p.getAppArgs.size == f.params.size + 1 do
    throwError "decompose the polynomial operation before certifying its recurrence"
  let some L ← linRec? f.name f.params | throwError "no linear recurrence"
  unless L.offset > 0 && L.terms.all (fun t => t.2.1 ≤ 1) do
    throwError "expected a finite-lag recurrence with at most first derivatives"
  let (D, d) ← coefficientEnvelope L
  let P ← certTerm (mkAppN (← mkConstWithFreshMVarLevels f.name) f.params)
  let eqn ← certTerm (mkAppN (← mkConstWithFreshMVarLevels L.eqn) f.params)
  let A ← pairedCoefficients L 1
  let B ← pairedCoefficients L 0
  let degree ← `(fun n : ℕ => $(rowNumLit D) + $(rowNumLit d) * n)
  let recProof ← `(by
    intro n
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    solve
    | rw [$eqn:term]
    | (rw [$eqn:term]; rr_row_unfold)
    | (rw [$eqn:term]; rr_row_unfold; norm_num)
    | (rw [$eqn:term]; rr_row_unfold; norm_num; ring1))
  let bounds ← `(by
    intro n j hj
    interval_cases j <;> norm_num <;> compute_degree!)
  let constant ← `(by
    intro n j hj
    interval_cases j <;> norm_num <;> positivity)
  let multipliers ← `(by rr_row_coefficient_multipliers)
  let base ← `(by
    intro j hj
    interval_cases j <;> constructor <;>
      simp only [$(mkIdent f.name):ident] <;>
      rr_row_unfold <;> first | compute_degree! | rr_nonneg_coeffs)
  `((RealRooted.LinRec.natDegree_le_and_hasNonnegCoeffs
      (P := $P) (k := $(rowNumLit L.offset)) (D := $degree) (A := $A) (B := $B)
      $recProof (by intro n j hj; lia) $bounds $bounds $constant $multipliers
      $base _).2)

/-- Prove coefficient nonnegativity by structural closure, with bounded recursive search. -/
syntax (name := rrRowCoefficientClosure) "rr_row_coefficient_closure " num : tactic

/-- Prove scalar nonnegativity, allowing coefficients of recursively certified polynomials. -/
syntax (name := rrRowScalarCoefficientClosure) "rr_row_scalar_coefficient_closure " num : tactic

/-- Apply polynomial closure lemmas and the shared finite-lag recurrence certificate.
The depth bound controls syntax traversal, not the number of rows checked. -/
private partial def coefficientClosure (fuel : Nat) : TacticM Unit := withMainContext do
  if ← rowSucceeds (do
      evalTactic (← `(tactic| rr_nonneg_coeffs))
      evalTactic (← `(tactic| done))) then return
  let recurrence ← rowAttempt do
    let proof ← coefficientRowNonnegTerm
    evalTactic (← `(tactic| exact $proof))
  match recurrence with
  | .ok _ => return
  | .error message => trace[rr.row] "coefficient recurrence: {message}"
  if fuel == 0 then throwError "coefficient closure depth exhausted"
  let f := Syntax.mkNumLit (toString (fuel - 1))
  let target ← instantiateMVars (← getMainTarget)
  let (``RealRooted.HasNonnegCoeffs, #[p]) := target.getAppFnArgs
    | throwError "expected nonnegative coefficients"
  let op := if p.isAppOfArity ``DFunLike.coe 6 then p.getAppArgs[4]! else p
  let alternatives ← pure #[
    (op.isAppOf ``Polynomial.C,
      ← `(tactic| (apply RealRooted.hasNonnegCoeffs_C; rr_row_scalar_coefficient_closure $f))),
    (op.isAppOf ``Polynomial.monomial, ← `(tactic| (
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      exact RealRooted.hasNonnegCoeffs_C_mul
        (by rr_row_scalar_coefficient_closure $f) (by rr_nonneg_coeffs)))),
    (p.isAppOf ``Finset.sum, ← `(tactic| (
      apply RealRooted.hasNonnegCoeffs_finsetSum
      intro i hi
      rr_row_coefficient_closure $f))),
    (p.isAppOf ``RealRooted.hadamardProduct,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.hadamardProduct <;>
        rr_row_coefficient_closure $f))),
    (p.isAppOf ``RealRooted.schurSzegoComp,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.schurSzegoComp <;>
        rr_row_coefficient_closure $f))),
    (p.isAppOf ``Polynomial.basisTransform,
      ← `(tactic| exact RealRooted.HasNonnegCoeffs.basisTransform
        (by rr_row_coefficient_closure $f) (by intro k; rr_row_coefficient_closure $f))),
    (p.isAppOf ``HAdd.hAdd,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.add <;> rr_row_coefficient_closure $f))),
    (p.isAppOf ``HMul.hMul,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.mul <;> rr_row_coefficient_closure $f))),
    (p.isAppOf ``HPow.hPow,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.pow; rr_row_coefficient_closure $f))),
    (op.isAppOf ``Polynomial.derivative,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.derivative; rr_row_coefficient_closure $f))),
    (p.isAppOf ``Polynomial.reflect,
      ← `(tactic| (apply RealRooted.HasNonnegCoeffs.reflect; rr_row_coefficient_closure $f)))]
  for (applicable, alt) in alternatives do
    if applicable then
      evalTactic alt
      return
  if p.isAppOf ``Polynomial.reverse then
    let q ← certTerm p.getAppArgs.back!
    evalTactic (← `(tactic| (
      change RealRooted.HasNonnegCoeffs (Polynomial.reflect ($q).natDegree $q)
      exact RealRooted.HasNonnegCoeffs.reflect (by rr_row_coefficient_closure $f) _)))
    return
  unless (← rowCoeffDefs target).isEmpty do
    evalTactic (← `(tactic| rr_row_unfold))
    unless (← getGoals).isEmpty do coefficientClosure (fuel - 1)
    return
  throwError "no coefficient closure rule"

/-- Combine ordinary scalar positivity with coefficient extraction and arithmetic closure. -/
private partial def scalarCoefficientClosure (fuel : Nat) : TacticM Unit :=
    withMainContext do
  if ← rowSucceeds (do
      evalTactic (← `(tactic| rr_side_nonneg))
      evalTactic (← `(tactic| done))) then return
  if fuel == 0 then throwError "scalar coefficient closure depth exhausted"
  let f := Syntax.mkNumLit (toString (fuel - 1))
  let target ← instantiateMVars (← getMainTarget)
  let (``LE.le, #[_, _, _, rhs]) := target.getAppFnArgs
    | throwError "expected scalar nonnegativity"
  let coefficient := if rhs.isAppOfArity ``DFunLike.coe 6 then
      rhs.getAppArgs[4]! else rhs
  if coefficient.isAppOf ``Polynomial.coeff then
    let p ← certTerm coefficient.getAppArgs.back!
    let k ← certTerm rhs.getAppArgs.back!
    let step ← `(tactic| exact (show RealRooted.HasNonnegCoeffs ($p : ℝ[X]) from
      by rr_row_coefficient_closure $f) $k)
    evalTactic step
    return
  let alternatives ← pure #[
    (rhs.isAppOf ``HMul.hMul,
      ← `(tactic| (apply mul_nonneg <;> rr_row_scalar_coefficient_closure $f))),
    (rhs.isAppOf ``HDiv.hDiv,
      ← `(tactic| (apply div_nonneg <;> rr_row_scalar_coefficient_closure $f))),
    (rhs.isAppOf ``HAdd.hAdd,
      ← `(tactic| (apply add_nonneg <;> rr_row_scalar_coefficient_closure $f))),
    (rhs.isAppOf ``Finset.sum,
      ← `(tactic| (apply Finset.sum_nonneg; intro i hi; rr_row_scalar_coefficient_closure $f)))]
  for (applicable, alt) in alternatives do
    if applicable then
      evalTactic alt
      return
  unless (← rowCoeffDefs target).isEmpty do
    evalTactic (← `(tactic| rr_row_unfold))
    unless (← getGoals).isEmpty do scalarCoefficientClosure (fuel - 1)
    return
  throwError "no scalar coefficient closure rule"

elab_rules : tactic
  | `(tactic| rr_row_coefficient_closure $f:num) => coefficientClosure f.getNat
  | `(tactic| rr_row_scalar_coefficient_closure $f:num) => scalarCoefficientClosure f.getNat

/-- Prove positive leading coefficient from nonnegative coefficients and a nonzero premise.
The coefficient certificate uses general recurrence and polynomial closure lemmas. -/
def coefficientRowLeadingCoeff : TacticM Cert := withMainContext do
  let direct ← rowAttempt do
    let proof ← coefficientRowNonnegTerm
    let cert ← `(tactic| exact ($proof).pos_leadingCoeff (by assumption))
    evalTactic cert
    return #[cert]
  if let .ok cert := direct then return cert
  let cert ← `(tactic| exact RealRooted.HasNonnegCoeffs.pos_leadingCoeff
    (by rr_row_coefficient_closure 16) (by assumption))
  evalTactic cert
  return #[cert]

end RealRooted.Tactic
