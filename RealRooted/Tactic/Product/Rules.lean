module

public import RealRooted.ProductSequence
public import RealRooted.Tactic.Product.Syntax
public meta import RealRooted.ProductSequence
public meta import RealRooted.Tactic.Product.Syntax

/-!
# Product-tactic elaboration and rules

Checked expression inspection and the rules required by the retained lift routers.
These stay in one unit because the routers are heartbeat-sensitive when elaboration
and their dispatch rules are compiled into separate imported environments.
-/

public meta section

open Polynomial
open scoped BigOperators

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

private inductive AffinePowOrientation where
  | mulXFirst
  | constFirst

private inductive ScalarFactorKind where
  | scalar
  | scalarPow

private inductive ProductOrientation where
  | factorLeft
  | factorRight

private inductive LiftAutoShape where
  | X
  | scalar
  | scalarPow
  | XAddC
  | CAddX
  | XPow
  | XAddCPow
  | CAddXPow
  | affineMulXFirst
  | affineConstFirst
  | affinePowMulXFirst
  | affinePowConstFirst

private def appFnName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

private partial def containsAppFn (needle : Name) (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some needle ||
    e.getAppArgs.any (containsAppFn needle) ||
    match e with
    | .forallE _ domain body _ => containsAppFn needle domain || containsAppFn needle body
    | .lam _ domain body _ => containsAppFn needle domain || containsAppFn needle body
    | .letE _ type value body _ =>
        containsAppFn needle type || containsAppFn needle value || containsAppFn needle body
    | .proj _ _ body => containsAppFn needle body
    | _ => false

private def isPolynomialX (e : Expr) : Bool :=
  appFnName? e == some ``Polynomial.X

private def isPolynomialC (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some ``Polynomial.C ||
    (appFnName? e == some ``DFunLike.coe &&
      e.getAppArgs.any (fun arg => appFnName? arg == some ``Polynomial.C))

private def outerMulArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if appFnName? e == some ``HMul.hMul then
    let args := e.getAppArgs
    if args.size > 5 then
      some (args[4]!, args[5]!)
    else
      none
  else
    none

private def outerAddArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if appFnName? e == some ``HAdd.hAdd then
    let args := e.getAppArgs
    if args.size > 5 then
      some (args[4]!, args[5]!)
    else
      none
  else
    none

private def outerPowBase? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 then
      some args[4]!
    else
      none
  else
    none

private def containsPolynomialX (e : Expr) : Bool :=
  containsAppFn ``Polynomial.X e

private def isScalarPolynomialExpr (e : Expr) : Bool :=
  containsAppFn ``Polynomial.C e && !containsPolynomialX e

private def scalarFactorKind? (e : Expr) : Option ScalarFactorKind :=
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 && isScalarPolynomialExpr args[4]! then
      some .scalarPow
    else
      none
  else if isScalarPolynomialExpr e then
    some .scalar
  else
    none

private partial def topMulFactors (e : Expr) : List Expr :=
  let e := e.consumeMData
  if appFnName? e == some ``HMul.hMul then
    let args := e.getAppArgs
    if args.size > 5 then
      topMulFactors args[4]! ++ topMulFactors args[5]!
    else
      [e]
  else
    [e]

private partial def containsAppHead (head : Expr) (e : Expr) : Bool :=
  let e := e.consumeMData
  e.getAppFn == head ||
    e.getAppArgs.any (containsAppHead head) ||
    match e with
    | .forallE _ domain body _ =>
        containsAppHead head domain || containsAppHead head body
    | .lam _ domain body _ =>
        containsAppHead head domain || containsAppHead head body
    | .letE _ type value body _ =>
        containsAppHead head type || containsAppHead head value || containsAppHead head body
    | .proj _ _ body => containsAppHead head body
    | _ => false

private def productOrientationOfEquality? (e : Expr) : Option ProductOrientation :=
  let e := e.consumeMData
  if appFnName? e == some ``Eq then
    let args := e.getAppArgs
    if args.size > 1 then
      let lhs := args[args.size - 2]!
      let rhs := args[args.size - 1]!
      match topMulFactors rhs, (topMulFactors rhs).reverse with
      | first :: _, last :: _ =>
          let sequence := lhs.consumeMData.getAppFn
          if containsAppHead sequence last then
            some .factorLeft
          else if containsAppHead sequence first then
            some .factorRight
          else if containsPolynomialX first || containsAppFn ``Polynomial.C first then
            some .factorLeft
          else if containsPolynomialX last || containsAppFn ``Polynomial.C last then
            some .factorRight
          else
            none
      | _, _ => none
    else
      none
  else
    none

private partial def findProductOrientation? (e : Expr) : Option ProductOrientation := Id.run do
  let e := e.consumeMData
  if let some orientation := productOrientationOfEquality? e then
    return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findProductOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      findProductOrientation? domain <|> findProductOrientation? body
  | .lam _ domain body _ =>
      findProductOrientation? domain <|> findProductOrientation? body
  | .letE _ type value body _ =>
      findProductOrientation? type <|>
        findProductOrientation? value <|> findProductOrientation? body
  | .proj _ _ body => findProductOrientation? body
  | _ => none

private partial def identifierTerms (stx : Syntax) : Array Syntax :=
  if stx.isIdent then
    #[stx]
  else
    stx.getArgs.foldl (fun terms arg => terms ++ identifierTerms arg) #[]

private def productOrientationsOfCandidate (candidate : Syntax) :
    TacticM (List ProductOrientation) :=
  withMainContext do
    let localContext ← getLCtx
    let mut orientations := []
    for term in identifierTerms candidate do
      if let some declaration := localContext.findFromUserName? term.getId then
        let type ← instantiateMVars declaration.type
        if let some orientation := findProductOrientation? type then
          orientations := orientations ++ [orientation]
    pure orientations

private def productOrientationOfCandidate? (candidate : Syntax) :
    TacticM (Option ProductOrientation) := do
  match ← productOrientationsOfCandidate candidate with
  | orientation :: _ => pure (some orientation)
  | [] => pure none

private def scalarKindOfTopProduct? (rhs : Expr) : Option ScalarFactorKind :=
  match topMulFactors rhs with
  | lhsFactor :: rhsFactor :: [] =>
      match scalarFactorKind? lhsFactor, scalarFactorKind? rhsFactor with
      | some kind, none => some kind
      | none, some kind => some kind
      | _, _ => none
  | _ => none

private partial def findScalarTopProductKind? (e : Expr) :
    Option ScalarFactorKind := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``Eq then
    let args := e.getAppArgs
    if args.size > 0 then
      if let some kind := scalarKindOfTopProduct? args[args.size - 1]! then
        return some kind
  match e with
  | .forallE _ _ body _ => findScalarTopProductKind? body
  | .lam _ _ body _ => findScalarTopProductKind? body
  | .letE _ _ value body _ =>
      if let some kind := findScalarTopProductKind? value then
        return some kind
      findScalarTopProductKind? body
  | .proj _ _ body => findScalarTopProductKind? body
  | _ => none

private def isPolynomialCMulX (e : Expr) : Bool :=
  let e := e.consumeMData
  appFnName? e == some ``HMul.hMul &&
    let args := e.getAppArgs
    args.size > 5 &&
      containsAppFn ``Polynomial.C args[4]! &&
      isPolynomialX args[5]!

private def affineOrientationOfBase? (e : Expr) : Option AffinePowOrientation :=
  let e := e.consumeMData
  if appFnName? e == some ``HAdd.hAdd then
    let args := e.getAppArgs
    if args.size > 5 then
      if isPolynomialCMulX args[4]! then
        some .mulXFirst
      else if isPolynomialCMulX args[5]! then
        some .constFirst
      else
        none
    else
      none
  else
    none

private partial def findEqualityRhs? (e : Expr) : Option Expr := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``Eq then
    let args := e.getAppArgs
    if args.size > 1 then
      return some args[args.size - 1]!
  match e with
  | .forallE _ _ body _ =>
      findEqualityRhs? body
  | .letE _ _ value body _ =>
      findEqualityRhs? value <|> findEqualityRhs? body
  | .proj _ _ body =>
      findEqualityRhs? body
  | _ =>
      for arg in e.getAppArgs do
        if let some rhs := findEqualityRhs? arg then
          return some rhs
      none

private partial def findSplitsArgument? (e : Expr) : Option Expr := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``Polynomial.Splits then
    let args := e.getAppArgs
    if args.size > 0 then
      return some args[args.size - 1]!
  match e with
  | .forallE _ _ body _ =>
      findSplitsArgument? body
  | .letE _ _ value body _ =>
      findSplitsArgument? value <|> findSplitsArgument? body
  | .proj _ _ body =>
      findSplitsArgument? body
  | _ =>
      for arg in e.getAppArgs do
        if let some p := findSplitsArgument? arg then
          return some p
      none

/-- Remove the matching pointwise binders from the established lift certificates.

The generic lift-auto router deliberately supports only a single pointwise
certificate pair: `∀ n, ...` or `∀ n, N ≤ n → ...`, with the same binders in
the quotient and row evidence.  The resulting operands retain those aligned
bound variables, so they can be compared syntactically without unfolding or
definitional equality on loose binders. -/
private partial def pointwiseConclusion (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .forallE _ _ body _ => pointwiseConclusion body
  | _ => e

private def sameAlignedOperand (lhs rhs : Expr) : Bool :=
  lhs.consumeMData == rhs.consumeMData

private def outerLiftFactorAndOrientation? (quotient rhs : Expr) :
    Option (Expr × ProductOrientation) :=
  match outerMulArgs? rhs with
  | some (lhs, rhs) =>
      if sameAlignedOperand lhs quotient then
        some (rhs, .factorRight)
      else if sameAlignedOperand rhs quotient then
        some (lhs, .factorLeft)
      else
        none
  | none => none

private def mentionsLiftTheorem (candidate : Syntax) : Bool :=
  (identifierTerms candidate).any fun term =>
    let name := term.getId.toString
    name.startsWith "RealRooted.isRealRooted_of_" && name.contains "_lift_"

/-- Select a lift theorem variant from the exact quotient/row certificate pair.

This only recognizes a lift-theorem candidate containing a pointwise
`Polynomial.Splits` certificate and a row equality with that complete quotient
as an outer product operand. Other product families return `none` and retain
their legacy orientation selector. -/
private def liftProductOrientationOfCandidate? (candidate : Syntax) :
    TacticM (Option ProductOrientation) := do
  if !mentionsLiftTheorem candidate then
    return none
  withMainContext do
    let localContext ← getLCtx
    let mut types := #[]
    for term in identifierTerms candidate do
      if let some declaration := localContext.findFromUserName? term.getId then
        types := types.push (← instantiateMVars declaration.type)
    for quotientType in types do
      if let some quotient := findSplitsArgument? (pointwiseConclusion quotientType) then
        for rowType in types do
          if let some rhs := findEqualityRhs? (pointwiseConclusion rowType) then
            if let some (_, orientation) := outerLiftFactorAndOrientation? quotient rhs then
              return some orientation
    pure none

private def directCMulX? (e : Expr) : Bool :=
  match outerMulArgs? e with
  | some (coefficient, xTerm) => isPolynomialC coefficient && isPolynomialX xTerm
  | none => false

private def directAffineOrientation? (e : Expr) : Option AffinePowOrientation :=
  match outerAddArgs? e with
  | some (lhs, rhs) =>
      if directCMulX? lhs && isPolynomialC rhs then
        some .mulXFirst
      else if isPolynomialC lhs && directCMulX? rhs then
        some .constFirst
      else
        none
  | none => none

private def unitSlopeOrientation? (e : Expr) : Option AffinePowOrientation :=
  match outerAddArgs? e with
  | some (lhs, rhs) =>
      if isPolynomialX lhs && isPolynomialC rhs then
        some .mulXFirst
      else if isPolynomialC lhs && isPolynomialX rhs then
        some .constFirst
      else
        none
  | none => none

private def liftAutoShapeOfFactor? (factor : Expr) : Option LiftAutoShape :=
  let factor := factor.consumeMData
  if isPolynomialX factor then
    some .X
  else if isPolynomialC factor then
    some .scalar
  else if let some orientation := directAffineOrientation? factor then
    match orientation with
    | .mulXFirst => some .affineMulXFirst
    | .constFirst => some .affineConstFirst
  else if let some orientation := unitSlopeOrientation? factor then
    match orientation with
    | .mulXFirst => some .XAddC
    | .constFirst => some .CAddX
  else if let some powBase := outerPowBase? factor then
    if isPolynomialX powBase then
      some .XPow
    else if isPolynomialC powBase then
      some .scalarPow
    else if let some orientation := directAffineOrientation? powBase then
      match orientation with
      | .mulXFirst => some .affinePowMulXFirst
      | .constFirst => some .affinePowConstFirst
    else if let some orientation := unitSlopeOrientation? powBase then
      match orientation with
      | .mulXFirst => some .XAddCPow
      | .constFirst => some .CAddXPow
    else
      none
  else
    none

private def liftAutoShapeOfEvidence (hquot hrow : Syntax) : TacticM LiftAutoShape :=
  withMainContext do
    let quotientEvidence ← Lean.Elab.Tactic.elabTerm hquot none
    let quotientType ← instantiateMVars (← inferType quotientEvidence)
    let quotient ←
      match findSplitsArgument? (pointwiseConclusion quotientType) with
      | some quotient => pure quotient
      | none =>
          throwError
            "rr_product lift auto: could not identify quotient from quotient_realrooted"
    let rowEvidence ← Lean.Elab.Tactic.elabTerm hrow none
    let rowType ← instantiateMVars (← inferType rowEvidence)
    let rhs ←
      match findEqualityRhs? (pointwiseConclusion rowType) with
      | some rhs => pure rhs
      | none =>
          throwError "rr_product lift auto: no row equality found in factorization"
    let factor ←
      match outerMulArgs? rhs with
      | some _ =>
          match outerLiftFactorAndOrientation? quotient rhs with
          | some (factor, _) => pure factor
          | none =>
              throwError
                "rr_product lift auto: factorization does not expose quotient as an outer factor"
      | none =>
          throwError "rr_product lift auto: factorization is not an outer product"
    match liftAutoShapeOfFactor? factor with
    | some shape => pure shape
    | none =>
        throwError "rr_product lift auto: unsupported factor; use explicit factor_realrooted"

private partial def findAffinePowOrientation? (e : Expr) :
    Option AffinePowOrientation := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    if args.size > 5 then
      if let some orientation := affineOrientationOfBase? args[4]! then
        return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findAffinePowOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      if let some orientation := findAffinePowOrientation? domain then
        return some orientation
      findAffinePowOrientation? body
  | .lam _ domain body _ =>
      if let some orientation := findAffinePowOrientation? domain then
        return some orientation
      findAffinePowOrientation? body
  | .letE _ type value body _ =>
      if let some orientation := findAffinePowOrientation? type then
        return some orientation
      if let some orientation := findAffinePowOrientation? value then
        return some orientation
      findAffinePowOrientation? body
  | .proj _ _ body => findAffinePowOrientation? body
  | _ => none

private partial def containsRootZeroPower (e : Expr) : Bool :=
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    let args := e.getAppArgs
    args.size > 5 && isPolynomialX args[4]!
  else
    e.getAppArgs.any containsRootZeroPower ||
      match e with
      | .forallE _ domain body _ => containsRootZeroPower domain || containsRootZeroPower body
      | .lam _ domain body _ => containsRootZeroPower domain || containsRootZeroPower body
      | .letE _ type value body _ =>
          containsRootZeroPower type || containsRootZeroPower value || containsRootZeroPower body
      | .proj _ _ body => containsRootZeroPower body
      | _ => false

private partial def findAffineLinearOrientation? (e : Expr) :
    Option AffinePowOrientation := Id.run do
  let e := e.consumeMData
  if appFnName? e == some ``HPow.hPow then
    return none
  if let some orientation := affineOrientationOfBase? e then
    return some orientation
  for arg in e.getAppArgs do
    if let some orientation := findAffineLinearOrientation? arg then
      return some orientation
  match e with
  | .forallE _ domain body _ =>
      if let some orientation := findAffineLinearOrientation? domain then
        return some orientation
      findAffineLinearOrientation? body
  | .lam _ domain body _ =>
      if let some orientation := findAffineLinearOrientation? domain then
        return some orientation
      findAffineLinearOrientation? body
  | .letE _ type value body _ =>
      if let some orientation := findAffineLinearOrientation? type then
        return some orientation
      if let some orientation := findAffineLinearOrientation? value then
        return some orientation
      findAffineLinearOrientation? body
  | .proj _ _ body => findAffineLinearOrientation? body
  | _ => none

private def affineLinearOrientationOfEvidence (label : String) (evidence : Syntax) :
    TacticM AffinePowOrientation := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findAffineLinearOrientation? evidenceType with
  | some orientation => pure orientation
  | none =>
      throwError
        "rr_product checked affine auto: no affine factor found in {label}"

private def affinePowOrientationOfEvidence (label : String) (evidence : Syntax) :
    TacticM AffinePowOrientation := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findAffinePowOrientation? evidenceType with
  | some orientation => pure orientation
  | none =>
      throwError
        "rr_product checked affine-power auto: no affine-power factor found in {label}"

private def scalarKindOfEvidence (label : String) (evidence : Syntax) :
    TacticM ScalarFactorKind := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  match findScalarTopProductKind? evidenceType with
  | some kind => pure kind
  | none =>
      throwError "rr_product checked scalar auto: no scalar factor found in {label}"

private def rootZeroPowerOfEvidence (label : String) (evidence : Syntax) :
    TacticM Unit := withMainContext do
  let evidenceExpr ← Lean.Elab.Tactic.elabTerm evidence none
  let evidenceType ← instantiateMVars (← inferType evidenceExpr)
  if containsRootZeroPower evidenceType then
    pure ()
  else
    throwError "rr_product checked root-zero power auto: no root-zero power found in {label}"

/-- Checked form of `rr_product_lift_affine_sequence_auto`: reads the orientation of the affine
factor off the type of `factorization` and runs the affine or the constant-first lift tactic;
takes only `quotient_realrooted` and `factorization`. -/
elab "rr_product_lift_checked_affine_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affineLinearOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

/-- Cutoff form of `rr_product_lift_checked_affine_sequence_auto`; takes `base`,
`quotient_realrooted`, `cutoff` and `factorization`. -/
elab "rr_product_lift_checked_affine_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← affineLinearOrientationOfEvidence "factorization" hrow with
  | .mulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .constFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by lifting real-rootedness through a row factor whose
shape (`X`, a scalar, `X + C`, `C + X`, an affine factor, or a power of one of these) is read off
`factorization`; takes only `quotient_realrooted` and `factorization`. -/
elab "rr_product_lift_sequence_auto" " using "
    "quotient_realrooted" ":=" hquot:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← liftAutoShapeOfEvidence hquot hrow with
  | .X =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_sequence using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .XAddC =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_add_C_sequence using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .CAddX =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_add_X_sequence using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .XPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_pow_sequence using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .XAddCPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_add_C_row_pow_sequence using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .CAddXPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_add_X_pow_sequence using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .affineMulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .affineConstFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .affinePowMulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))
  | .affinePowConstFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_affine_pow_sequence_auto using
            quotient_realrooted := $hquot,
            factorization := $hrow))

/-- Cutoff form of `rr_product_lift_sequence_auto`; takes `base`,
`quotient_realrooted`, `cutoff` and `factorization`. -/
elab "rr_product_lift_sequence_auto" " using "
    "base" ":=" hbase:term ","
    "quotient_realrooted" ":=" hquot:term ","
    "cutoff" ":=" N:term ","
    "factorization" ":=" hrow:term : tactic => do
  match ← liftAutoShapeOfEvidence hquot hrow with
  | .X =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_sequence using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .scalar =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .scalarPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .XAddC =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_add_C_sequence using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .CAddX =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_add_X_sequence using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .XPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_pow_sequence using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .XAddCPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_X_add_C_row_pow_sequence using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .CAddXPow =>
      evalTactic
        (← `(tactic|
          rr_product_lift_C_add_X_pow_sequence using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .affineMulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .affineConstFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .affinePowMulXFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_affine_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))
  | .affinePowConstFirst =>
      evalTactic
        (← `(tactic|
          rr_product_lift_const_first_affine_pow_sequence_auto using
            base := $hbase,
            quotient_realrooted := $hquot,
            cutoff := $N,
            factorization := $hrow))

/-- Closes a real-rootedness goal from one of two certified terms: `hleft` or `hright` is chosen
by the product orientation recognized in `hleft`, and both are tried if none is recognized. -/
elab "rr_product_two_sequence_variants" hleft:term "," hright:term : tactic => do
  let orientation ←
    match ← liftProductOrientationOfCandidate? hleft with
    | some orientation => pure (some orientation)
    | none => productOrientationOfCandidate? hleft
  match orientation with
  | some .factorLeft =>
      evalTactic
        (← `(tactic| rr_first_realrooted_sequence_or_projection $hleft))
  | some .factorRight =>
      evalTactic
        (← `(tactic| rr_first_realrooted_sequence_or_projection $hright))
  | none =>
      evalTactic
        (← `(tactic| rr_first_realrooted_sequence_or_projection $hleft, $hright))

macro_rules
  | `(tactic| rr_product_nonzero) =>
      `(tactic| rr_side_ne)
  | `(tactic| rr_product_normalize using $h:term) =>
      `(tactic|
        have hcert := ($h);
        first
          | exact hcert
          | convert hcert using 2 <;> norm_num <;> ring)
  | `(rr_product_nonzero_seq) =>
      `(fun n => by rr_product_nonzero)
  | `(rr_product_nonzero_seq_from) =>
      `(fun n _ => by rr_product_nonzero)

macro_rules
  | `(tactic|
      rr_product_lift_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_lift_sequence_from $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_lift_sequence $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_lift_right_sequence $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_lift_sequence_from
            $N $hbase $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_lift_right_sequence_from
            $N $hbase $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_affine_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_affine_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_pow_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_pow_lift_sequence $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_pow_lift_right_sequence
            $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hc:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_pow_lift_sequence_from
            $N $hbase $hquot $hc $hrow),
          (RealRooted.isRealRooted_of_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hc $hrow))
  | `(tactic|
      rr_product_lift_C_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_C_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_X_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_X_pow_lift_right_sequence $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_row_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_sequence
            $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_X_add_C_row_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_X_add_C_row_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_pow_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_sequence $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_right_sequence
            $hquot $hrow))
  | `(tactic|
      rr_product_lift_C_add_X_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_sequence_from
            $N $hbase $hquot $hrow),
          (RealRooted.isRealRooted_of_C_add_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_mul_X_add_C_pow_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_affine_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_affine_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_sequence
            $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence
            $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_two_sequence_variants
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_sequence_from
            $N $hbase $hquot $hs $hrow),
          (RealRooted.isRealRooted_of_C_add_C_mul_X_pow_lift_right_sequence_from
            $N $hbase $hquot $hs $hrow))
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence_auto using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_const_first_affine_pow_sequence_auto using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := rr_product_nonzero_seq_from,
          cutoff := $N,
          factorization := $hrow)

end Tactic
end RealRooted
