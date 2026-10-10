import RealRooted.Interlacing.Euclid
import RealRooted.Tactic.Recurrence.ODE

/-!
# `rr_interlaces_explicit`

Closes `Interlaces g f` for explicit polynomials `g` and `f` with rational
coefficients.  The tactic computes the Euclidean remainder sequence exactly: it
divides `f` by `g`, checks that the remainder `r` has a negative leading coefficient,
and proves `g ≪ f` from `-r ≪ g` by `RealRooted.interlaces_of_euclid_step`, down to a
nonzero constant interlacing a linear polynomial.  This is the Sturm-sequence
certificate for interlacing: it succeeds exactly when the remainder sequence has
the alternating signs of a Jacobi continued fraction.

Both sides are first rewritten into monomial normal form, so the degree and
coefficient side goals reduce to numerals.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Close a degree, coefficient or nonvanishing side goal about explicit polynomials. -/
def explicitSideGoal : TacticM Unit := do
  evalTactic (← `(tactic| first
    | (compute_degree!; done)
    | (simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
        Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
        Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero]
       norm_num
       done)
    | (norm_num; done)
    | (simp; done)
    | fail "rr_interlaces_explicit: could not close a side goal"))

/-- For `p` of degree above two with only rational roots: `C a * ∏ (X - C r)` over its
roots (with multiplicity) and a proof that the product splits. -/
def rationalFactorization? (pq : QPoly) : TacticM (Option (Term × Term)) := do
  let roots := pq.rationalRoots
  unless pq.natDegree > 2 && roots.length == pq.natDegree do return none
  let mut prod : Term ← `(Polynomial.X - Polynomial.C ($(← ratTerm roots.getLast!) : ℝ))
  let mut pf : Term ← `(Polynomial.Splits.X_sub_C _)
  for r in roots.dropLast.reverse do
    prod ← `((Polynomial.X - Polynomial.C ($(← ratTerm r) : ℝ)) * $prod)
    pf ← `(Polynomial.Splits.mul (Polynomial.Splits.X_sub_C _) $pf)
  return some (← `(Polynomial.C ($(← ratTerm pq.lead) : ℝ) * $prod), pf)

/-- Prove `∀ t ∈ p.roots, Q t` for an explicit `p` of degree above two with only rational
roots: factor `p` over its roots and check `Q` at each root with `norm_num`. -/
elab "rr_roots_explicit" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some rootsE := tgt.find? (·.isAppOfArity ``Polynomial.roots 4)
    | throwError "rr_roots_explicit: the goal is not `∀ t ∈ p.roots, Q t`"
  let pE := rootsE.appArg!
  if pE.hasLooseBVars then throwError "rr_roots_explicit: the polynomial depends on the root"
  let some pq ← evalQPoly? pE | throwError "rr_roots_explicit: not an explicit polynomial"
  let some (fac, _) ← rationalFactorization? pq
    | throwError "rr_roots_explicit: the roots of the polynomial are not all rational"
  let pT ← Term.exprToSyntax pE
  let h := mkIdent `rr_hroot
  evalTactic (← `(tactic| (
    intro t ht
    have $h:ident := Polynomial.isRoot_of_mem_roots ht
    rw [show $pT = $fac by rr_poly_identity] at $h:ident
    simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, mul_eq_zero, sub_eq_zero] at $h:ident)))
  -- `a = 0 ∨ t = r₁ ∨ …`: the leading coefficient is nonzero, and `Q` holds at each root
  let leaf : TacticM Unit := evalTactic (← `(tactic| first
    | (norm_num at $h:ident; done)
    | (subst $h:ident; norm_num; done)
    | (rw [$h:ident]; norm_num; done)))
  for _ in [0:pq.natDegree + 1] do
    let g ← getMainGoal
    let some d := (← g.getDecl).lctx.findFromUserName? h.getId | break
    unless (← instantiateMVars d.type).isAppOf ``Or do break
    evalTactic (← `(tactic| rcases $h:ident with $h:ident | $h:ident))
    let [g₁, g₂] ← getGoals | throwError "rr_roots_explicit: unexpected goals"
    setGoals [g₁]
    leaf
    setGoals [g₂]
  leaf

/-- Prove `p.Splits` for an explicit `p` of degree at most two (degree one, or a
nonnegative discriminant) or with only rational roots, after rewriting `p` into normal form. -/
elab "rr_splits_explicit" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``Polynomial.Splits 3 || tgt.isAppOf ``Polynomial.Splits do
    throwError "rr_splits_explicit: the goal is not `p.Splits`"
  let pE := tgt.appArg!
  let some pq ← evalQPoly? pE | throwError "rr_splits_explicit: not an explicit polynomial"
  let pT ← Term.exprToSyntax pE
  if let some (fac, pf) ← rationalFactorization? pq then
    evalTactic (← `(tactic| (
      refine (congrArg Polynomial.Splits (show $pT = $fac by rr_poly_identity)).mpr ?_
      exact Polynomial.Splits.C_mul $pf _)))
    return
  evalTactic (← `(tactic|
    refine (congrArg Polynomial.Splits (show $pT = $(← qpolyTerm pq) by rr_poly_identity)).mpr ?_))
  if pq.natDegree ≤ 1 then
    evalTactic (← `(tactic| (
      refine Polynomial.Splits.of_natDegree_le_one ?_
      compute_degree!)))
  else if pq.natDegree == 2 then
    evalTactic (← `(tactic| (
      refine RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg ?_ ?_
      · compute_degree!
      · simp only [discrim, Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
          Polynomial.coeff_one, Polynomial.coeff_ofNat_mul]
        norm_num)))
  else
    throwError "rr_splits_explicit: degree {pq.natDegree} > 2 without rational roots \
      is not supported"

/-- Prove `p ≠ 0` for an explicit nonzero `p`, from its top coefficient. -/
elab "rr_ne_zero_explicit" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (_, pE, _) := tgt.ne? | throwError "rr_ne_zero_explicit: the goal is not `p ≠ 0`"
  let some pq ← evalQPoly? pE | throwError "rr_ne_zero_explicit: not an explicit polynomial"
  if pq.isZero then throwError "rr_ne_zero_explicit: the polynomial is zero"
  let pT ← Term.exprToSyntax pE
  evalTactic (← `(tactic| (
    refine (congrArg (· ≠ (0 : ℝ[X])) (show $pT = $(← qpolyTerm pq) by rr_poly_identity)).mpr ?_
    intro h0
    have h' := congrArg (fun p : ℝ[X] => p.coeff $(rowNumLit pq.natDegree)) h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
      Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
      Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
      Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero] at h'
    norm_num at h')))

/-- Prove `Interlaces g f` for the normal-form terms of `gq` and `fq`. -/
partial def proveInterlacesExplicit (gq fq : QPoly) : TacticM Unit := do
  if gq.isZero || fq.natDegree != gq.natDegree + 1 then
    throwError "rr_interlaces_explicit: the degrees are not consecutive"
  if gq.natDegree == 0 then
    evalTactic (← `(tactic|
      apply RealRooted.interlaces_of_natDegree_eq_zero_of_natDegree_eq_one))
    for g in ← getGoals do
      setGoals [g]
      explicitSideGoal
    return
  let (q, r) := fq.divMod gq
  let h := -r
  unless !h.isZero && h.natDegree + 1 == gq.natDegree && 0 < h.lead do
    throwError "rr_interlaces_explicit: the Euclidean remainder has the wrong sign or degree"
  let m := h.natDegree
  evalTactic (← `(tactic|
    refine RealRooted.interlaces_of_euclid_step_of_natDegree (q := $(← qpolyTerm q))
      (h := $(← qpolyTerm h)) (m := $(rowNumLit m)) ?_ ?_ ?_ ?_ ?_ ?_ ?_))
  let gs ← getGoals
  let some grec := gs[0]? | throwError "rr_interlaces_explicit: no recursive goal"
  for g in gs.drop 1 do
    setGoals [g]
    if (← instantiateMVars (← g.getType)).isAppOf ``Eq &&
        ((← instantiateMVars (← g.getType)).find? (·.isConstOf ``Polynomial.natDegree)).isNone &&
        ((← instantiateMVars (← g.getType)).find? (·.isConstOf ``Polynomial.coeff)).isNone then
      evalTactic (← `(tactic| rr_poly_identity))
    else explicitSideGoal
  setGoals [grec]
  proveInterlacesExplicit h gq

/-- Close `Interlaces g f` for explicit polynomials with rational coefficients. -/
elab "rr_interlaces_explicit" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``RealRooted.Interlaces 2 do
    throwError "rr_interlaces_explicit: the goal is not `Interlaces g f`"
  let gE := tgt.appFn!.appArg!
  let fE := tgt.appArg!
  let (some gq, some fq) := (← evalQPoly? gE, ← evalQPoly? fE)
    | throwError "rr_interlaces_explicit: could not read the polynomials as explicit"
  let gT ← Term.exprToSyntax gE
  let fT ← Term.exprToSyntax fE
  let d := gq.gcd fq
  if d.natDegree == 0 then
    -- rewrite both sides into monomial normal form
    evalTactic (← `(tactic|
      refine (congrArg₂ RealRooted.Interlaces (show $gT = $(← qpolyTerm gq) by rr_poly_identity)
        (show $fT = $(← qpolyTerm fq) by rr_poly_identity)).mpr ?_))
    proveInterlacesExplicit gq fq
  else
    -- a common factor `d`: cancel it, and prove that `d` is real-rooted
    let some g' := gq.divExact? d | throwError "rr_interlaces_explicit: gcd failure"
    let some f' := fq.divExact? d | throwError "rr_interlaces_explicit: gcd failure"
    let dT ← qpolyTerm d
    evalTactic (← `(tactic|
      refine (congrArg₂ RealRooted.Interlaces
        (show $gT = $dT * $(← qpolyTerm g') by rr_poly_identity)
        (show $fT = $dT * $(← qpolyTerm f') by rr_poly_identity)).mpr ?_))
    evalTactic (← `(tactic| refine RealRooted.Interlaces.mul_both_of_splits ?_ ?_ ?_))
    let gs ← getGoals
    let some grec := gs[0]? | throwError "rr_interlaces_explicit: no goal"
    let some gsplit := gs[1]? | throwError "rr_interlaces_explicit: no goal"
    let some gne := gs[2]? | throwError "rr_interlaces_explicit: no goal"
    setGoals [gsplit]
    evalTactic (← `(tactic| rr_splits_explicit))
    setGoals [gne]
    evalTactic (← `(tactic| rr_ne_zero_explicit))
    setGoals [grec]
    proveInterlacesExplicit g' f'

end RealRooted.Tactic
