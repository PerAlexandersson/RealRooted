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

/-- Quotient and remainder of `p` by a nonzero `q`. -/
def QPoly.divMod (p q : QPoly) : QPoly × QPoly := Id.run do
  if q.isZero then return (⟨#[]⟩, p)
  let mut r := p
  let mut quot : QPoly := ⟨#[]⟩
  for _ in [0:p.coeffs.size + 1] do
    if r.isZero || r.natDegree < q.natDegree then break
    let k := r.natDegree - q.natDegree
    let mono : QPoly := QPoly.smul (r.lead / q.lead) ⟨Array.replicate k 0 ++ #[1]⟩
    quot := quot + mono
    r := r - mono * q
  return (quot, r)

/-- Monic greatest common divisor. -/
partial def QPoly.gcd (p q : QPoly) : QPoly :=
  if q.isZero then (if p.isZero then p else QPoly.smul p.lead⁻¹ p)
  else QPoly.gcd q (p.divMod q).2

/-- Value at a rational point. -/
def QPoly.evalAt (p : QPoly) (r : Rat) : Rat :=
  p.coeffs.foldr (fun c acc => c + r * acc) 0

private def divisors (n : Nat) : List Nat :=
  if n == 0 || n > 1000000 then [] else (List.range (n + 1)).filter fun d => d > 0 && n % d == 0

/-- The rational roots of `p`, with multiplicity (complete when `p` splits over `ℚ`). -/
partial def QPoly.rationalRoots (p : QPoly) : List Rat := Id.run do
  if p.isZero || p.natDegree == 0 then return []
  -- a root at zero
  if p.coeff 0 == 0 then
    let some p' := p.divExact? QPoly.X | return []
    return 0 :: p'.rationalRoots
  let l := p.coeffs.foldl (fun acc c => Nat.lcm acc c.den) 1
  let a0 := ((p.coeff 0) * l).num.natAbs
  let an := (p.lead * l).num.natAbs
  for u in divisors a0 do
    for v in divisors an do
      for r in [((u : Int) : Rat) / v, -(((u : Int) : Rat) / v)] do
        if p.evalAt r == 0 then
          let lin : QPoly := ⟨#[-r, 1]⟩
          if let some p' := p.divExact? lin then return r :: p'.rationalRoots
  return []

private def numLit (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

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

/-- Prove `p.Splits` for an explicit `p` of degree at most two (degree one, or a
nonnegative discriminant), after rewriting `p` into normal form. -/
elab "rr_splits_explicit" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``Polynomial.Splits 3 || tgt.isAppOf ``Polynomial.Splits do
    throwError "rr_splits_explicit: the goal is not `p.Splits`"
  let pE := tgt.appArg!
  let some pq ← evalQPoly? pE | throwError "rr_splits_explicit: not an explicit polynomial"
  let pT ← Term.exprToSyntax pE
  let roots := pq.rationalRoots
  if pq.natDegree > 2 && roots.length == pq.natDegree then
    -- `p = C a * ∏ (X - C r)` over its rational roots
    let mut prod : Term ← `(Polynomial.X - Polynomial.C ($(← ratTerm roots.getLast!) : ℝ))
    let mut pf : Term ← `(Polynomial.Splits.X_sub_C _)
    for r in roots.dropLast.reverse do
      prod ← `((Polynomial.X - Polynomial.C ($(← ratTerm r) : ℝ)) * $prod)
      pf ← `(Polynomial.Splits.mul (Polynomial.Splits.X_sub_C _) $pf)
    let fac ← `(Polynomial.C ($(← ratTerm pq.lead) : ℝ) * $prod)
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
    have h' := congrArg (fun p : ℝ[X] => p.coeff $(numLit pq.natDegree)) h0
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
      (h := $(← qpolyTerm h)) (m := $(numLit m)) ?_ ?_ ?_ ?_ ?_ ?_ ?_))
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
