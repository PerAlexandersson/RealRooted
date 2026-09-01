import RealRooted.SequenceClosure
import RealRooted.Tactic.Lookup
import RealRooted.Tactic.Named
import RealRooted.Tactic.RecurrenceEval
import RealRooted.Tactic.Sign
import RealRooted.Tactic.SideGoals

/-!
# Finish tactic frontend

Syntax and elaboration for proof tails that consume the theorem backend in
`RealRooted.SequenceClosure`.
-/

open Polynomial

namespace RealRooted

namespace Tactic

open Lean
open Lean.Meta
open Lean.Elab.Tactic

syntax (name := rr_lookup_term) "rr_lookup_term" : term
syntax (name := rr_realrooted_term) "rr_realrooted_term" : term
syntax (name := rr_lookup_interlaces_term) "rr_lookup_interlaces_term" : term
syntax (name := rr_degree_eq_one) "rr_degree_eq_one" : tactic
syntax (name := rr_degree_le_one) "rr_degree_le_one" : tactic
syntax (name := rr_natDegree_from_top_above)
  "rr_natDegree_from_top_above" " using "
    "top_ne" ":=" term ","
    "above" ":=" term :
  tactic

syntax (name := rr_natDegree_from_top_eq_above)
  "rr_natDegree_from_top_above" " using "
    "top_eq" ":=" term ","
    "above" ":=" term :
  tactic

syntax (name := rr_natDegree_from_top_pos_above)
  "rr_natDegree_from_top_above" " using "
    "top_pos" ":=" term ","
    "above" ":=" term :
  tactic

syntax (name := rr_exact_realrooted_or_projection)
  "rr_exact_realrooted_or_projection" term :
  tactic

syntax (name := rr_exact_realrooted_sequence_or_projection)
  "rr_exact_realrooted_sequence_or_projection" term :
  tactic

syntax (name := rr_exact_realrooted_refine_then)
  "rr_exact_realrooted_refine_then " term " with " tactic :
  tactic

syntax (name := rr_exact_realrooted_pair_sequence_or_projection)
  "rr_exact_realrooted_pair_sequence_or_projection" term :
  tactic

syntax (name := rr_first_exact)
  "rr_first_exact" term,* :
  tactic

syntax (name := rr_first_exact_or_simpa)
  "rr_first_exact_or_simpa" term ", " term :
  tactic

syntax (name := rr_first_exact_or_simpa_mul_assoc)
  "rr_first_exact_or_simpa_mul_assoc" term ", " term :
  tactic

syntax (name := rr_first_exact_or_simpa_mul_add_assoc)
  "rr_first_exact_or_simpa_mul_add_assoc" term ", " term :
  tactic

syntax (name := rr_first_realrooted_or_projection)
  "rr_first_realrooted_or_projection" term,* :
  tactic

syntax (name := rr_first_realrooted_sequence_or_projection)
  "rr_first_realrooted_sequence_or_projection" term,* :
  tactic

syntax (name := rr_first_exact_then_realrooted_sequence_or_projection)
  "rr_first_exact_then_realrooted_sequence_or_projection" term,* :
  tactic

syntax (name := rr_nonzero) "rr_nonzero" " using " term : tactic
syntax (name := rr_splits) "rr_splits" " using " term : tactic
syntax (name := rr_splits_mul)
  "rr_splits_mul" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
syntax (name := rr_splits_pow)
  "rr_splits_pow" " using "
    "splits" ":=" term ","
    "exponent" ":=" term :
  tactic
syntax (name := rr_splits_reverse)
  "rr_splits_reverse" " using "
    "splits" ":=" term :
  tactic
syntax (name := rr_splits_of_reverse)
  "rr_splits_of_reverse" " using "
    "reverse_splits" ":=" term :
  tactic
syntax (name := rr_splits_reflect)
  "rr_splits_reflect" " using "
    "splits" ":=" term ","
    "degree_bound" ":=" term :
  tactic
syntax (name := rr_splits_X_pow_mul_reverse)
  "rr_splits_X_pow_mul_reverse" " using "
    "splits" ":=" term :
  tactic
syntax (name := rr_splits_divX)
  "rr_splits_divX" " using "
    "coeff_zero" ":=" term ","
    "splits" ":=" term :
  tactic
syntax (name := rr_splits_of_divX)
  "rr_splits_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits)
  "rr_zero_or_splits" " using " term :
  tactic
syntax (name := rr_zero_or_splits_mul)
  "rr_zero_or_splits_mul" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_pow)
  "rr_zero_or_splits_pow" " using "
    "zero_or_splits" ":=" term ","
    "exponent" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_reverse)
  "rr_zero_or_splits_reverse" " using "
    "zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_of_reverse)
  "rr_zero_or_splits_of_reverse" " using "
    "reverse_zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_reflect)
  "rr_zero_or_splits_reflect" " using "
    "zero_or_splits" ":=" term ","
    "degree_bound" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_X_pow_mul_reverse)
  "rr_zero_or_splits_X_pow_mul_reverse" " using "
    "zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_divX)
  "rr_zero_or_splits_divX" " using "
    "coeff_zero" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_of_divX)
  "rr_zero_or_splits_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_zero_or_splits" ":=" term :
  tactic
syntax (name := rr_realrooted) "rr_realrooted" " using " term : tactic
syntax (name := rr_mul_realrooted)
  "rr_mul_realrooted" " using " term ", " term :
  tactic
syntax (name := rr_mul_realrooted_named)
  "rr_mul_realrooted" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
syntax (name := rr_pow_realrooted)
  "rr_pow_realrooted" " using "
    "realrooted" ":=" term ","
    "exponent" ":=" term :
  tactic
syntax (name := rr_realrooted_reverse)
  "rr_realrooted_reverse" " using "
    "realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_of_reverse)
  "rr_realrooted_of_reverse" " using "
    "reverse_realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_reflect)
  "rr_realrooted_reflect" " using "
    "realrooted" ":=" term ","
    "degree_bound" ":=" term :
  tactic
syntax (name := rr_realrooted_X_pow_mul_reverse)
  "rr_realrooted_X_pow_mul_reverse" " using "
    "realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_divX)
  "rr_realrooted_divX" " using "
    "coeff_zero" ":=" term ","
    "realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_of_divX)
  "rr_realrooted_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_realrooted" ":=" term :
  tactic
syntax (name := rr_nonzero_auto) "rr_nonzero" : tactic
syntax (name := rr_splits_auto) "rr_splits" : tactic
syntax (name := rr_zero_or_splits_auto) "rr_zero_or_splits" : tactic
syntax (name := rr_realrooted_auto) "rr_realrooted" : tactic

syntax (name := rr_interlaces_with_degree)
  "rr_interlaces" " using " term ", " term : tactic

syntax (name := rr_interlaces_auto_degree)
  "rr_interlaces" " using " term : tactic

syntax (name := rr_interlaces_auto_named) "rr_interlaces" : tactic

syntax (name := rr_prec0) "rr_prec0" " using " term : tactic

syntax (name := rr_prec_of_interlaces)
  "rr_prec" " using " term :
  tactic

syntax (name := rr_prec_of_prec0)
  "rr_prec" " using " term ", " term ", " term : tactic

syntax (name := rr_gsturm_cons)
  "rr_gsturm_cons" " using " term ", " term : tactic

syntax (name := rr_sturm_cons)
  "rr_sturm_cons" " using " term ", " term : tactic

syntax (name := rr_sturm_base) "rr_sturm_base" : tactic

syntax (name := rr_prec_sequence)
  "rr_prec_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_prec_sequence_realrooted)
  "rr_prec_sequence_realrooted" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_finish_sequence_base_step)
  "rr_finish_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_finish_sequence_prec)
  "rr_finish_sequence" " using "
    "prec" ":=" term :
  tactic

syntax (name := rr_finish_sequence_prec_degree)
  "rr_finish_sequence" " using "
    "prec" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_degree_branch)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted_degree_branch)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish_sequence_branches)
  "rr_finish_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish_sequence_branches_degree_branch)
  "rr_finish_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish_using) "rr_finish" " using " term : tactic

syntax (name := rr_finish_using_interlaces_degree)
  "rr_finish" " using " term ", " term : tactic

syntax (name := rr_finish_using_prec0)
  "rr_finish" " using " term ", " term ", " term : tactic

syntax (name := rr_finish_using_sequence_branches)
  "rr_finish" " using " term ", " term ", " term ", " term : tactic

syntax (name := rr_finish) "rr_finish" : tactic

private def closeWithProof? (tacticName : Name) (proof : Expr) : TacticM Bool := do
  let result? ← observing? do
    withMainContext do
      let target ← getMainTarget
      let proofType ← inferType proof
      if ← withNewMCtxDepth <| isDefEq proofType target then
        closeMainGoal tacticName proof
        return true
      else
        return false
  return result?.getD false

private def assertProofAs (nameBase : Name) (proof : Expr) : TacticM Ident := do
  let name ← mkFreshUserName nameBase
  let type ← inferType proof
  let goal ← getMainGoal
  let (_, goal) ← (← goal.assert name type proof).intro1P
  replaceMainGoal [goal]
  return mkIdent name

private def closeNamedDirect? (tacticName : Name) (cName : Name) (arg : Expr)
    (suffix : String) : TacticM Bool := do
  for candidate in namedSuffixCandidates suffix do
    if let some proof ← mkNamedTheoremApp? cName candidate arg then
      if ← closeWithProof? tacticName proof then
        return true
  return false

private def closeNamedDirectOrPrec (tacticName : Name) (target : Expr)
    (directSuffix : String) (closePrec : Ident → TacticM Unit) : TacticM Unit := do
  let some (cName, arg) ← findNamedPolynomialConstantApp? target
    | throwError "{tacticName} failed: could not find named polynomial in target: {target}"
  if ← closeNamedDirect? tacticName cName arg directSuffix then
    return
  for candidate in namedSuffixCandidates "_prec" do
    if let some proof ← mkNamedTheoremApp? cName candidate arg then
      let hprec ← assertProofAs `hprec proof
      withMainContext do
        closePrec hprec
      return
  throwError "{tacticName} failed: no matching named final wrapper closes target: {target}"

elab "rr_named_nonzero" : tactic => do
  withMainContext do
    let target ← getMainTarget
    closeNamedDirectOrPrec `rr_named_nonzero target "_ne_zero" fun hprec => do
      evalTactic (← `(tactic| rr_nonzero using $hprec:ident))

elab "rr_named_splits" : tactic => do
  withMainContext do
    let target ← getMainTarget
    closeNamedDirectOrPrec `rr_named_splits target "_splits" fun hprec => do
      evalTactic (← `(tactic| rr_splits using $hprec:ident))

elab "rr_named_realrooted" : tactic => do
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some (cName, arg) ← findNamedPolynomialConstantApp? target
      | throwError "rr_named_realrooted failed: could not find named polynomial"
    if ← closeNamedDirect? `rr_named_realrooted cName arg "_realRooted" then
      return
    evalTactic (← `(tactic| exact ⟨by rr_named_nonzero, by rr_named_splits⟩))

elab "rr_named_interlaces" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let some (cName, arg) ← findNamedConstantApp? target
      | throwError "rr_named_interlaces failed: could not find named expression"
    unless ← closeNamedDirect? `rr_named_interlaces cName arg "_interlaces" do
      throwError
        "rr_named_interlaces failed: no matching named interlacing wrapper for {cName}"

macro_rules
  | `(rr_lookup_term) =>
      `(by rr_lookup)
  | `(rr_realrooted_term) =>
      `(by rr_realrooted)
  | `(rr_lookup_interlaces_term) =>
      `(by
        first
          | exact RealRooted.Prec.toInterlaces rr_lookup_term rr_lookup_term
          | exact RealRooted.Prec.toInterlaces rr_lookup_term (by
              symm
              rr_lookup))
  | `(tactic| rr_degree_eq_one) =>
      `(tactic|
        first
          | rr_lookup [rr_degree]
          | (symm; rr_lookup [rr_degree]))
  | `(tactic| rr_degree_le_one) =>
      `(tactic|
        first
          | assumption
          | rr_lookup [rr_degree]
          | exact le_of_eq (by rr_lookup [rr_degree])
          | exact le_of_eq (by
              symm
              rr_lookup [rr_degree]))
  | `(tactic|
      rr_natDegree_from_top_above using
        top_ne := $htop:term,
        above := $habove:term) =>
      `(tactic|
        exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            (fun m hm => by exact $habove m hm))
          $htop)
  | `(tactic|
      rr_natDegree_from_top_above using
        top_pos := $htop:term,
        above := $habove:term) =>
      `(tactic|
        exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            (fun m hm => by exact $habove m hm))
          (ne_of_gt $htop))
  | `(tactic|
      rr_natDegree_from_top_above using
        top_eq := $htop:term,
        above := $habove:term) =>
      `(tactic|
        exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            (fun m hm => by exact $habove m hm))
          (by
            have htop' := $htop
            simp [htop']))
  | `(tactic| rr_exact_realrooted_or_projection $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          RealRooted.ne_zero_of_isRealRooted $h,
          RealRooted.splits_of_isRealRooted $h,
          RealRooted.eq_zero_or_splits_of_isRealRooted $h,
          RealRooted.left_isRealRooted_of_isRealRooted_pair $h,
          RealRooted.right_isRealRooted_of_isRealRooted_pair $h,
          RealRooted.left_ne_zero_of_isRealRooted_pair $h,
          RealRooted.right_ne_zero_of_isRealRooted_pair $h,
          RealRooted.left_splits_of_isRealRooted_pair $h,
          RealRooted.right_splits_of_isRealRooted_pair $h,
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair $h,
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)),
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)),
          RealRooted.left_isRealRooted_of_prec $h,
          RealRooted.right_isRealRooted_of_prec $h,
          RealRooted.left_ne_zero_of_prec $h,
          RealRooted.right_ne_zero_of_prec $h,
          RealRooted.left_splits_of_prec $h,
          RealRooted.right_splits_of_prec $h,
          RealRooted.left_eq_zero_or_splits_of_prec $h,
          RealRooted.right_eq_zero_or_splits_of_prec $h,
          RealRooted.right_isRealRooted_of_interlaces $h,
          RealRooted.left_isRealRooted_of_interlaces $h,
          RealRooted.right_ne_zero_of_interlaces $h,
          RealRooted.left_ne_zero_of_interlaces $h,
          RealRooted.right_splits_of_interlaces $h,
          RealRooted.left_splits_of_interlaces $h,
          RealRooted.right_eq_zero_or_splits_of_interlaces $h,
          RealRooted.left_eq_zero_or_splits_of_interlaces $h)
  | `(tactic| rr_exact_realrooted_sequence_or_projection $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.at_of_isRealRooted_sequence $h _),
          RealRooted.ne_zero_of_isRealRooted_sequence $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence $h _),
          RealRooted.splits_of_isRealRooted_sequence $h,
          (RealRooted.splits_of_isRealRooted_sequence $h _),
          RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h _))
  | `(tactic| rr_exact_realrooted_refine_then $h:term with $tac:tactic) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            rr_refine_then $h with $tac))
  | `(tactic| rr_exact_realrooted_pair_sequence_or_projection $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.at_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence $h _))
  | `(tactic| rr_first_exact $[$hs:term],*) =>
      `(tactic|
        first
          $[ | exact $hs]*)
  | `(tactic| rr_first_exact_or_simpa $hdirect:term, $hnormalized:term) =>
      `(tactic|
        first
          | exact $hdirect
          | simpa using $hnormalized)
  | `(tactic| rr_first_exact_or_simpa_mul_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        first
          | exact $hdirect
          | simpa [mul_assoc] using $hnormalized)
  | `(tactic| rr_first_exact_or_simpa_mul_add_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        first
          | exact $hdirect
          | simpa [mul_assoc, add_assoc] using $hnormalized)
  | `(tactic| rr_first_realrooted_or_projection $[$hs:term],*) =>
      `(tactic|
        first
          $[ | rr_exact_realrooted_or_projection $hs]*)
  | `(tactic| rr_first_realrooted_sequence_or_projection $[$hs:term],*) =>
      `(tactic|
        first
          $[ | rr_exact_realrooted_sequence_or_projection $hs]*)
  | `(tactic| rr_first_exact_then_realrooted_sequence_or_projection $[$hs:term],*) =>
      `(tactic|
        first
          $[ | exact $hs]*
          $[ | rr_exact_realrooted_sequence_or_projection $hs]*)
  | `(tactic| rr_nonzero using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)) _),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_prec_sequence $h)),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_prec_sequence $h) _),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_prec_sequence $h)),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_prec_sequence $h) _),
          RealRooted.ne_zero_of_isRealRooted_sequence $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence $h _),
          RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_ne_zero_of_prec $h,
          RealRooted.right_ne_zero_of_prec $h,
          RealRooted.right_ne_zero_of_interlaces $h,
          RealRooted.left_ne_zero_of_interlaces $h,
          RealRooted.ne_zero_of_isRealRooted $h,
          RealRooted.left_ne_zero_of_isRealRooted_pair $h,
          RealRooted.right_ne_zero_of_isRealRooted_pair $h)
  | `(tactic| rr_nonzero) =>
      `(tactic|
        first
          | rr_lookup
          | rr_nonzero using rr_lookup_term
          | assumption
          | (apply RealRooted.ne_zero_of_natDegree_eq_one <;> rr_degree_eq_one)
          | exact Polynomial.X_ne_zero
          | exact Polynomial.X_add_C_ne_zero _
          | exact Polynomial.X_sub_C_ne_zero _
          | (rw [add_comm]; exact Polynomial.X_add_C_ne_zero _)
          | (apply Polynomial.C_ne_zero.mpr <;> rr_side_ne)
          | exact RealRooted.HasPosLeadingCoeff.ne_zero (by assumption)
          | rr_named_nonzero
          | (apply mul_ne_zero <;> rr_nonzero)
          | (apply pow_ne_zero <;> rr_nonzero)
          | (rw [Ne, Polynomial.reverse_eq_zero] <;> rr_nonzero)
          | exact Polynomial.derivative_ne_zero.mpr (by rr_close_side)
          | (intro hzero; simp_all [RealRooted.Prec, RealRooted.Interlaces])
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_splits using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))),
          (RealRooted.splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)) _),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_prec_sequence $h)),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_prec_sequence $h) _),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_prec_sequence $h)),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_prec_sequence $h) _),
          RealRooted.splits_of_isRealRooted_sequence $h,
          (RealRooted.splits_of_isRealRooted_sequence $h _),
          RealRooted.left_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.splits_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.splits_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.splits_swap_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.splits_swap_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_splits_of_prec $h,
          RealRooted.right_splits_of_prec $h,
          RealRooted.right_splits_of_interlaces $h,
          RealRooted.left_splits_of_interlaces $h,
          RealRooted.splits_of_isRealRooted $h,
          RealRooted.left_splits_of_isRealRooted_pair $h,
          RealRooted.right_splits_of_isRealRooted_pair $h,
          RealRooted.mul_splits_of_isRealRooted_pair $h,
          RealRooted.swap_mul_splits_of_isRealRooted_pair $h,
          RealRooted.splits_pow_of_isRealRooted $h _,
          Polynomial.Splits.pow $h _,
          RealRooted.DegreeDropReversal.splits_reverse $h,
          RealRooted.DegreeDropReversal.splits_of_reverse $h,
          RealRooted.DegreeDropReversal.splits_X_pow_mul_reverse $h _,
          (RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mpr $h,
          (RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mp $h)
  | `(tactic|
      rr_splits_mul using
        left := $hleft:term,
        right := $hright:term) =>
      `(tactic|
        rr_first_exact
          Polynomial.Splits.mul $hleft $hright,
          (by
            simpa [mul_comm] using Polynomial.Splits.mul $hright $hleft))
  | `(tactic|
      rr_splits_pow using
        splits := $h:term,
        exponent := $n:term) =>
      `(tactic|
        exact Polynomial.Splits.pow $h $n)
  | `(tactic|
      rr_splits_reverse using
        splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_reverse $h)
  | `(tactic|
      rr_splits_of_reverse using
        reverse_splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_of_reverse $h)
  | `(tactic|
      rr_splits_reflect using
        splits := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_reflect_of_splits $h $hN)
  | `(tactic|
      rr_splits_X_pow_mul_reverse using
        splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_X_pow_mul_reverse $h _)
  | `(tactic|
      rr_splits_divX using
        coeff_zero := $h0:term,
        splits := $h:term) =>
      `(tactic|
        exact (RealRooted.DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero
          $h0).1 $h)
  | `(tactic|
      rr_splits_of_divX using
        coeff_zero := $h0:term,
        divX_splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_of_divX_splits_of_coeff_zero
          $h0 $h)
  | `(tactic| rr_splits) =>
      `(tactic|
        first
          | rr_lookup
          | rr_splits using rr_lookup_term
          | assumption
          | exact Polynomial.Splits.C _
          | exact Polynomial.Splits.X
          | exact Polynomial.Splits.X_add_C _
          | exact Polynomial.Splits.X_sub_C _
          | exact Polynomial.Splits.X_pow _
          | exact Polynomial.Splits.C_mul_X_pow _ _
          | exact RealRooted.left_splits_of_interlaces
              (RealRooted.derivative_interlaces (by assumption) (by rr_close_side))
          | rr_named_splits
          | (apply Polynomial.Splits.mul <;> rr_splits)
          | (apply Polynomial.Splits.pow <;> rr_splits)
          | simp [add_comm]
          | (apply Polynomial.Splits.of_natDegree_le_one <;> rr_degree_le_one)
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_zero_or_splits using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)) _),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_prec_sequence $h)),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_prec_sequence $h) _),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_prec_sequence $h)),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_prec_sequence $h) _),
          RealRooted.eq_zero_or_splits_of_isRealRooted $h,
          RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h,
          RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h,
          (RealRooted.mul_eq_zero_or_splits
            (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)
            (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)),
          (RealRooted.mul_eq_zero_or_splits
            (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)
            (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.left_eq_zero_or_splits_of_prec $h,
          RealRooted.right_eq_zero_or_splits_of_prec $h,
          RealRooted.right_eq_zero_or_splits_of_interlaces $h,
          RealRooted.left_eq_zero_or_splits_of_interlaces $h,
          RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h _),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair_sequence
            $h _),
          RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h _),
          RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h _),
          (RealRooted.at_of_eq_zero_or_splits_pair_sequence $h _),
          RealRooted.mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h _),
          RealRooted.swap_mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.swap_mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence
            $h _),
          Or.inr $h,
          Or.inr (Polynomial.Splits.pow $h _),
          Or.inr (RealRooted.DegreeDropReversal.splits_reverse $h),
          Or.inr (RealRooted.DegreeDropReversal.splits_of_reverse $h),
          Or.inr (RealRooted.DegreeDropReversal.splits_X_pow_mul_reverse $h _),
          Or.inr ((RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mpr $h),
          Or.inr ((RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mp $h),
          RealRooted.pow_eq_zero_or_splits $h _,
          RealRooted.pow_eq_zero_or_splits_of_isRealRooted $h _,
          RealRooted.reverse_eq_zero_or_splits $h,
          RealRooted.eq_zero_or_splits_of_reverse $h,
          RealRooted.X_pow_mul_reverse_eq_zero_or_splits $h _)
  | `(tactic|
      rr_zero_or_splits_mul using
        left := $hp:term,
        right := $hq:term) =>
      `(tactic|
        rr_first_exact
          RealRooted.mul_eq_zero_or_splits $hp $hq,
          RealRooted.mul_eq_zero_or_splits $hq $hp)
  | `(tactic|
      rr_zero_or_splits_pow using
        zero_or_splits := $h:term,
        exponent := $n:term) =>
      `(tactic|
        exact RealRooted.pow_eq_zero_or_splits $h $n)
  | `(tactic|
      rr_zero_or_splits_reverse using
        zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.reverse_eq_zero_or_splits $h)
  | `(tactic|
      rr_zero_or_splits_of_reverse using
        reverse_zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.eq_zero_or_splits_of_reverse $h)
  | `(tactic|
      rr_zero_or_splits_reflect using
        zero_or_splits := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact RealRooted.reflect_eq_zero_or_splits $h $hN)
  | `(tactic|
      rr_zero_or_splits_X_pow_mul_reverse using
        zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.X_pow_mul_reverse_eq_zero_or_splits $h _)
  | `(tactic|
      rr_zero_or_splits_divX using
        coeff_zero := $h0:term,
        zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.divX_eq_zero_or_splits_of_coeff_zero $h0 $h)
  | `(tactic|
      rr_zero_or_splits_of_divX using
        coeff_zero := $h0:term,
        divX_zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.eq_zero_or_splits_of_divX $h0 $h)
  | `(tactic| rr_zero_or_splits) =>
      `(tactic|
        first
          | rr_lookup
          | rr_zero_or_splits using rr_lookup_term
          | assumption
          | (apply RealRooted.mul_eq_zero_or_splits <;> rr_zero_or_splits)
          | (apply RealRooted.pow_eq_zero_or_splits <;> rr_zero_or_splits)
          | exact Or.inr (by rr_splits)
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_realrooted using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)),
          (RealRooted.left_isRealRooted_of_interlaces ($h _)),
          (RealRooted.left_isRealRooted_of_prec_sequence $h),
          (RealRooted.left_isRealRooted_of_prec_sequence $h _),
          (RealRooted.right_isRealRooted_of_prec_sequence $h),
          (RealRooted.right_isRealRooted_of_prec_sequence $h _),
          (RealRooted.at_of_isRealRooted_sequence $h _),
          (RealRooted.at_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence
            $h _),
          RealRooted.left_isRealRooted_of_prec $h,
          RealRooted.right_isRealRooted_of_prec $h,
          RealRooted.right_isRealRooted_of_interlaces $h,
          RealRooted.left_isRealRooted_of_interlaces $h,
          RealRooted.left_isRealRooted_of_isRealRooted_pair $h,
          RealRooted.right_isRealRooted_of_isRealRooted_pair $h,
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)),
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)),
          RealRooted.isRealRooted_pow_of_isRealRooted $h _,
          RealRooted.reverse_isRealRooted $h,
          RealRooted.isRealRooted_of_reverse $h,
          RealRooted.X_pow_mul_reverse_isRealRooted $h _)
  | `(tactic| rr_mul_realrooted using $hp:term, $hq:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_mul_of_isRealRooted $hp $hq),
          (RealRooted.isRealRooted_mul_of_isRealRooted $hq $hp))
  | `(tactic|
      rr_mul_realrooted using
        left := $hp:term,
        right := $hq:term) =>
      `(tactic|
        rr_mul_realrooted using $hp, $hq)
  | `(tactic|
      rr_pow_realrooted using
        realrooted := $hp:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_pow_of_isRealRooted $hp $n))
  | `(tactic|
      rr_realrooted_reverse using
        realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.reverse_isRealRooted $h)
  | `(tactic|
      rr_realrooted_of_reverse using
        reverse_realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_reverse $h)
  | `(tactic|
      rr_realrooted_reflect using
        realrooted := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact RealRooted.reflect_isRealRooted $h $hN)
  | `(tactic|
      rr_realrooted_X_pow_mul_reverse using
        realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.X_pow_mul_reverse_isRealRooted $h _)
  | `(tactic|
      rr_realrooted_divX using
        coeff_zero := $h0:term,
        realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.divX_isRealRooted_of_coeff_zero $h0 $h)
  | `(tactic|
      rr_realrooted_of_divX using
        coeff_zero := $h0:term,
        divX_realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_divX $h0 $h)
  | `(tactic| rr_realrooted) =>
      `(tactic|
        first
          | rr_lookup
          | rr_realrooted using rr_lookup_term
          | assumption
          | rr_named_realrooted
          | (exact ⟨by rr_nonzero, by rr_splits⟩ <;> done)
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_interlaces using $hprec:term, $hdeg:term) =>
      `(tactic|
        rr_first_exact
          RealRooted.Prec.toInterlaces $hprec $hdeg,
          RealRooted.Prec.toInterlaces $hprec ($hdeg).symm)
  | `(tactic| rr_interlaces using $hprec:term) =>
      `(tactic|
        exact RealRooted.Prec.toInterlaces $hprec (by rr_close_side))
  | `(tactic| rr_interlaces) =>
      `(tactic|
        first
          | rr_named_interlaces
          | exact rr_lookup_interlaces_term)
  | `(tactic| rr_prec0 using $hprec:term) =>
      `(tactic|
        rr_first_exact
          $hprec,
          RealRooted.Prec.toPrec0 $hprec,
          RealRooted.Prec.toPrec0 (RealRooted.Interlaces.toPrec $hprec))
  | `(tactic| rr_prec using $hinter:term) =>
      `(tactic|
        rr_first_exact
          $hinter,
          RealRooted.Interlaces.toPrec $hinter,
          (fun n => RealRooted.Interlaces.toPrec ($hinter n)),
          (RealRooted.Interlaces.toPrec ($hinter _)))
  | `(tactic| rr_prec using $hprec0:term, $hf:term, $hg:term) =>
      `(tactic|
        exact RealRooted.Prec0.toPrec_of_ne $hprec0 $hf $hg)
  | `(tactic| rr_gsturm_cons using $hprec:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsGeneralizedSturmSeq] using And.intro $hprec $htail)
  | `(tactic| rr_sturm_cons using $hinter:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsSturmSeq] using And.intro $hinter $htail)
  | `(tactic| rr_sturm_base) =>
      `(tactic|
        simp [RealRooted.IsSturmSeq, RealRooted.IsGeneralizedSturmSeq])
  | `(tactic|
      rr_prec_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_step $hbase $hstep)
  | `(tactic|
      rr_prec_sequence_realrooted using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence $hbase $hstep))
  | `(tactic|
      rr_finish_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        rr_prec_sequence_realrooted using
          base := $hbase,
          step := $hstep)
  | `(tactic|
      rr_finish_sequence using
        prec := $hprec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_chain_from_step $hprec))
  | `(tactic|
      rr_finish_sequence using
        prec := $hprec:term,
        degree := $hdegree:term) =>
      `(tactic|
        first
          | exact RealRooted.interlaces_of_prec_chain $hprec $hdegree
          | exact RealRooted.interlaces_of_prec_chain $hprec (fun n => ($hdegree n).symm)
          | exact (RealRooted.interlaces_of_prec_chain $hprec $hdegree _)
          | exact (RealRooted.interlaces_of_prec_chain
              $hprec (fun n => ($hdegree n).symm) _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step $hprec))
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_finish_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_prec_sequence_branches_realrooted using
          base := $hbase,
          degree := $hbranch,
          same := $hsame,
          successor := $hsucc)
  | `(tactic|
      rr_finish_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_prec_sequence_branches_realrooted using
          base := $hbase,
          degree_branch := $hbranch,
          same := $hsame,
          successor := $hsucc)
  | `(tactic| rr_finish using $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact RealRooted.derivative_interlaces $h (by rr_close_side)
          | exact (RealRooted.derivative_interlaces $h (by rr_close_side)).toPrec
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.left_isRealRooted_of_prec_sequence $h)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.right_isRealRooted_of_prec_sequence $h)
          | rr_exact_realrooted_sequence_or_projection
              (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))
          | rr_exact_realrooted_sequence_or_projection $h
          | rr_exact_realrooted_pair_sequence_or_projection $h
          | rr_exact_realrooted_or_projection $h
          | rr_zero_or_splits using $h
          | exact RealRooted.natDegree_succ_of_interlaces $h
          | exact (RealRooted.natDegree_succ_of_interlaces $h).symm
          | exact RealRooted.Prec.toInterlaces $h (by rr_close_side)
          | exact RealRooted.Interlaces.toPrec $h
          | exact fun n => RealRooted.Interlaces.toPrec ($h n)
          | exact RealRooted.Interlaces.toPrec ($h _)
          | exact RealRooted.Prec.toPrec0 $h
          | exact RealRooted.Prec.toPrec0 (RealRooted.Interlaces.toPrec $h)
          | rr_close_side)
  | `(tactic| rr_finish using $hprec:term, $hdeg:term) =>
      `(tactic|
        first
          | exact RealRooted.interlaces_of_prec_chain $hprec $hdeg
          | exact RealRooted.interlaces_of_prec_chain $hprec (fun n => ($hdeg n).symm)
          | exact (RealRooted.interlaces_of_prec_chain $hprec $hdeg _)
          | exact (RealRooted.interlaces_of_prec_chain
              $hprec (fun n => ($hdeg n).symm) _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step $hprec)
          | exact RealRooted.Prec.toInterlaces $hprec $hdeg
          | exact RealRooted.Prec.toInterlaces $hprec ($hdeg).symm
          | exact RealRooted.prec_sequence_of_base_and_step $hprec $hdeg
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_sequence $hprec $hdeg)
          | simpa [RealRooted.IsGeneralizedSturmSeq] using
              And.intro $hprec $hdeg
          | simpa [RealRooted.IsSturmSeq] using And.intro $hprec $hdeg)
  | `(tactic| rr_finish using $hprec0:term, $hf:term, $hg:term) =>
      `(tactic| exact RealRooted.Prec0.toPrec_of_ne $hprec0 $hf $hg)
  | `(tactic| rr_finish using $hbase:term, $hbranch:term, $hsame:term, $hsucc:term) =>
      `(tactic|
        first
          | exact RealRooted.prec_sequence_of_base_and_degree_branches
              $hbase $hbranch $hsame $hsucc
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_sequence_degree_branches
                $hbase $hbranch $hsame $hsucc))
  | `(tactic| rr_finish) =>
      `(tactic|
        first
          | rr_lookup
          | assumption
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step rr_lookup_term)
          | exact RealRooted.interlaces_of_prec_chain rr_lookup_term rr_lookup_term
          | exact RealRooted.interlaces_of_prec_chain
              rr_lookup_term (fun n => (rr_lookup_term n).symm)
          | rr_exact_realrooted_sequence_or_projection rr_lookup_term
          | rr_exact_realrooted_pair_sequence_or_projection rr_lookup_term
          | rr_exact_realrooted_or_projection rr_lookup_term
          | exact RealRooted.natDegree_succ_of_interlaces rr_lookup_term
          | exact (RealRooted.natDegree_succ_of_interlaces rr_lookup_term).symm
          | exact rr_lookup_interlaces_term
          | exact RealRooted.derivative_interlaces (by rr_splits) (by rr_close_side)
          | exact (RealRooted.derivative_interlaces (by rr_splits) (by rr_close_side)).toPrec
          | exact RealRooted.Interlaces.toPrec rr_lookup_term
          | exact RealRooted.ne_zero_of_natDegree_eq_one (by rr_degree_eq_one)
          | (apply Polynomial.Splits.of_natDegree_le_one <;> rr_degree_le_one)
          | exact RealRooted.Prec.toPrec0 (RealRooted.Interlaces.toPrec rr_lookup_term)
          | (exact ⟨by rr_nonzero, by rr_splits⟩ <;> done)
          | rr_named_interlaces
          | rr_named_realrooted
          | rr_named_nonzero
          | rr_named_splits
          | rr_zero_or_splits
          | rr_sign
          | simp_all [
              RealRooted.Prec,
              RealRooted.Prec0,
              RealRooted.Interlaces,
              RealRooted.IsSturmSeq,
              RealRooted.IsGeneralizedSturmSeq]
          | rr_close_side)

end Tactic
end RealRooted
