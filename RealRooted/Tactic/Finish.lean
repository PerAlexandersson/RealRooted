module

public import RealRooted.SequenceClosure
public import RealRooted.Tactic.Lookup
public import RealRooted.Tactic.Named
public import RealRooted.Tactic.RecurrenceEval
public import RealRooted.Tactic.Sign
public import RealRooted.Tactic.SideGoals
public meta import RealRooted.SequenceClosure
public meta import RealRooted.Tactic.Lookup
public meta import RealRooted.Tactic.Named
public meta import RealRooted.Tactic.RecurrenceEval
public meta import RealRooted.Tactic.Sign
public meta import RealRooted.Tactic.SideGoals

/-!
# Finish tactic frontend

Syntax and elaboration for proof tails that consume the theorem backend in
`RealRooted.SequenceClosure`.
-/

public meta section

open Polynomial

namespace RealRooted

namespace Tactic

open Lean
open Lean.Meta
open Lean.Elab.Tactic

theorem splits_of_eq_zero_or_splits {p : ℝ[X]} (h : p = 0 ∨ p.Splits) :
    p.Splits :=
  h.elim (fun hp => hp ▸ Polynomial.Splits.zero) id

/-- Term form of `rr_lookup`: elaborates to `by rr_lookup`. -/
syntax (name := rr_lookup_term) "rr_lookup_term" : term
/-- Term form of `rr_realrooted`: elaborates to `by rr_realrooted`. -/
syntax (name := rr_realrooted_term) "rr_realrooted_term" : term
/-- Term proving an `Interlaces` fact from a strict interlacing found by `rr_lookup` together with a
degree equation found by `rr_lookup`, in either orientation. -/
syntax (name := rr_lookup_interlaces_term) "rr_lookup_interlaces_term" : term
/-- Closes `p.natDegree = 1`, or its symmetric form, by `rr_lookup [rr_degree]`. -/
syntax (name := rr_degree_eq_one) "rr_degree_eq_one" : tactic
/-- Closes `p.natDegree ≤ 1` from an assumption or a degree equation found by
`rr_lookup [rr_degree]`. -/
syntax (name := rr_degree_le_one) "rr_degree_le_one" : tactic
/-- Closes `p.natDegree = n` from `top_ne : p.coeff n ≠ 0` and
`above : ∀ m, n < m → p.coeff m = 0`. -/
syntax (name := rr_natDegree_from_top_above)
  "rr_natDegree_from_top_above" " using "
    "top_ne" ":=" term ","
    "above" ":=" term :
  tactic

/-- Closes `p.natDegree = n` from `above : ∀ m, n < m → p.coeff m = 0` and `top_eq`, an equation for
`p.coeff n` whose value `simp` shows to be nonzero. -/
syntax (name := rr_natDegree_from_top_eq_above)
  "rr_natDegree_from_top_above" " using "
    "top_eq" ":=" term ","
    "above" ":=" term :
  tactic

/-- Closes `p.natDegree = n` from `top_pos : 0 < p.coeff n` and
`above : ∀ m, n < m → p.coeff m = 0`. -/
syntax (name := rr_natDegree_from_top_pos_above)
  "rr_natDegree_from_top_above" " using "
    "top_pos" ":=" term ","
    "above" ":=" term :
  tactic

/-- Closes the goal by `exact` of the certificate `h`, or of one of its projections: the
nonvanishing, splitting or zero-or-splitting fact for a real-rooted polynomial, for the left or
right member of a real-rooted pair, a `StrictInterl` or an `Interlaces` fact, or for the product of
the two members of a pair. -/
syntax (name := rr_exact_realrooted_or_projection)
  "rr_exact_realrooted_or_projection" term :
  tactic

/-- Sequence form of `rr_exact_realrooted_or_projection`: closes the goal by `exact` of a
real-rooted sequence certificate `h`, or of its value, nonvanishing, splitting or zero-or-splitting
projection, at a row. -/
syntax (name := rr_exact_realrooted_sequence_or_projection)
  "rr_exact_realrooted_sequence_or_projection" term :
  tactic

/-- Applies `rr_exact_realrooted_sequence_or_projection` to the term `h`, whose side goals are
created by `refine` and closed by the tactic after `with`. -/
syntax (name := rr_exact_realrooted_refine_then)
  "rr_exact_realrooted_refine_then " term " with " tactic :
  tactic

/-- Closes the goal by `exact` of a real-rooted pair sequence certificate `h`, or of one of its
projections: the pair at a row, the left or right sequence, their nonvanishing, splitting or
zero-or-splitting facts, or the real-rootedness of the product of the two members. -/
syntax (name := rr_exact_realrooted_pair_sequence_or_projection)
  "rr_exact_realrooted_pair_sequence_or_projection" term :
  tactic

/-- Closes the goal with the first of the comma-separated terms that `apply` accepts, working with
reducible instances. It fails if no term applies. -/
syntax (name := rr_first_exact)
  "rr_first_exact" term,* :
  tactic

/-- Closes the goal by `exact` of the first term or, failing that, by `simpa using` the second
term. -/
syntax (name := rr_first_exact_or_simpa)
  "rr_first_exact_or_simpa" term ", " term :
  tactic

/-- Closes the goal by `exact` of the first term or, failing that, by `simpa [mul_assoc] using` the
second term. -/
syntax (name := rr_first_exact_or_simpa_mul_assoc)
  "rr_first_exact_or_simpa_mul_assoc" term ", " term :
  tactic

/-- Closes the goal by `exact` of the first term or, failing that, by
`simpa [mul_assoc, add_assoc] using` the second term. -/
syntax (name := rr_first_exact_or_simpa_mul_add_assoc)
  "rr_first_exact_or_simpa_mul_add_assoc" term ", " term :
  tactic

/-- Tries `rr_exact_realrooted_or_projection` on each of the comma-separated certificates in
turn. -/
syntax (name := rr_first_realrooted_or_projection)
  "rr_first_realrooted_or_projection" term,* :
  tactic

/-- Tries `rr_exact_realrooted_sequence_or_projection` on each of the comma-separated certificates
in turn, also after binding the certificate with `have`. -/
syntax (name := rr_first_realrooted_sequence_or_projection)
  "rr_first_realrooted_sequence_or_projection" term,* :
  tactic

/-- Closes the goal with the first comma-separated term that either applies directly or yields the
goal through `rr_exact_realrooted_sequence_or_projection`. -/
syntax (name := rr_first_exact_then_realrooted_sequence_or_projection)
  "rr_first_exact_then_realrooted_sequence_or_projection" term,* :
  tactic

/-- Closes `p ≠ 0` from the certificate `h`: a real-rooted, pair, `Interlaces` or `StrictInterl`
fact, or a sequence of such facts. -/
syntax (name := rr_nonzero) "rr_nonzero" " using " term : tactic
/-- Closes `p.Splits` from the certificate `h`: a real-rooted, pair, `Interlaces` or `StrictInterl`
fact, a sequence of such facts, or a power or reversal of a splitting polynomial. -/
syntax (name := rr_splits) "rr_splits" " using " term : tactic
/-- Closes `(p * q).Splits` from `left : p.Splits` and `right : q.Splits`, in either order. -/
syntax (name := rr_splits_mul)
  "rr_splits_mul" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
/-- Closes `(p ^ n).Splits` from `splits : p.Splits` and the `exponent` `n`. -/
syntax (name := rr_splits_pow)
  "rr_splits_pow" " using "
    "splits" ":=" term ","
    "exponent" ":=" term :
  tactic
/-- Closes `p.reverse.Splits` from `splits : p.Splits`. -/
syntax (name := rr_splits_reverse)
  "rr_splits_reverse" " using "
    "splits" ":=" term :
  tactic
/-- Closes `p.Splits` from `reverse_splits : p.reverse.Splits`. -/
syntax (name := rr_splits_of_reverse)
  "rr_splits_of_reverse" " using "
    "reverse_splits" ":=" term :
  tactic
/-- Closes `(reflect N p).Splits` from `splits : p.Splits` and `degree_bound : p.natDegree ≤ N`. -/
syntax (name := rr_splits_reflect)
  "rr_splits_reflect" " using "
    "splits" ":=" term ","
    "degree_bound" ":=" term :
  tactic
/-- Closes `(X ^ k * p.reverse).Splits` from `splits : p.Splits`. -/
syntax (name := rr_splits_X_pow_mul_reverse)
  "rr_splits_X_pow_mul_reverse" " using "
    "splits" ":=" term :
  tactic
/-- Closes `p.divX.Splits` from `coeff_zero : p.coeff 0 = 0` and `splits : p.Splits`. -/
syntax (name := rr_splits_divX)
  "rr_splits_divX" " using "
    "coeff_zero" ":=" term ","
    "splits" ":=" term :
  tactic
/-- Closes `p.Splits` from `coeff_zero : p.coeff 0 = 0` and `divX_splits : p.divX.Splits`. -/
syntax (name := rr_splits_of_divX)
  "rr_splits_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_splits" ":=" term :
  tactic
/-- Closes `p = 0 ∨ p.Splits` from the certificate `h`: a real-rooted, pair, `Interlaces` or
`StrictInterl` fact, or a sequence of such facts. -/
syntax (name := rr_zero_or_splits)
  "rr_zero_or_splits" " using " term :
  tactic
/-- Closes `p * q = 0 ∨ (p * q).Splits` from `left` and `right`, the zero-or-splits facts for `p`
and `q`. -/
syntax (name := rr_zero_or_splits_mul)
  "rr_zero_or_splits_mul" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
/-- Closes `p ^ n = 0 ∨ (p ^ n).Splits` from `zero_or_splits` for `p` and the `exponent` `n`. -/
syntax (name := rr_zero_or_splits_pow)
  "rr_zero_or_splits_pow" " using "
    "zero_or_splits" ":=" term ","
    "exponent" ":=" term :
  tactic
/-- Closes the zero-or-splits statement for `p.reverse` from `zero_or_splits` for `p`. -/
syntax (name := rr_zero_or_splits_reverse)
  "rr_zero_or_splits_reverse" " using "
    "zero_or_splits" ":=" term :
  tactic
/-- Closes the zero-or-splits statement for `p` from `reverse_zero_or_splits` for `p.reverse`. -/
syntax (name := rr_zero_or_splits_of_reverse)
  "rr_zero_or_splits_of_reverse" " using "
    "reverse_zero_or_splits" ":=" term :
  tactic
/-- Closes the zero-or-splits statement for `reflect N p` from `zero_or_splits` for `p` and
`degree_bound : p.natDegree ≤ N`. -/
syntax (name := rr_zero_or_splits_reflect)
  "rr_zero_or_splits_reflect" " using "
    "zero_or_splits" ":=" term ","
    "degree_bound" ":=" term :
  tactic
/-- Closes the zero-or-splits statement for `X ^ k * p.reverse` from `zero_or_splits` for `p`. -/
syntax (name := rr_zero_or_splits_X_pow_mul_reverse)
  "rr_zero_or_splits_X_pow_mul_reverse" " using "
    "zero_or_splits" ":=" term :
  tactic
/-- Closes the zero-or-splits statement for `p.divX` from `coeff_zero : p.coeff 0 = 0` and
`zero_or_splits` for `p`. -/
syntax (name := rr_zero_or_splits_divX)
  "rr_zero_or_splits_divX" " using "
    "coeff_zero" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic
/-- Closes the zero-or-splits statement for `p` from `coeff_zero : p.coeff 0 = 0` and
`divX_zero_or_splits` for `p.divX`. -/
syntax (name := rr_zero_or_splits_of_divX)
  "rr_zero_or_splits_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_zero_or_splits" ":=" term :
  tactic
/-- Closes `p ≠ 0 ∧ p.Splits` from the certificate `h`: a real-rooted, pair, `Interlaces` or
`StrictInterl` fact, a sequence of such facts, or a product, power or reversal of real-rooted
polynomials. -/
syntax (name := rr_realrooted) "rr_realrooted" " using " term : tactic
/-- Closes the real-rootedness of a product `p * q` from the real-rootedness certificates for `p`
and `q`, given in this order or swapped. -/
syntax (name := rr_mul_realrooted)
  "rr_mul_realrooted" " using " term ", " term :
  tactic
/-- Named form of `rr_mul_realrooted`: `left` and `right` are the real-rootedness certificates of
the two factors. -/
syntax (name := rr_mul_realrooted_named)
  "rr_mul_realrooted" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
/-- Closes the real-rootedness of `p ^ n` from `realrooted` for `p` and the `exponent` `n`. -/
syntax (name := rr_pow_realrooted)
  "rr_pow_realrooted" " using "
    "realrooted" ":=" term ","
    "exponent" ":=" term :
  tactic
/-- Closes the real-rootedness of `p.reverse` from `realrooted` for `p`. -/
syntax (name := rr_realrooted_reverse)
  "rr_realrooted_reverse" " using "
    "realrooted" ":=" term :
  tactic
/-- Closes the real-rootedness of `p` from `reverse_realrooted` for `p.reverse`. -/
syntax (name := rr_realrooted_of_reverse)
  "rr_realrooted_of_reverse" " using "
    "reverse_realrooted" ":=" term :
  tactic
/-- Closes the real-rootedness of `reflect N p` from `realrooted` for `p` and
`degree_bound : p.natDegree ≤ N`. -/
syntax (name := rr_realrooted_reflect)
  "rr_realrooted_reflect" " using "
    "realrooted" ":=" term ","
    "degree_bound" ":=" term :
  tactic
/-- Closes the real-rootedness of `X ^ k * p.reverse` from `realrooted` for `p`. -/
syntax (name := rr_realrooted_X_pow_mul_reverse)
  "rr_realrooted_X_pow_mul_reverse" " using "
    "realrooted" ":=" term :
  tactic
/-- Closes the real-rootedness of `p.divX` from `coeff_zero : p.coeff 0 = 0` and `realrooted` for
`p`. -/
syntax (name := rr_realrooted_divX)
  "rr_realrooted_divX" " using "
    "coeff_zero" ":=" term ","
    "realrooted" ":=" term :
  tactic
/-- Closes the real-rootedness of `p` from `coeff_zero : p.coeff 0 = 0` and `divX_realrooted` for
`p.divX`. -/
syntax (name := rr_realrooted_of_divX)
  "rr_realrooted_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_realrooted" ":=" term :
  tactic
/-- Closes `p ≠ 0` without a named certificate, trying `rr_lookup`, assumptions, linear factors,
products, powers, reversals and derivatives. -/
syntax (name := rr_nonzero_auto) "rr_nonzero" : tactic
/-- Closes `p.Splits` without a named certificate, trying `rr_lookup`, assumptions, linear factors,
monomials, products, powers and derivatives of interlacing polynomials. -/
syntax (name := rr_splits_auto) "rr_splits" : tactic
/-- Closes `p = 0 ∨ p.Splits` without a named certificate, trying `rr_lookup`, assumptions,
products, powers and `rr_splits`. -/
syntax (name := rr_zero_or_splits_auto) "rr_zero_or_splits" : tactic
/-- Closes `p ≠ 0 ∧ p.Splits` without a named certificate, trying `rr_lookup`, assumptions, named
wrapper lemmas, and `rr_nonzero` together with `rr_splits`. -/
syntax (name := rr_realrooted_auto) "rr_realrooted" : tactic

/-- Closes `Interlaces p q` from a strict interlacing (first term) and a degree equation (second
term), accepting the degree equation in either orientation. -/
syntax (name := rr_interlaces_with_degree)
  "rr_interlaces" " using " term ", " term : tactic

/-- Closes `Interlaces p q` from a strict interlacing; the degree side goal is closed by
`rr_close_side`. -/
syntax (name := rr_interlaces_auto_degree)
  "rr_interlaces" " using " term : tactic

/-- Closes `Interlaces p q` for named expressions, using the matching named `_interlaces` wrapper
lemma or `rr_lookup_interlaces_term`. -/
syntax (name := rr_interlaces_auto_named) "rr_interlaces" : tactic

/-- Closes `Interl p q` from the certificate `h`: an `Interl`, `StrictInterl` or `Interlaces`
fact. -/
syntax (name := rr_interl) "rr_interl" " using " term : tactic

/-- Closes `StrictInterl p q` from an `Interlaces p q` fact, or from a sequence of such facts. -/
syntax (name := rr_strict_interl_of_interlaces)
  "rr_strict_interl" " using " term :
  tactic

/-- Closes `StrictInterl f g` from `Interl f g` (first term) and the nonvanishing of `f` and `g`
(second and third terms). -/
syntax (name := rr_strict_interl_of_interl)
  "rr_strict_interl" " using " term ", " term ", " term : tactic

/-- Closes `IsGeneralizedSturmSeq (p :: q :: l)` from a `StrictInterl` fact for the first pair
(first term) and the certificate for the tail (second term). -/
syntax (name := rr_gsturm_cons)
  "rr_gsturm_cons" " using " term ", " term : tactic

/-- Closes `IsSturmSeq (p :: q :: l)` from an `Interlaces` fact for the first pair (first term) and
the certificate for the tail (second term). -/
syntax (name := rr_sturm_cons)
  "rr_sturm_cons" " using " term ", " term : tactic

/-- Closes the empty and singleton cases of `IsSturmSeq` and `IsGeneralizedSturmSeq` by `simp`. -/
syntax (name := rr_sturm_base) "rr_sturm_base" : tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` by induction from `base : StrictInterl (P 0) (P 1)`
and `step`, which passes the previous strict interlacing on to the next one. -/
syntax (name := rr_strict_interl_sequence)
  "rr_strict_interl_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by the `StrictInterl` induction of
`rr_strict_interl_sequence`, from `base` and `step`. -/
syntax (name := rr_strict_interl_sequence_realrooted)
  "rr_strict_interl_sequence_realrooted" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

/-- Sequence finisher: the same as `rr_strict_interl_sequence_realrooted`, from `base` and
`step`. -/
syntax (name := rr_finish_sequence_base_step)
  "rr_finish_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

/-- Closes the real-rootedness of a sequence from `strictInterl`, a chain of strict interlacings
`StrictInterl (P n) (P (n + 1))` for all `n`. -/
syntax (name := rr_finish_sequence_strict_interl)
  "rr_finish_sequence" " using "
    "strictInterl" ":=" term :
  tactic

/-- Closes `∀ n, Interlaces (P n) (P (n + 1))` from the chain `strictInterl` and the `degree`
increments `(P n).natDegree + 1 = (P (n + 1)).natDegree`. It falls back to real-rootedness of the
sequence. -/
syntax (name := rr_finish_sequence_strict_interl_degree)
  "rr_finish_sequence" " using "
    "strictInterl" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` by induction for sequences whose degree either
stays the same or increases by one. The arguments are `base`, `degree`, the same-degree step `same`
and the successor-degree step `successor`. -/
syntax (name := rr_strict_interl_sequence_branches)
  "rr_strict_interl_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_sequence_branches` whose degree dichotomy is named
`degree_branch`. -/
syntax (name := rr_strict_interl_sequence_branches_degree_branch)
  "rr_strict_interl_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` by the branched induction of
`rr_strict_interl_sequence_branches`. The arguments are `base`, `degree`, `same` and `successor`. -/
syntax (name := rr_strict_interl_sequence_branches_realrooted)
  "rr_strict_interl_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_sequence_branches_realrooted` whose degree dichotomy is named
`degree_branch`. -/
syntax (name := rr_strict_interl_sequence_branches_realrooted_degree_branch)
  "rr_strict_interl_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

/-- Sequence finisher for degree-plateau recurrences: the same as
`rr_strict_interl_sequence_branches_realrooted`, with arguments `base`, `degree`, `same` and
`successor`. -/
syntax (name := rr_finish_sequence_branches)
  "rr_finish_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

/-- Variant of `rr_finish_sequence_branches` whose degree dichotomy is named `degree_branch`. -/
syntax (name := rr_finish_sequence_branches_degree_branch)
  "rr_finish_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

/-- Closes the goal from the certificate `h`, trying exact use, derivative interlacing, projections
of real-rooted, pair and strict-interlacing certificates, and conversions between `Interlaces`,
`StrictInterl` and `Interl`. -/
syntax (name := rr_finish_using) "rr_finish" " using " term : tactic

/-- Closes a sequence goal from two certificates: a chain of strict interlacings and its degree
increments (giving `Interlaces`), a base and a step (giving strict interlacing or real-rootedness),
or the head and tail of a Sturm sequence. -/
syntax (name := rr_finish_using_interlaces_degree)
  "rr_finish" " using " term ", " term : tactic

/-- Closes `StrictInterl f g` from `Interl f g` (first term) and the nonvanishing of `f` and `g`
(second and third terms). -/
syntax (name := rr_finish_using_interl)
  "rr_finish" " using " term ", " term ", " term : tactic

/-- Closes a strict interlacing or real-rootedness goal for a degree-plateau sequence from `base`,
`degree`, `same` and `successor` given in this order. -/
syntax (name := rr_finish_using_sequence_branches)
  "rr_finish" " using " term ", " term ", " term ", " term : tactic

/-- Closes a real-rootedness, interlacing, nonvanishing or splitting goal without a named
certificate, trying `rr_lookup`, assumptions, sequence projections, derivative interlacing, the
named wrappers and `rr_close_side`. -/
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

private def closeNamedDirectOrStrictInterl (tacticName : Name) (target : Expr)
    (directSuffix : String) (closeStrictInterl : Ident → TacticM Unit) : TacticM Unit := do
  let some (cName, arg) ← findNamedPolynomialConstantApp? target
    | throwError "{tacticName} failed: could not find named polynomial in target: {target}"
  if ← closeNamedDirect? tacticName cName arg directSuffix then
    return
  for candidate in namedSuffixCandidates "_strictInterl" do
    if let some proof ← mkNamedTheoremApp? cName candidate arg then
      let hstrictInterl ← assertProofAs `hstrictInterl proof
      withMainContext do
        closeStrictInterl hstrictInterl
      return
  throwError "{tacticName} failed: no matching named final wrapper closes target: {target}"

/-- Closes `p ≠ 0` for a polynomial given by a named constant applied to an argument, using the
named theorem with suffix `_ne_zero`, or the `_strictInterl` wrapper via `rr_nonzero`. -/
elab "rr_named_nonzero" : tactic => do
  withMainContext do
    let target ← getMainTarget
    closeNamedDirectOrStrictInterl `rr_named_nonzero target "_ne_zero" fun hstrictInterl => do
      evalTactic (← `(tactic| rr_nonzero using $hstrictInterl:ident))

/-- Closes `p.Splits` for a polynomial given by a named constant applied to an argument, using the
named theorem with suffix `_splits`, or the `_strictInterl` wrapper via `rr_splits`. -/
elab "rr_named_splits" : tactic => do
  withMainContext do
    let target ← getMainTarget
    closeNamedDirectOrStrictInterl `rr_named_splits target "_splits" fun hstrictInterl => do
      evalTactic (← `(tactic| rr_splits using $hstrictInterl:ident))

/-- Closes `p ≠ 0 ∧ p.Splits` for a polynomial given by a named constant applied to an argument,
using the named theorem with suffix `_realRooted`, or `rr_named_nonzero` together with
`rr_named_splits`. -/
elab "rr_named_realrooted" : tactic => do
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some (cName, arg) ← findNamedPolynomialConstantApp? target
      | throwError "rr_named_realrooted failed: could not find named polynomial"
    if ← closeNamedDirect? `rr_named_realrooted cName arg "_realRooted" then
      return
    evalTactic (← `(tactic| exact ⟨by rr_named_nonzero, by rr_named_splits⟩))

/-- Closes `Interlaces p q` for a named expression, using the named theorem with suffix
`_interlaces`. -/
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
        with_reducible_and_instances
          first
            | exact RealRooted.StrictInterl.toInterlaces rr_lookup_term rr_lookup_term
            | exact RealRooted.StrictInterl.toInterlaces rr_lookup_term (by
                symm
                rr_lookup))
  | `(tactic| rr_degree_eq_one) =>
      `(tactic|
        with_reducible_and_instances
          first
            | rr_lookup [rr_degree]
            | (symm; rr_lookup [rr_degree]))
  | `(tactic| rr_degree_le_one) =>
      `(tactic|
        with_reducible_and_instances
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
          RealRooted.left_isRealRooted_of_strictInterl $h,
          RealRooted.right_isRealRooted_of_strictInterl $h,
          RealRooted.left_ne_zero_of_strictInterl $h,
          RealRooted.right_ne_zero_of_strictInterl $h,
          RealRooted.left_splits_of_strictInterl $h,
          RealRooted.right_splits_of_strictInterl $h,
          RealRooted.left_eq_zero_or_splits_of_strictInterl $h,
          RealRooted.right_eq_zero_or_splits_of_strictInterl $h,
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
        with_reducible_and_instances
          solve
            $[ | apply $hs]*)
  | `(tactic| rr_first_exact_or_simpa $hdirect:term, $hnormalized:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact $hdirect
            | simpa using $hnormalized)
  | `(tactic| rr_first_exact_or_simpa_mul_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact $hdirect
            | simpa [mul_assoc] using $hnormalized)
  | `(tactic| rr_first_exact_or_simpa_mul_add_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact $hdirect
            | simpa [mul_assoc, add_assoc] using $hnormalized)
  | `(tactic| rr_first_realrooted_or_projection $[$hs:term],*) =>
      `(tactic|
        with_reducible_and_instances
          first
            $[ | rr_exact_realrooted_or_projection $hs]*)
  | `(tactic| rr_first_realrooted_sequence_or_projection $[$hs:term],*) =>
      `(tactic|
        with_reducible_and_instances
          first
            $[ | (have hcertificate := $hs
                  rr_exact_realrooted_sequence_or_projection hcertificate)]*
            $[ | rr_exact_realrooted_sequence_or_projection $hs]*)
  | `(tactic| rr_first_exact_then_realrooted_sequence_or_projection $[$hs:term],*) =>
      `(tactic|
        with_reducible_and_instances
          solve
            $[ | apply $hs]*
            $[ | (have hcertificate := $hs
                  rr_exact_realrooted_sequence_or_projection hcertificate)]*
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
            (RealRooted.left_isRealRooted_of_strictInterl_sequence $h)),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_strictInterl_sequence $h) _),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_strictInterl_sequence $h)),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_strictInterl_sequence $h) _),
          RealRooted.ne_zero_of_isRealRooted_sequence $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence $h _),
          RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_ne_zero_of_strictInterl $h,
          RealRooted.right_ne_zero_of_strictInterl $h,
          RealRooted.right_ne_zero_of_interlaces $h,
          RealRooted.left_ne_zero_of_interlaces $h,
          RealRooted.ne_zero_of_isRealRooted $h,
          RealRooted.left_ne_zero_of_isRealRooted_pair $h,
          RealRooted.right_ne_zero_of_isRealRooted_pair $h)
  | `(tactic| rr_nonzero) =>
      `(tactic|
        with_reducible_and_instances
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
            | (refine Polynomial.derivative_ne_zero.mpr ?_ <;> rr_close_side)
            | (intro hzero; simp_all [RealRooted.StrictInterl, RealRooted.Interlaces])
            | simp_all [RealRooted.StrictInterl, RealRooted.Interlaces])
  | `(tactic| rr_splits using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))),
          (RealRooted.splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)) _),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_strictInterl_sequence $h)),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_strictInterl_sequence $h) _),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_strictInterl_sequence $h)),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_strictInterl_sequence $h) _),
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
          RealRooted.left_splits_of_strictInterl $h,
          RealRooted.right_splits_of_strictInterl $h,
          RealRooted.right_splits_of_interlaces $h,
          RealRooted.left_splits_of_interlaces $h,
          RealRooted.splits_of_isRealRooted $h,
          RealRooted.left_splits_of_isRealRooted_pair $h,
          RealRooted.right_splits_of_isRealRooted_pair $h,
          RealRooted.mul_splits_of_isRealRooted_pair $h,
          RealRooted.swap_mul_splits_of_isRealRooted_pair $h,
          RealRooted.splits_pow_of_isRealRooted $h _,
          Polynomial.Splits.pow $h _,
          Polynomial.Splits.reverse $h,
          Polynomial.Splits.of_reverse $h,
          Polynomial.Splits.X_pow_mul_reverse $h _,
          (RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mpr $h,
          (RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mp $h)
  | `(tactic|
      rr_splits_mul using
        left := $hleft:term,
        right := $hright:term) =>
      `(tactic|
        rr_first_exact
          Polynomial.Splits.mul $hleft $hright,
          Polynomial.Splits.mul $hright $hleft)
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
        exact Polynomial.Splits.reverse $h)
  | `(tactic|
      rr_splits_of_reverse using
        reverse_splits := $h:term) =>
      `(tactic|
        exact Polynomial.Splits.of_reverse $h)
  | `(tactic|
      rr_splits_reflect using
        splits := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact Polynomial.Splits.reflect $h $hN)
  | `(tactic|
      rr_splits_X_pow_mul_reverse using
        splits := $h:term) =>
      `(tactic|
        exact Polynomial.Splits.X_pow_mul_reverse $h _)
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
        with_reducible_and_instances
          solve
            | rr_lookup
            | rr_splits using rr_lookup_term
            | assumption
            | apply Polynomial.Splits.C
            | apply Polynomial.Splits.X
            | apply Polynomial.Splits.X_add_C
            | apply Polynomial.Splits.X_sub_C
            | apply Polynomial.Splits.X_pow
            | apply Polynomial.Splits.C_mul_X_pow
            | (refine RealRooted.left_splits_of_interlaces
                  (RealRooted.derivative_interlaces_of_natDegree_ne_zero ?_ ?_) <;>
                [assumption; rr_close_side])
            | rr_named_splits
            | (apply Polynomial.Splits.mul <;> rr_splits)
            | (apply Polynomial.Splits.pow <;> rr_splits)
            | simp [add_comm]
            | (apply Polynomial.Splits.of_natDegree_le_one <;> rr_degree_le_one)
            | simp_all [RealRooted.StrictInterl, RealRooted.Interlaces])
  | `(tactic| rr_zero_or_splits using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)) _),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_strictInterl_sequence $h)),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.left_isRealRooted_of_strictInterl_sequence $h) _),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_strictInterl_sequence $h)),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.right_isRealRooted_of_strictInterl_sequence $h) _),
          RealRooted.eq_zero_or_splits_of_isRealRooted $h,
          RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h,
          RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h,
          (Or.inr
            ((splits_of_eq_zero_or_splits
                (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)).mul
              (splits_of_eq_zero_or_splits
                (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)))),
          (Or.inr
            ((splits_of_eq_zero_or_splits
                (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)).mul
              (splits_of_eq_zero_or_splits
                (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)))),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.left_eq_zero_or_splits_of_strictInterl $h,
          RealRooted.right_eq_zero_or_splits_of_strictInterl $h,
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
          Or.inr (Polynomial.Splits.reverse $h),
          Or.inr (Polynomial.Splits.of_reverse $h),
          Or.inr (Polynomial.Splits.X_pow_mul_reverse $h _),
          Or.inr ((RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mpr $h),
          Or.inr ((RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mp $h),
          Or.inr ((splits_of_eq_zero_or_splits $h).pow _),
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
          (Or.inr ((splits_of_eq_zero_or_splits $hp).mul
            (splits_of_eq_zero_or_splits $hq))),
          (Or.inr ((splits_of_eq_zero_or_splits $hq).mul
            (splits_of_eq_zero_or_splits $hp))))
  | `(tactic|
      rr_zero_or_splits_pow using
        zero_or_splits := $h:term,
        exponent := $n:term) =>
      `(tactic|
        exact Or.inr ((splits_of_eq_zero_or_splits $h).pow $n))
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
        with_reducible_and_instances
          first
            | rr_lookup
            | rr_zero_or_splits using rr_lookup_term
            | assumption
            | (apply Or.inr; apply Polynomial.Splits.mul <;>
                (apply splits_of_eq_zero_or_splits; rr_zero_or_splits))
            | (apply Or.inr; apply Polynomial.Splits.pow;
                apply splits_of_eq_zero_or_splits; rr_zero_or_splits)
            -- `apply` rejects a non-disjunction before `rr_splits` runs; `exact Or.inr (by …)`
            -- would elaborate the `by` block first
            | (apply Or.inr; rr_splits; done)
            | simp_all [RealRooted.StrictInterl, RealRooted.Interlaces])
  | `(tactic| rr_realrooted using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n)),
          (RealRooted.left_isRealRooted_of_interlaces ($h _)),
          (RealRooted.left_isRealRooted_of_strictInterl_sequence $h),
          (RealRooted.left_isRealRooted_of_strictInterl_sequence $h _),
          (RealRooted.right_isRealRooted_of_strictInterl_sequence $h),
          (RealRooted.right_isRealRooted_of_strictInterl_sequence $h _),
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
          RealRooted.left_isRealRooted_of_strictInterl $h,
          RealRooted.right_isRealRooted_of_strictInterl $h,
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
        with_reducible_and_instances
          first
            | rr_lookup
            | rr_realrooted using rr_lookup_term
            | assumption
            | rr_named_realrooted
            | (exact ⟨by rr_nonzero, by rr_splits⟩ <;> done)
            | simp_all [RealRooted.StrictInterl, RealRooted.Interlaces])
  | `(tactic| rr_interlaces using $hstrictInterl:term, $hdeg:term) =>
      `(tactic|
        rr_first_exact
          RealRooted.StrictInterl.toInterlaces $hstrictInterl $hdeg,
          RealRooted.StrictInterl.toInterlaces $hstrictInterl ($hdeg).symm)
  | `(tactic| rr_interlaces using $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.toInterlaces $hstrictInterl (by rr_close_side))
  | `(tactic| rr_interlaces) =>
      `(tactic|
        with_reducible_and_instances
          first
            | rr_named_interlaces
            | exact rr_lookup_interlaces_term)
  | `(tactic| rr_interl using $hstrictInterl:term) =>
      `(tactic|
        rr_first_exact
          $hstrictInterl,
          RealRooted.StrictInterl.toInterl $hstrictInterl,
          RealRooted.StrictInterl.toInterl (RealRooted.Interlaces.toStrictInterl $hstrictInterl))
  | `(tactic| rr_strict_interl using $hinter:term) =>
      `(tactic|
        rr_first_exact
          $hinter,
          RealRooted.Interlaces.toStrictInterl $hinter,
          (fun n => RealRooted.Interlaces.toStrictInterl ($hinter n)),
          (RealRooted.Interlaces.toStrictInterl ($hinter _)))
  | `(tactic| rr_strict_interl using $hinterl:term, $hf:term, $hg:term) =>
      `(tactic|
        exact RealRooted.Interl.toStrictInterl_of_ne $hinterl $hf $hg)
  | `(tactic| rr_gsturm_cons using $hstrictInterl:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsGeneralizedSturmSeq] using And.intro $hstrictInterl $htail)
  | `(tactic| rr_sturm_cons using $hinter:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsSturmSeq] using And.intro $hinter $htail)
  | `(tactic| rr_sturm_base) =>
      `(tactic|
        simp [RealRooted.IsSturmSeq, RealRooted.IsGeneralizedSturmSeq])
  | `(tactic|
      rr_strict_interl_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        exact RealRooted.strictInterl_sequence_of_base_and_step $hbase $hstep)
  | `(tactic|
      rr_strict_interl_sequence_realrooted using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_strictInterl_sequence $hbase $hstep))
  | `(tactic|
      rr_finish_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        rr_strict_interl_sequence_realrooted using
          base := $hbase,
          step := $hstep)
  | `(tactic|
      rr_finish_sequence using
        strictInterl := $hstrictInterl:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_strictInterl_chain_from_step $hstrictInterl))
  | `(tactic|
      rr_finish_sequence using
        strictInterl := $hstrictInterl:term,
        degree := $hdegree:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact RealRooted.interlaces_of_strictInterl_chain $hstrictInterl $hdegree
            | exact RealRooted.interlaces_of_strictInterl_chain
                $hstrictInterl (fun n => ($hdegree n).symm)
            | exact (RealRooted.interlaces_of_strictInterl_chain $hstrictInterl $hdegree _)
            | exact (RealRooted.interlaces_of_strictInterl_chain
                $hstrictInterl (fun n => ($hdegree n).symm) _)
            | rr_exact_realrooted_sequence_or_projection
                (RealRooted.isRealRooted_of_strictInterl_chain_from_step $hstrictInterl))
  | `(tactic|
      rr_strict_interl_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.strictInterl_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_strict_interl_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.strictInterl_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_strict_interl_sequence_branches_realrooted using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_strictInterl_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_strict_interl_sequence_branches_realrooted using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_strictInterl_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_finish_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_strict_interl_sequence_branches_realrooted using
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
        rr_strict_interl_sequence_branches_realrooted using
          base := $hbase,
          degree_branch := $hbranch,
          same := $hsame,
          successor := $hsucc)
  | `(tactic| rr_finish using $h:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact $h
            | (refine RealRooted.derivative_interlaces_of_natDegree_ne_zero $h ?_ <;> rr_close_side)
            | (refine
                  (RealRooted.derivative_interlaces_of_natDegree_ne_zero $h ?_).toStrictInterl <;>
                rr_close_side)
            | rr_exact_realrooted_sequence_or_projection
                (RealRooted.left_isRealRooted_of_strictInterl_sequence $h)
            | rr_exact_realrooted_sequence_or_projection
                (RealRooted.right_isRealRooted_of_strictInterl_sequence $h)
            | rr_exact_realrooted_sequence_or_projection
                (fun n => RealRooted.left_isRealRooted_of_interlaces ($h n))
            | rr_exact_realrooted_sequence_or_projection $h
            | rr_exact_realrooted_pair_sequence_or_projection $h
            | rr_exact_realrooted_or_projection $h
            | rr_zero_or_splits using $h
            | exact RealRooted.natDegree_succ_of_interlaces $h
            | exact (RealRooted.natDegree_succ_of_interlaces $h).symm
            | (refine RealRooted.StrictInterl.toInterlaces $h ?_ <;> rr_close_side)
            | exact RealRooted.Interlaces.toStrictInterl $h
            | exact fun n => RealRooted.Interlaces.toStrictInterl ($h n)
            | exact RealRooted.Interlaces.toStrictInterl ($h _)
            | exact RealRooted.StrictInterl.toInterl $h
            | exact RealRooted.StrictInterl.toInterl (RealRooted.Interlaces.toStrictInterl $h)
            | rr_close_side)
  | `(tactic| rr_finish using $hstrictInterl:term, $hdeg:term) =>
      `(tactic|
        first
          | exact RealRooted.interlaces_of_strictInterl_chain $hstrictInterl $hdeg
          | exact RealRooted.interlaces_of_strictInterl_chain
              $hstrictInterl (fun n => ($hdeg n).symm)
          | exact (RealRooted.interlaces_of_strictInterl_chain $hstrictInterl $hdeg _)
          | exact (RealRooted.interlaces_of_strictInterl_chain
              $hstrictInterl (fun n => ($hdeg n).symm) _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_strictInterl_chain_from_step $hstrictInterl)
          | exact RealRooted.StrictInterl.toInterlaces $hstrictInterl $hdeg
          | exact RealRooted.StrictInterl.toInterlaces $hstrictInterl ($hdeg).symm
          | exact RealRooted.strictInterl_sequence_of_base_and_step $hstrictInterl $hdeg
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_strictInterl_sequence $hstrictInterl $hdeg)
          | simpa [RealRooted.IsGeneralizedSturmSeq] using
              And.intro $hstrictInterl $hdeg
          | simpa [RealRooted.IsSturmSeq] using And.intro $hstrictInterl $hdeg)
  | `(tactic| rr_finish using $hinterl:term, $hf:term, $hg:term) =>
      `(tactic| exact RealRooted.Interl.toStrictInterl_of_ne $hinterl $hf $hg)
  | `(tactic| rr_finish using $hbase:term, $hbranch:term, $hsame:term, $hsucc:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact RealRooted.strictInterl_sequence_of_base_and_degree_branches
                $hbase $hbranch $hsame $hsucc
            | rr_exact_realrooted_sequence_or_projection
                (RealRooted.isRealRooted_of_strictInterl_sequence_degree_branches
                  $hbase $hbranch $hsame $hsucc))
  | `(tactic| rr_finish) =>
      `(tactic|
        first
          | rr_lookup
          | assumption
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_strictInterl_chain_from_step rr_lookup_term)
          | exact RealRooted.interlaces_of_strictInterl_chain rr_lookup_term rr_lookup_term
          | exact RealRooted.interlaces_of_strictInterl_chain
              rr_lookup_term (fun n => (rr_lookup_term n).symm)
          | rr_exact_realrooted_sequence_or_projection rr_lookup_term
          | rr_exact_realrooted_pair_sequence_or_projection rr_lookup_term
          | rr_exact_realrooted_or_projection rr_lookup_term
          | exact RealRooted.natDegree_succ_of_interlaces rr_lookup_term
          | exact (RealRooted.natDegree_succ_of_interlaces rr_lookup_term).symm
          | exact rr_lookup_interlaces_term
          | (refine RealRooted.derivative_interlaces_of_natDegree_ne_zero ?_ ?_ <;>
              [rr_splits; rr_close_side])
          | (refine (RealRooted.derivative_interlaces_of_natDegree_ne_zero ?_ ?_).toStrictInterl <;>
              [rr_splits; rr_close_side])
          | exact RealRooted.Interlaces.toStrictInterl rr_lookup_term
          | exact RealRooted.StrictInterl.toInterl rr_lookup_term
          | (refine RealRooted.ne_zero_of_natDegree_eq_one ?_ <;> rr_degree_eq_one)
          | (apply Polynomial.Splits.of_natDegree_le_one <;> rr_degree_le_one)
          | exact RealRooted.StrictInterl.toInterl
              (RealRooted.Interlaces.toStrictInterl rr_lookup_term)
          | (exact ⟨by rr_nonzero, by rr_splits⟩ <;> done)
          | rr_named_interlaces
          | rr_named_realrooted
          | rr_named_nonzero
          | rr_named_splits
          | rr_zero_or_splits
          | rr_sign
          | simp_all [
              RealRooted.StrictInterl,
              RealRooted.Interl,
              RealRooted.Interlaces,
              RealRooted.IsSturmSeq,
              RealRooted.IsGeneralizedSturmSeq]
          | rr_close_side)

end Tactic
end RealRooted
