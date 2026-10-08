import RealRooted.Tactic.Recurrence.Degree
import RealRooted.DerivativeRecurrence.Interlacing

/-!
# Degrees of derivative recurrences whose top terms cancel

`rr_row_cancel` closes `(P t).natDegree = e`, `P t ≠ 0`, `0 < (P t).leadingCoeff` and the
conjunction `(P t).natDegree = e ∧ 0 < (P t).leadingCoeff` for a first-order derivative
recurrence `P (n + 1) = A n * (P n)' + B n * P n` whose top terms may cancel, with
`RealRooted.derivRec_natDegree_eq_and_leadingCoeff_pos_of_cancel`.

A numeric probe (exact rows, `linRecRows?`) fixes the number of rows dropped, the degree law
`D n = D₀ + d * ((n + e) / p)` (`fitDegreeLaw`), the bound `m` of the degrees of `A n`
(`m + 1`) and `B n` (`m`), and for each residue of `n` modulo `p` whether the top terms grow
or cancel.  The side goals are discharged after a residue decomposition of `n`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- A linear function that is nonnegative at both ends of an interval is nonnegative on it. -/
theorem cancel_lin_nonneg {a b D j : ℝ} (hj : 0 ≤ j) (hjD : j ≤ D) (hb : 0 ≤ b)
    (hD : 0 ≤ a * D + b) : 0 ≤ a * j + b := by
  rcases le_total 0 a with ha | ha
  · nlinarith [mul_nonneg ha hj]
  · nlinarith [mul_nonneg (neg_nonneg.2 ha) (sub_nonneg.2 hjD)]

/-- The numeric data of a cancelling first-order derivative recurrence. -/
structure CancelPlan where
  /-- the rows dropped beyond the shift of the recurrence -/
  extra : Nat
  /-- the degree law of the shifted sequence -/
  law : DegreeLaw
  /-- the degrees of `A n` and `B n` are at most `m + 1` and `m` -/
  m : Nat
  /-- per residue of `n` modulo `law.p`: do the top terms grow (`true`) or cancel (`false`)? -/
  grow : Array Bool

/-- Read the degree law, `m` and the growth pattern off the exact rows of `r`. -/
def cancelPlan (r : RowRec) : MetaM (Except MessageData CancelPlan) := do
  let some L ← linRec? r.P | return .error m!"{r.P}: not a linear recurrence"
  let some rows ← linRecRows? L 30 | return .error m!"{r.P}: the rows cannot be computed"
  let degs := rows.map (·.degInt)
  let some law := fitDegreeLaw degs r.shift (r.shift + 2)
    | return .error m!"the degrees {degs.toList.take 8} follow no degree law"
  let extra := law.drop - r.shift
  let some Af := r.coeffs[0]? | return .error m!"missing coefficient"
  let some Bf := r.coeffs[1]? | return .error m!"missing coefficient"
  let mut m := 1
  let mut coeffs : Array (QPoly × QPoly) := #[]
  for n in [0:16] do
    let some a ← evalCoeffAt? Af (n + extra) | return .error m!"coefficients not recognized"
    let some b ← evalCoeffAt? Bf (n + extra) | return .error m!"coefficients not recognized"
    if !a.isZero then m := max m (a.natDegree - 1)
    if !b.isZero then m := max m b.natDegree
    coeffs := coeffs.push (a, b)
  let mut grow : Array Bool := #[]
  for ρ in [0:law.p] do
    let mut pos := true
    let mut zero := true
    for i in [0:4] do
      let n := ρ + law.p * i
      let (a, b) := coeffs[n]!
      let c := a.coeff (m + 1) * (law.deg n : Rat) + b.coeff m
      let step := (law.deg (n + 1) : Int) - law.deg n
      if c > 0 then zero := false
      else if c == 0 then pos := false
      else return .error m!"the top coefficient is negative at n = {n}"
      if c > 0 && step != m then
        return .error m!"the degree grows by {step}, not {m}, at n = {n}"
      if c == 0 && step + 1 != m then
        return .error m!"the degree grows by {step}, not {m} - 1, at n = {n}"
    if !(pos || zero) then return .error m!"the top terms grow and cancel for n ≡ {ρ}"
    grow := grow.push pos
  return .ok { extra, law, m, grow }

/-- The (unhygienic) names of the variables `n = p * k + r` of a residue decomposition. -/
private def cancelN : Ident := mkIdent `rr_n
private def cancelK : Ident := mkIdent `rr_k

/-- Normalize the arithmetic of a periodic degree law after `n = p * q + r`. -/
private def cancelNatNorm (p : Nat) : TacticM (TSyntax `tactic) :=
  `(tactic| (first
    | simp only [Nat.add_assoc, Nat.mul_add_div (show 0 < $(rowNumLit p) by norm_num),
        Nat.mul_div_cancel_left _ (show 0 < $(rowNumLit p) by norm_num), Nat.mul_add_mod,
        Nat.mul_mod_right, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceSub, Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.add_sub_add_left,
        Nat.add_sub_cancel_left, ← Nat.mul_sub, Nat.reduceEqDiff, Nat.div_one, one_mul,
        ↓reduceIte, ite_true, ite_false]
    | skip))

/-- The residue decomposition `n = p * k + r` of `rr_n`, one goal for each residue. -/
private def cancelResidue (p : Nat) : TacticM (TSyntax `tactic) :=
  if p ≤ 1 then `(tactic| skip) else
  `(tactic| (
    obtain ⟨$cancelK, rr_r, rr_hr, rr_h⟩ : ∃ q r, r < $(rowNumLit p) ∧
        $cancelN = $(rowNumLit p) * q + r :=
      ⟨$cancelN / $(rowNumLit p), $cancelN % $(rowNumLit p), by lia, by lia⟩
    subst rr_h
    interval_cases rr_r))

/-- Compute the coefficients of the explicit polynomials in the goal. -/
private def cancelCoeffSimp : TacticM (TSyntax `tactic) :=
  `(tactic| (
    simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
      Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat, Polynomial.coeff_ofNat_zero,
      Polynomial.coeff_ofNat_succ, Polynomial.coeff_zero, neg_mul, one_mul, Nat.reduceSub,
      Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, ite_true, ite_false] <;>
    push_cast <;> (first | norm_num | skip)))

/-- Close an inequality between real rational functions of natural numbers. -/
private def cancelFinish : TacticM (TSyntax `tactic) :=
  `(tactic| first
    | done
    | positivity
    | (refine ne_of_gt ?_; positivity)
    | nlinarith [(Nat.cast_nonneg $cancelN : (0 : ℝ) ≤ $cancelN)]
    | nlinarith [(Nat.cast_nonneg $cancelK : (0 : ℝ) ≤ $cancelK)]
    | rr_row_field
    | (ring_nf; positivity)
    | fail)

/-- Run `tac` on the goal `g`, which it must close. -/
private def cancelRun (what : String) (g : MVarId) (tac : TacticM Unit) : TacticM Unit := do
  setGoals [g]
  try tac catch e => throwError "side goal {what}: {e.toMessageData}"
  unless (← getGoals).isEmpty do throwError "rr_row_cancel: goals remain after side goal {what}"

/-- A side goal about an explicit base row `P 0`: by `rowSideGoal`, by `rr_row_side` (which
also proves `HasNonnegCoeffs` once `RealRooted.Tactic.RowInterlacing` is imported), or by
simplification (numerals have no `leadingCoeff` simp lemma). -/
private def cancelBase (P : Ident) : TacticM Unit := do
  if ← rowSucceeds (do
      rowSideGoal (some P)
      unless (← getGoals).isEmpty do throwError "goals remain") then return
  if ← rowSucceeds (do
      evalTactic (← `(tactic| rr_row_side))
      unless (← getGoals).isEmpty do throwError "goals remain") then return
  evalTactic (← `(tactic| (
    beta_reduce
    first
      | (simp [$P:ident, Polynomial.leadingCoeff]; done)
      | (simp [$P:ident, ← Polynomial.C_ofNat]; done))))

/-- The side goal `hmult`: `j ≤ D n → 0 ≤ (A n).coeff (i + 1) * j + (B n).coeff i`, split by
the residue of `n`, by `i ≤ m` and, for `i ≤ m`, by the endpoints of `0 ≤ j ≤ D n`. -/
private def cancelMult (p m : Nat) : TacticM Unit := do
  let (i, j, hj) := (mkIdent `rr_i, mkIdent `rr_j, mkIdent `rr_hj)
  evalTactic (← `(tactic| intro $cancelN:ident $i:ident $j:ident $hj:ident))
  evalTactic (← `(tactic| revert $hj:ident))
  evalTactic (← cancelResidue p)
  let norm ← cancelNatNorm p
  let coeff ← cancelCoeffSimp
  let fin ← cancelFinish
  for g in ← getGoals do
    setGoals [g]
    evalTactic norm
    evalTactic (← `(tactic| intro $hj:ident))
    evalTactic (← `(tactic| have hj' := (Nat.cast_le (α := ℝ)).mpr $hj))
    evalTactic (← `(tactic| rcases Nat.lt_or_ge $(rowNumLit m) $i with hi | hi))
    let [g₁, g₂] ← getGoals | throwError "rr_row_cancel: unexpected goals"
    cancelRun "hmult (i > m)" g₁ do
      evalTactic (← `(tactic| (
        obtain ⟨i', hi'⟩ : ∃ i', $i = i' + ($(rowNumLit m) + 1) :=
          ⟨$i - ($(rowNumLit m) + 1), by lia⟩
        subst hi')))
      evalTactic (← `(tactic| (first | simp only [Nat.add_assoc, Nat.reduceAdd] | skip)))
      evalTactic (← `(tactic| ($coeff:tactic <;> first | done | positivity)))
    cancelRun "hmult (i ≤ m)" g₂ do
      evalTactic (← `(tactic| interval_cases $i:ident))
      for g' in ← getGoals do
        setGoals [g']
        evalTactic (← `(tactic| refine cancel_lin_nonneg (Nat.cast_nonneg _) hj' ?_ ?_))
        for g'' in ← getGoals do
          setGoals [g'']
          evalTactic (← `(tactic| ($coeff:tactic <;> $fin:tactic)))
      setGoals []
  setGoals []

/-- The side goal `hstep`, one residue of `n` after the other. -/
private def cancelStep (p : Nat) (grow : Array Bool) : TacticM Unit := do
  evalTactic (← `(tactic| intro $cancelN:ident))
  evalTactic (← cancelResidue p)
  let norm ← cancelNatNorm p
  let coeff ← cancelCoeffSimp
  let fin ← cancelFinish
  let gs ← getGoals
  for (g, ρ) in gs.zip (List.range gs.length) do
    setGoals [g]
    evalTactic norm
    if grow[ρ]! then
      evalTactic (← `(tactic| refine Or.inl ⟨?_, ?_⟩))
      let [g₁, g₂] ← getGoals | throwError "rr_row_cancel: unexpected goals"
      cancelRun "hstep (growth)" g₁ (evalTactic (← `(tactic| ($coeff:tactic <;> $fin:tactic))))
      cancelRun "hstep (degree)" g₂ (evalTactic (← `(tactic| lia)))
    else
      evalTactic (← `(tactic| refine Or.inr ⟨?_, ?_, ?_, ?_⟩))
      let [g₁, g₂, g₃, g₄] ← getGoals | throwError "rr_row_cancel: unexpected goals"
      cancelRun "hstep (cancellation)" g₁ do
        evalTactic (← `(tactic| ($coeff:tactic <;> first | done | ring1 | rr_linrec_field)))
      cancelRun "hstep (degree)" g₂ (evalTactic (← `(tactic| lia)))
      cancelRun "hstep (sign)" g₃ (evalTactic (← `(tactic| ($coeff:tactic <;> $fin:tactic))))
      cancelRun "hstep (next)" g₄ (evalTactic (← `(tactic| ($coeff:tactic <;> $fin:tactic))))
  setGoals []

/-- The kind of a goal about the rows of a sequence. -/
private def cancelGoalKind? (tgt : Expr) : Option String :=
  match tgt.getAppFnArgs with
  | (``Eq, #[_, a, _]) =>
      if a.getAppFn.isConstOf ``Polynomial.natDegree then some "natDegree" else none
  | (``Ne, _) => some "ne_zero"
  | (``LT.lt, #[_, _, _, b]) =>
      if b.getAppFn.isConstOf ``Polynomial.leadingCoeff then some "leadingCoeff_pos" else none
  | (``And, _) => some "natDegree_leadingCoeff_pos"
  | _ => none

/-- The core of `rr_row_cancel` for a goal of the given kind (`"natDegree"`, `"ne_zero"`,
`"leadingCoeff_pos"` or `"natDegree_leadingCoeff_pos"`, the kinds of the `rr_row_*` tactics). -/
def cancelCore (kind : String) : TacticM Unit := withMainContext do
  let r ← rowRecSetup "rr_row_cancel"
  unless r.shape == .deriv₁ do
    throwError "rr_row_cancel: {r.P} is not a first-order derivative recurrence"
  let plan ← match ← cancelPlan r with
    | .ok plan => pure plan
    | .error e => throwError "rr_row_cancel: {e}"
  trace[rr.row] "rr_row_cancel: law {repr plan.law}, m = {plan.m}, growth {plan.grow}"
  let P := mkIdent r.P
  let law := plan.law
  let (_, t) ← alignRow r.P (r.shift + plan.extra) (do
    rowSideGoal (some P)
    `(tactic| rr_row_side))
  let Q ← r.seq plan.extra
  let hrec ← r.hrecTerm plan.extra
  let n := mkIdent `n
  let Dfun ← `(fun $n:ident => $(rowNumLit law.D₀) + $(rowNumLit law.d) *
    (($n + $(rowNumLit law.e)) / $(rowNumLit law.p)))
  let h := mkIdent `h_row
  evalTactic (← `(tactic|
    have $h:ident := RealRooted.derivRec_natDegree_eq_and_leadingCoeff_pos_of_cancel (P := $Q)
      (D := $Dfun) (m := $(rowNumLit plan.m)) (by norm_num) $hrec
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t))
  let gs ← getGoals
  let some mg := gs.head? | throwError "rr_row_cancel: no goals"
  setGoals [mg]
  evalTactic (← `(tactic| beta_reduce at $h:ident))
  try
    match kind with
    | "natDegree" =>
        evalTactic (← `(tactic| exact (And.left $h).trans (by lia)))
    | "ne_zero" =>
        evalTactic (← `(tactic|
          exact Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt (And.left (And.right $h)))))
    | "natDegree_leadingCoeff_pos" =>
        evalTactic (← `(tactic|
          exact ⟨(And.left $h).trans (by lia), And.left (And.right $h)⟩))
    | _ => evalTactic (← `(tactic| exact And.left (And.right $h)))
  catch e => throwError "main goal: {e.toMessageData}"
  let [hA, hB, hA0, hmult, h0, hpos0, hnn0, hstep] := gs.tail
    | throwError "rr_row_cancel: unexpected side goals"
  cancelRun "hA" hA (rowSideGoal none)
  cancelRun "hB" hB (rowSideGoal none)
  cancelRun "hA0" hA0 (rowSideGoal none)
  cancelRun "hmult" hmult (cancelMult law.p plan.m)
  cancelRun "h0" h0 (cancelBase P)
  cancelRun "hpos0" hpos0 (cancelBase P)
  cancelRun "hnn0" hnn0 (cancelBase P)
  cancelRun "hstep" hstep (cancelStep law.p plan.grow)

elab_rules : tactic
  | `(tactic| rr_row_cancel) => withMainContext do
  betaReduceGoal
  let some kind := cancelGoalKind? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row_cancel: the goal is not a statement about natDegree, ≠ 0 or leadingCoeff"
  cancelCore kind

end RealRooted.Tactic
