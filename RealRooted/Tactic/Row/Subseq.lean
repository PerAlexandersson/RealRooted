import RealRooted.Tactic.Row.SideGoals

/-!
# Row tactics: residue subsequences

`rr_row_subseq_splits` proves `(P t).Splits` for a recurrence whose lags share a period
`p ∈ [2, 6]`, one residue class at a time; also the closers for explicit rows and factors
used by `rr_row_splits`.
-/

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Close the splitting of an explicit row: the side-goal engine, or the Euclidean certificate
of `rr_splits_explicit` after unfolding `P`. -/
def explicitRowSplits (P : Ident) : TacticM Unit := do
  unless ← rowSucceeds (rowSideFull (some P)) do
    evalTactic (← `(tactic| (beta_reduce; simp only [Nat.zero_add, $P:ident]; rr_splits_explicit)))

/-- `smallRow` for splitting goals of explicit rows. -/
def smallRowSplits (P : Ident) : TacticM (TSyntax `tactic) := do
  explicitRowSplits P
  `(tactic| rr_row_side)

/-- Close `∀ k, (q k).Splits` for explicit factors of degree at most two. -/
def factorSplitsTac : TacticM (TSyntax `tactic) :=
  `(tactic| (
    intro k
    beta_reduce
    first
      | (refine Polynomial.Splits.of_natDegree_le_one ?_; compute_degree!; done)
      | (refine RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg ?_ ?_
         · compute_degree!
         · simp [discrim, Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow,
             Polynomial.coeff_C] <;> norm_num)))

/-! ### Residue subsequences -/

/-- The shapes of the recurrence of a residue class. -/
private inductive SubShape where
  | product
  | deriv
  | derivProduct
  | lag
  deriving BEq

/-- The reduced recurrence of a residue class read off `linRec?`. -/
private structure Reduced where
  P : Ident
  eqn : Name
  p : Nat
  k : Nat
  jmin : Nat
  K : Nat
  shape : SubShape
  /-- the summands `(j, i, fun n => c n)` of the original recurrence -/
  terms : Array (Nat × Nat × Expr)

private def natLit (n : Nat) : Term := ⟨(rowNumLit n).raw⟩

/-- The coefficient `fun m => c (p * m + e)`. -/
private def subCoeff (c : Expr) (p e : Nat) : TacticM Term := do
  let lam ← withLocalDeclD `m (mkConst ``Nat) fun m => do
    mkLambdaFVars #[m] (c.beta #[mkNatAdd (mkNatMul (mkNatLit p) m) (mkNatLit e)])
  Term.exprToSyntax lam

/-- Read the reduced recurrence; fails if the lags are not divisible by `p ∈ [2, 6]` or if the
reduced recurrence has none of the three shapes. -/
private def readReduced (L : LinRecData) : TacticM Reduced := do
  let k := L.offset
  let lags := L.terms.map fun (j, _, _) => k - j
  let some g := lags[0]? | throwError "rr_row_subseq_splits: no summands"
  let p := lags.foldl Nat.gcd g
  let jmin := L.terms.foldl (fun a (j, _, _) => min a j) k
  let K := (k - jmin) / p
  -- `P (n + k) = A n * (P (n + k - p)).derivative` needs no reduction
  let derivProduct := K == 1 && L.terms.all fun (_, i, _) => i == 1
  unless (2 ≤ p || derivProduct) && p ≤ 6 do
    throwError "rr_row_subseq_splits: the lags of {L.P} have gcd {p}, not in [2, 6]"
  let shape ← match K with
    | 1 =>
        if L.terms.all fun (_, i, _) => i == 0 then pure SubShape.product
        else if derivProduct then pure SubShape.derivProduct
        else if L.terms.all fun (_, i, _) => i ≤ 1 then pure SubShape.deriv
        else throwError "rr_row_subseq_splits: derivatives of order > 1 in the reduced recurrence"
    | 2 =>
        if L.terms.all fun (_, i, _) => i == 0 then pure SubShape.lag
        else throwError "rr_row_subseq_splits: derivatives in a reduced three-term recurrence"
    | _ => throwError "rr_row_subseq_splits: reduced recurrence of length {K}"
  return { P := mkIdent L.P, eqn := L.eqn, p, k, jmin, K, shape, terms := L.terms }

/-- The coefficient of the reduced summand `(j', i)` for the class with `e = c - jmin`, or `0`. -/
private def Reduced.coeffAt (R : Reduced) (j' i e : Nat) : TacticM Term := do
  let mut found : Option Expr := none
  for (j, i', c) in R.terms do
    if (j - R.jmin) / R.p == j' && i' == i then
      if found.isSome then
        throwError "rr_row_subseq_splits: repeated summand in the reduced recurrence"
      found := some c
  match found with
  | some c => subCoeff c R.p e
  | none => `(fun _ : ℕ => (0 : ℝ[X]))

/-- The row `P (p * (m + j') + c)`. -/
private def Reduced.row (R : Reduced) (m : Ident) (j' c : Nat) : TacticM Term :=
  if j' == 0 then `($(R.P) ($(natLit R.p) * $m + $(natLit c)))
  else `($(R.P) ($(natLit R.p) * ($m + $(natLit j')) + $(natLit c)))

/-- The statement of the reduced recurrence in the shape of the theorems. -/
private def Reduced.stmt (R : Reduced) (c : Nat) : TacticM Term := do
  let m := mkIdent `m
  let e := c - R.jmin
  let lhs ← R.row m R.K c
  match R.shape with
  | .product =>
      let q ← R.coeffAt 0 0 e
      `(∀ $m:ident, $lhs = ($q $m) * $(← R.row m 0 c))
  | .derivProduct =>
      let A ← R.coeffAt 0 1 e
      `(∀ $m:ident, $lhs = ($A $m) * Polynomial.derivative $(← R.row m 0 c))
  | .deriv =>
      let A ← R.coeffAt 0 1 e
      let B ← R.coeffAt 0 0 e
      `(∀ $m:ident, $lhs = ($A $m) * (Polynomial.derivative $(← R.row m 0 c)) +
        ($B $m) * $(← R.row m 0 c))
  | .lag =>
      let a ← R.coeffAt 1 0 e
      let b ← R.coeffAt 0 0 e
      `(∀ $m:ident, $lhs = ($a $m) * $(← R.row m 1 c) + ($b $m) * $(← R.row m 0 c))

/-- Prove the reduced recurrence from the equation lemma of the definition. -/
private def Reduced.proveRec (R : Reduced) (c : Nat) : TacticM Unit := do
  let m := mkIdent `m
  let e := c - R.jmin
  let p := natLit R.p
  let base ← `($p * $m + $(natLit e))
  evalTactic (← `(tactic| intro $m:ident))
  evalTactic (← `(tactic| have h0 := $(mkIdent R.eqn):ident ($base)))
  let mut eqs : Array (TSyntax `tactic) := #[]
  let mut seen : Array Nat := #[]
  for j in R.k :: (R.terms.map (·.1)).toList do
    if seen.contains j then continue
    seen := seen.push j
    let j' := (j - R.jmin) / R.p
    let src ← if j == 0 then pure base else `($base + $(natLit j))
    let dst ← if j' == 0 then `($p * $m + $(natLit c))
      else `($p * ($m + $(natLit j')) + $(natLit c))
    unless j == 0 && j' == 0 && e == c do
      eqs := eqs.push (← `(tactic| rw [show ($src : ℕ) = $dst by ring] at h0))
  let optional (t : TSyntax `tactic) : TacticM Unit := discard <| rowAttempt (evalTactic t)
  let viaRw := do
    optional (← `(tactic| simp only [Nat.succ_eq_add_one] at h0))
    for t in eqs do evalTactic t
    evalTactic (← `(tactic| beta_reduce))
    evalTactic (← `(tactic| linear_combination h0))
  let viaRing := do
    optional (← `(tactic| simp only [Nat.succ_eq_add_one] at h0))
    evalTactic (← `(tactic| beta_reduce))
    optional (← `(tactic| ring_nf at h0))
    optional (← `(tactic| ring_nf))
    evalTactic (← `(tactic| linear_combination h0))
  match ← rowAttempt viaRw with
  | .ok _ => pure ()
  | .error e₁ =>
    match ← rowAttempt viaRing with
    | .ok _ => pure ()
    | .error e₂ => throwError "rr_row_subseq_splits: cannot derive the reduced recurrence:\n\
        {e₁}\n{e₂}"

/-- `have h : T := ?_`: the goal of the proof of `T` and the main goal (which has `h`). -/
private def subHave (h : Ident) (T : Term) : TacticM (MVarId × MVarId) := do
  evalTactic (← `(tactic| have $h:ident : $T := ?_))
  let mut proof? : Option MVarId := none
  let mut main? : Option MVarId := none
  for g in ← getGoals do
    if ((← g.getDecl).lctx.findFromUserName? h.getId).isSome then main? := some g
    else proof? := some g
  let (some pg, some mg) := (proof?, main?) | throwError "rr_row_subseq_splits: unexpected goals"
  return (pg, mg)

/-- Normalize numeral indices such as `2 * 0 + 1` in the main goal. -/
private def subNormIdx : TacticM Unit := do
  discard <| rowAttempt do
    evalTactic (← `(tactic| simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, Nat.mul_one, Nat.one_mul]))

/-- Close a side goal of the row theorems for a residue class. -/
private def subSide (P : Ident) : TacticM Unit := do
  betaReduceGoal
  withMainContext do
    subNormIdx
    withMainContext do rowSideFull (some P)

/-- `apply`-style attempt: run `main` and close every remaining goal by `subSide`. -/
private def subAttempt (P : Ident) (main : TSyntax `tactic) : TacticM Unit := do
  evalTactic main
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    subSide P
  setGoals []

/-- Run the alternatives in turn, collecting the failures. -/
private def subFirst (what : String) (alts : List (MessageData × TacticM Unit)) :
    TacticM Unit := do
  let mut failures : Array (MessageData × MessageData) := #[]
  for (name, tac) in alts do
    match ← rowAttempt (do
        tac
        unless (← getGoals).isEmpty do throwError "goals remain") with
    | .ok _ => return
    | .error e => failures := failures.push (name, e)
  throwRowFailures m!"rr_row_subseq_splits: no strategy proves {what}" failures

/-- The summand coefficient terms `(a, b)` / `(A, B)` and the named arguments of the shape. -/
private def Reduced.coeffArgs (R : Reduced) (c : Nat) :
    TacticM (Array (TSyntax `Lean.Parser.Term.namedArgument)) := do
  let e := c - R.jmin
  match R.shape with
  | .product => return #[← `(Lean.Parser.Term.namedArgument| (q := $(← R.coeffAt 0 0 e)))]
  | .derivProduct => return #[← `(Lean.Parser.Term.namedArgument| (A := $(← R.coeffAt 0 1 e)))]
  | .deriv => return #[← `(Lean.Parser.Term.namedArgument| (A := $(← R.coeffAt 0 1 e))),
      ← `(Lean.Parser.Term.namedArgument| (B := $(← R.coeffAt 0 0 e)))]
  | .lag => return #[← `(Lean.Parser.Term.namedArgument| (a := $(← R.coeffAt 1 0 e))),
      ← `(Lean.Parser.Term.namedArgument| (b := $(← R.coeffAt 0 0 e)))]

/-- Parse a term. -/
private def subParse (r : String) : TacticM Term := do
  let some t := (Parser.runParserCategory (← getEnv) `term r).toOption
    | throwError "rr_row_subseq_splits: bad term {r}"
  return ⟨t⟩

/-- Prove `∀ m, (P (p * m + c)).Splits` for a class of nonzero rows of degree `D₀ + m`
(`K ≥ 1`, derivative or three-term shape) from the interlacing of consecutive rows. -/
private def proveInterlaceClass (R : Reduced) (c D₀ : Nat) : TacticM Unit := do
  let P := R.P
  let p := natLit R.p
  let m := mkIdent `m
  let cL := natLit c
  let Dq := natLit D₀
  let Q ← `(fun $m:ident => $P ($p * $m + $cL))
  let hrecI := mkIdent `hrecI
  let hdegI := mkIdent `hdegI
  let hposI := mkIdent `hposI
  let hdp := mkIdent `hdp
  let (hg, main) ← subHave hrecI (← R.stmt c)
  setGoals [hg]
  R.proveRec c
  setGoals [main]
  withMainContext do
  let args ← R.coeffArgs c
  let d1 := natLit 1
  -- the degrees and the positivity of the leading coefficients
  let degThms : List (Name × Option String) :=
    if R.shape == .deriv then [(``RealRooted.derivRec_natDegree_eq_and_leadingCoeff_pos, none)]
    else (``RealRooted.threeTermPos_natDegree_eq_and_leadingCoeff_pos, none) ::
      ["1", "2", "4", "1 / 2", "3"].map fun r =>
        (``RealRooted.threeTermRatio_natDegree_eq_and_leadingCoeff_pos, some r)
  let degAlts : List (MessageData × TacticM Unit) ← degThms.mapM fun (thm, ρ) => do
    let t := mkIdent thm
    let main ← match ρ with
      | none => `(tactic| apply $t:ident (P := $Q) (d := $d1) (D₀ := $Dq) $args:namedArgument*
          (hrec := $hrecI))
      | some ρ => do
          let ρ ← subParse ρ
          `(tactic| apply $t:ident (P := $Q) (d := $d1) (D₀ := $Dq) $args:namedArgument*
            (ρ := ($ρ : ℝ)) (hrec := $hrecI))
    return (m!"{thm}{ρ.elim "" (" with ρ = " ++ ·)}", subAttempt P main)
  let (hg2, main2) ← subHave hdp (← `(∀ $m:ident,
    ($P ($p * $m + $cL)).natDegree = $Dq + 1 * $m ∧ 0 < ($P ($p * $m + $cL)).leadingCoeff))
  setGoals [hg2]
  subFirst "the degrees of the residue class" degAlts
  setGoals [main2]
  withMainContext do
  evalTactic (← `(tactic| have $hdegI:ident :
    ∀ $m:ident, ($P ($p * $m + $cL)).natDegree = $Dq + $m :=
      fun $m:ident => (($hdp $m).1).trans (by lia)))
  evalTactic (← `(tactic| have $hposI:ident :
    ∀ $m:ident, 0 < ($P ($p * $m + $cL)).leadingCoeff := fun $m:ident => ($hdp $m).2))
  -- interlacing of consecutive rows
  let named (thm : Name) (extra : Array (TSyntax `Lean.Parser.Term.namedArgument)) :
      TacticM (TSyntax `tactic) := do
    `(tactic| apply $(mkIdent thm):ident (P := $Q) (D₀ := $Dq) $args:namedArgument*
      $extra:namedArgument* (hrec := $hrecI) (hdeg := $hdegI) (hpos := $hposI))
  let plain : List Name :=
    if R.shape == .deriv then
      if D₀ == 0 then [``RealRooted.derivRec_interlaces_of_eval_nonpos]
      else [``RealRooted.derivRec_interlaces_of_splits_of_eval_nonpos]
    else [``RealRooted.threeTerm_interlaces_of_eval_nonpos]
  let mut alts : List (MessageData × TacticM Unit) := []
  for thm in plain do
    alts := alts ++ [(m!"{thm}", do subAttempt P (← named thm #[]))]
  let (icc, iic) := if R.shape == .deriv then
      (``RealRooted.derivRec_interlaces_of_roots_mem_Icc,
        ``RealRooted.derivRec_interlaces_of_roots_le)
    else
      (``RealRooted.threeTerm_interlaces_of_roots_mem_Icc,
        ``RealRooted.threeTerm_interlaces_of_roots_le)
  for (lo, hi) in [(some "-1", "0"), (some "-1 / 2", "0"), (some "-2", "0"),
      (some "-4", "0"), (none, "-1"), (none, "-1 / 2"), (none, "-2")] do
    let U ← subParse hi
    match lo with
    | some l =>
        let L ← subParse l
        alts := alts ++ [(m!"{icc} on [{l}, {hi}]", do
          subAttempt P (← named icc #[← `(Lean.Parser.Term.namedArgument| (L := ($L : ℝ))),
            ← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]))]
    | none =>
        alts := alts ++ [(m!"{iic} on (-∞, {hi}]", do
          subAttempt P (← named iic #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]))]
  if R.shape == .deriv then
    for u in ["-1", "0", "-1 / 2", "-2"] do
      let U ← subParse u
      alts := alts ++ [(m!"derivRec_interlaces_of_roots_le_of_degree on (-∞, {u}]", do
        subAttempt P (← named ``RealRooted.derivRec_interlaces_of_roots_le_of_degree
          #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ)))]))]
  else
    for u in ["0", "-1"] do
      for ρ in ["1", "2"] do
        let U ← subParse u
        let ρ ← subParse ρ
        alts := alts ++ [(m!"threeTerm_interlaces_of_roots_le_of_ratio on (-∞, {u}]", do
          subAttempt P (← named ``RealRooted.threeTerm_interlaces_of_roots_le_of_ratio
            #[← `(Lean.Parser.Term.namedArgument| (U := ($U : ℝ))),
              ← `(Lean.Parser.Term.namedArgument| (ρ := fun _ => ($ρ : ℝ)))]))]
  let hI := mkIdent `hI
  let (hg3, main3) ← subHave hI (← `(∀ $m:ident,
    RealRooted.Interlaces ($P ($p * $m + $cL)) ($P ($p * ($m + 1) + $cL))))
  setGoals [hg3]
  subFirst "the interlacing of consecutive rows of the residue class" alts
  setGoals [main3]
  withMainContext do
  evalTactic (← `(tactic| exact fun $m:ident => (($hI $m).2.1.2)))

/-- Prove `∀ m, (P (p * m + c)).Splits` for a product class (of `P` or of its derivative). -/
private def proveProductClass (R : Reduced) (c : Nat) : TacticM Unit := do
  let P := R.P
  let p := natLit R.p
  let m := mkIdent `m
  let cL := natLit c
  let Q ← `(fun $m:ident => $P ($p * $m + $cL))
  let hrecI := mkIdent `hrecI
  let (hg, main) ← subHave hrecI (← R.stmt c)
  setGoals [hg]
  R.proveRec c
  setGoals [main]
  withMainContext do
  let args ← R.coeffArgs c
  -- the base row `P c` is explicit
  let h0 := mkIdent `h0row
  let (hg1, main1) ← subHave h0 (← `(($P $cL).Splits))
  setGoals [hg1]
  unless ← rowSucceeds (rowSideFull (some P)) do
    evalTactic (← `(tactic| (simp only [$P:ident]; rr_splits_explicit)))
  setGoals [main1]
  withMainContext do
  evalTactic (← `(tactic| intro $m:ident))
  let thm := mkIdent <| if R.shape == .derivProduct then ``RealRooted.derivProduct_splits
    else ``RealRooted.productSequence_splits
  evalTactic (← `(tactic|
    refine $thm:ident (P := $Q) $args:namedArgument* $hrecI ?_ $h0 $m))
  evalTactic (← factorSplitsTac)
  unless (← getGoals).isEmpty do throwError "rr_row_subseq_splits: goals remain"

/-- Prove `∀ m, (P (p * m + c)).Splits` for a class of zero rows. -/
private def proveZeroClass (R : Reduced) (c : Nat) : TacticM Unit := do
  let P := R.P
  let p := natLit R.p
  let m := mkIdent `m
  let cL := natLit c
  let Q ← `(fun $m:ident => $P ($p * $m + $cL))
  let hrecI := mkIdent `hrecI
  let (hg, main) ← subHave hrecI (← R.stmt c)
  setGoals [hg]
  R.proveRec c
  setGoals [main]
  withMainContext do
  let args ← R.coeffArgs c
  let base (j : Nat) : TacticM Unit := do
    evalTactic (← `(tactic| have : $P ($(natLit (c + j * R.p))) = 0 := by
      first | (simp only [$P:ident]; done) | (simp [$P:ident]; done)))
  let hz := mkIdent `hz
  let eqThm : Name := match R.shape with
    | .product => ``RealRooted.eq_zero_of_product_rec
    -- derivative products are classified as live
    | .deriv | .derivProduct => ``RealRooted.eq_zero_of_derivRec
    | .lag => ``RealRooted.eq_zero_of_threeTerm_rec
  base 0
  if R.shape == .lag then base 1
  evalTactic (← `(tactic| intro $m:ident))
  match R.shape with
  | .lag =>
      evalTactic (← `(tactic| have $hz:ident := $(mkIdent eqThm):ident (Q := $Q)
        $args:namedArgument* $hrecI (by assumption) (by assumption) $m))
  | _ =>
      evalTactic (← `(tactic| have $hz:ident := $(mkIdent eqThm):ident (Q := $Q)
        $args:namedArgument* $hrecI (by assumption) $m))
  evalTactic (← `(tactic| (beta_reduce at $hz:ident; rw [$hz:ident]; exact Polynomial.Splits.zero)))

/-- The class sequences' numeric kinds. -/
private inductive ClassKind where
  | zero
  | live (D₀ : Nat)
  deriving Inhabited

/-- Classify the residue class `c` from the computed rows. -/
private def classKind (rows : Array QPoly) (p c : Nat) : Except String ClassKind := Id.run do
  let mut seq : Array QPoly := #[]
  let mut i := c
  while i < rows.size do
    seq := seq.push rows[i]!
    i := i + p
  if seq.size < 4 then return .error "too few computed rows"
  if seq.all (·.isZero) then return .ok ClassKind.zero
  if seq.any (·.isZero) then return .error "some rows vanish"
  let D₀ := seq[0]!.natDegree
  for m in [0:seq.size] do
    unless seq[m]!.natDegree == D₀ + m do
      return .error s!"the degree of row {c + p * m} is {seq[m]!.natDegree}, not {D₀ + m}"
    unless seq[m]!.lead > 0 do
      return .error s!"the leading coefficient of row {c + p * m} is not positive"
  return .ok (ClassKind.live D₀)

/-- `rr_row_subseq_splits` closes `(P t).Splits` for a sequence whose recurrence has all lags
divisible by `p ∈ [2, 6]`; see the module documentation. -/
syntax (name := rrRowSubseqSplits) "rr_row_subseq_splits" : tactic

elab_rules : tactic
  | `(tactic| rr_row_subseq_splits) => withMainContext do
    discard introIfForall
    withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let some Pn ← findSeqConstDeep? tgt
      | throwError "rr_row_subseq_splits: no sequence `P : ℕ → ℝ[X]` found in the goal"
    let some L ← linRec? Pn
      | throwError "rr_row_subseq_splits: {Pn} has no linear recurrence"
    let R ← readReduced L
    let P := R.P
    let some rows ← linRecRows? L 26
      | throwError "rr_row_subseq_splits: could not compute the rows of {Pn}"
    -- numeric guard
    let mut kinds : Array ClassKind := #[]
    for r in [0:R.p] do
      let c := R.jmin + r
      if R.shape == .product || R.shape == .derivProduct then
        kinds := kinds.push (ClassKind.live 0)
      else
        match classKind rows R.p c with
        | .ok kd => kinds := kinds.push kd
        | .error e =>
            throwError "rr_row_subseq_splits: residue class {c} mod {R.p}: {e}"
    -- the residue classes
    let t ← mainRowIndex P
    let hres : Array Ident := (Array.range R.p).map fun r => mkIdent (.mkSimple s!"hres{r}")
    let m := mkIdent `m
    for r in [0:R.p] do
      let c := R.jmin + r
      let T ← `(∀ $m:ident, ($P ($(natLit R.p) * $m + $(natLit c))).Splits)
      let (hg, main) ← subHave hres[r]! T
      setGoals [hg]
      withMainContext do
        match kinds[r]! with
        | .zero => proveZeroClass R c
        | .live D₀ =>
            if R.shape == .product || R.shape == .derivProduct then proveProductClass R c
            else proveInterlaceClass R c D₀
      unless (← getGoals).isEmpty do throwError "rr_row_subseq_splits: goals remain"
      setGoals [main]
    -- the rows below `jmin`
    withMainContext do
    let some tFv := (if t.isFVar then some t else none)
      | throwError "rr_row_subseq_splits: the row index is not a variable"
    let tId := mkIdent (← tFv.fvarId!.getUserName)
    if R.jmin > 0 then
      evalTactic (← `(tactic| rcases Nat.lt_or_ge $tId $(natLit R.jmin) with hlt | hge))
      let [hlt, hge] ← getGoals | throwError "rr_row_subseq_splits: unexpected goals"
      setGoals [hlt]
      evalTactic (← `(tactic| interval_cases $tId))
      for g in ← getGoals do
        setGoals [g]
        unless ← rowSucceeds (rowSideFull (some P)) do
          evalTactic (← `(tactic| (simp only [$P:ident]; rr_splits_explicit)))
      setGoals [hge]
    withMainContext do
    let r := mkIdent `r
    let hr := mkIdent `hr
    let ht := mkIdent `ht
    evalTactic (← `(tactic| obtain ⟨$m:ident, $r:ident, $hr:ident, $ht:ident⟩ :=
      RealRooted.exists_mul_add_lt $(natLit R.p) ($tId - $(natLit R.jmin)) (by norm_num)))
    withMainContext do
    evalTactic (← `(tactic| (
      have hteq : $tId = $(natLit R.p) * $m + ($(natLit R.jmin) + $r) := by lia
      rw [hteq])))
    evalTactic (← `(tactic| interval_cases $r:ident))
    let gs ← getGoals
    unless gs.length == R.p do throwError "rr_row_subseq_splits: unexpected residue goals"
    for i in [0:R.p] do
      setGoals [gs[i]!]
      withMainContext do
        evalTactic (← `(tactic| exact $(hres[i]!):ident $m))
    setGoals []

end RealRooted.Tactic
