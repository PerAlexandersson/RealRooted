module

public import RealRooted.DerivativeRecurrence.EndpointWindow
public import RealRooted.Tactic.Row.PowerForm
public import RealRooted.Tactic.Row.SideGoals
public import RealRooted.Tactic.Row.FTransform
public meta import RealRooted.DerivativeRecurrence.EndpointWindow
public meta import RealRooted.Tactic.Row.PowerForm
public meta import RealRooted.Tactic.Row.SideGoals
public meta import RealRooted.Tactic.Row.FTransform

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Rational functions fitted for the two endpoints. -/
structure EndpointWindowFit where
  /-- The lower endpoint of the window, as numerator and denominator coefficients in `n`. -/
  lower : Array Rat × Array Rat
  /-- The upper endpoint of the window, as numerator and denominator coefficients in `n`. -/
  upper : Array Rat × Array Rat
  /-- All roots of the derivative coefficient, each as numerator and denominator coefficients in
  `n`. -/
  roots : Array (Array Rat × Array Rat)
  /-- The leading coefficient, as numerator and denominator coefficients in `n`. -/
  lead : Array Rat × Array Rat
  /-- The position of the lower endpoint among the sorted roots. -/
  lowerIndex : Nat
  /-- The degree of the derivative coefficient, which is the number of roots. -/
  degree : Nat

/-- Fit sampled values to `(a + b n) / (1 + d n)`, including constants. -/
private def fitAffineRat? (values : Array Rat) : Option (Array Rat × Array Rat) := do
  let v0 ← values[0]?
  let v1 ← values[1]?
  let v2 ← values[2]?
  if v2 == v1 then
    guard (values.all (· == v0))
    return (#[v0], #[1])
  let d := (2 * v1 - v0 - v2) / (2 * (v2 - v1))
  let a := v0
  let b := v1 * (1 + d) - v0
  guard (0 ≤ d)
  guard <| (List.range values.size).all fun n =>
    0 < 1 + d * n && values[n]! * (1 + d * n) == a + b * n
  return (#[a, b], #[1, d])

private def sortedRationalRoots (p : QPoly) : List Rat :=
  p.rationalRoots.mergeSort (· ≤ ·)

/-- Probe adjacent rational roots of the derivative coefficient.  Candidate
windows are retained only when exact computed rows lie strictly inside them,
the coefficient signs propagate outward, and both endpoint sequences have
positive-denominator rational fits. -/
def rationalEndpointWindowFit? (r : RowRec) : MetaM (Option EndpointWindowFit) := do
  unless r.shape == .deriv₁ && r.offset == 1 && r.shift == 0 do return none
  let (some Af, some Bf) := (r.coeffs[0]?, r.coeffs[1]?) | return none
  let (some a0, some _) := (← evalCoeffAt? Af 0, ← evalCoeffAt? Bf 0) | return none
  let roots0 := sortedRationalRoots a0
  if roots0.length < 2 || roots0.length != a0.natDegree then return none
  let some recData ← linRec? r.P | return none
  let samples := 3
  let some rows ← linRecRows? recData samples | return none
  for i in [0:roots0.length - 1] do
    if roots0[i]! == roots0[i + 1]! then continue
    let mut lowers : Array Rat := #[]
    let mut uppers : Array Rat := #[]
    let mut rootSamples := Array.replicate roots0.length (#[] : Array Rat)
    let mut valid := true
    for n in [0:samples] do
      let (some a, some b) := (← evalCoeffAt? Af n, ← evalCoeffAt? Bf n)
        | valid := false; continue
      let roots := sortedRationalRoots a
      if roots.length != roots0.length then valid := false; continue
      let (some lower, some upper) := (roots[i]?, roots[i + 1]?)
        | valid := false; continue
      let some p := rows[n]? | valid := false; continue
      let mid := (lower + upper) / 2
      unless lower < upper && a.eval lower == 0 && a.eval upper == 0 &&
          a.eval mid ≤ 0 && b.eval lower < 0 && 0 < b.eval upper &&
          (p.isZero || (p.realRooted && p.rootsGe lower && p.rootsLe upper &&
            p.eval lower != 0 && p.eval upper != 0)) do
        valid := false
      lowers := lowers.push lower
      uppers := uppers.push upper
      for k in [0:roots.length] do
        rootSamples := rootSamples.set! k (rootSamples[k]!.push roots[k]!)
    unless valid && lowers.size == samples && uppers.size == samples do continue
    unless (List.range (samples - 1)).all (fun n => lowers[n + 1]! ≤ lowers[n]!) &&
        (List.range (samples - 1)).all (fun n => uppers[n]! ≤ uppers[n + 1]!) do continue
    let (some lowerFit, some upperFit) :=
      (fitAffineRat? lowers, fitAffineRat? uppers) | continue
    let mut rootFits := #[]
    for samples in rootSamples do
      let some fit := fitAffineRat? samples | valid := false; continue
      rootFits := rootFits.push fit
    unless valid && rootFits.size == roots0.length do continue
    let mut leads : Array Rat := #[]
    for n in [0:9] do
      let some a ← evalCoeffAt? Af n | valid := false; continue
      leads := leads.push a.lead
    let some (leadNums, leadDen) := fitCommonPositiveDenominator? #[leads]
      | continue
    return some {
      lower := lowerFit, upper := upperFit, roots := rootFits,
      lead := (leadNums[0]!, leadDen),
      lowerIndex := i, degree := a0.natDegree
    }
  return none

private def endpointNPolyTerm (cs : Array Rat) (n : Ident) : TacticM Term := do
  let cs := (QPoly.norm cs).coeffs
  if cs.isEmpty then return ← ratTerm 0
  let mut acc ← ratTerm cs.back!
  for i in (List.range (cs.size - 1)).reverse do
    acc ← `($(← ratTerm cs[i]!) + ($n : ℝ) * $acc)
  return acc

private def endpointRatFunTerm (fit : Array Rat × Array Rat) (n : Ident) :
    TacticM Term := do
  let num ← endpointNPolyTerm fit.1 n
  let den ← endpointNPolyTerm fit.2 n
  `($num / $den)

/-- Apply the endpoint-window theorem using a window discovered by
`rationalEndpointWindowFit?`; every sampled guess is re-certified symbolically. -/
def rationalEndpointWindowGoal : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let r ← match ← rowRec? P with
    | .ok r => pure r
    | .error e => throwError e
  let some fit ← rationalEndpointWindowFit? r
    | throwError "rr_row: no rational endpoint window"
  let some Af := r.coeffs[0]?
    | throwError "rr_row: no derivative coefficient"
  let some Bf := r.coeffs[1]?
    | throwError "rr_row: no row coefficient"
  let rawA ← certTerm Af
  let rawB ← certTerm Bf
  let some A ← normalizedCoeffTerm? Af 0
    | throwError "rr_row: the derivative coefficient is not rational in the row index"
  let some B ← normalizedCoeffTerm? Bf 0
    | throwError "rr_row: the row coefficient is not rational in the row index"
  let some D₀ ← findRowDegree (mkIdent P) r.shift
    | throwError "rr_row: could not compute the endpoint-window base degree"
  let Dq := rowNumLit D₀
  let Pi := mkIdent P
  let t ← Term.exprToSyntax (← mainRowIndex Pi)
  let degreeName ← freshAuxName "endpointWindowDegree"
  let degreeLemma := mkIdent degreeName
  elabAuxCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ degreeName)) (m : ℕ) :
        ($Pi m).natDegree = $Dq + m := by
      rr_row_natDegree))
  let posName ← freshAuxName "endpointWindowLeadingCoeffPos"
  let posLemma := mkIdent posName
  elabAuxCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ posName)) (m : ℕ) :
        0 < ($Pi m).leadingCoeff := by
      rr_row_leadingCoeff_pos))
  let n := mkIdent `n
  let L ← `(fun $n:ident : ℕ => $(← endpointRatFunTerm fit.lower n))
  let U ← `(fun $n:ident : ℕ => $(← endpointRatFunTerm fit.upper n))
  let x := mkIdent `x
  let hL := mkIdent `hL
  let hU := mkIdent `hU
  let mut factorTactics : Array (TSyntax `tactic) := #[]
  let mut product? : Option Term := none
  let mut productProof? : Option Term := none
  for k in [0:fit.roots.size] do
    let root ← endpointRatFunTerm fit.roots[k]! n
    let factor ← if k ≤ fit.lowerIndex then `($x - $root) else `($root - $x)
    let hfactor := mkIdent (Name.mkSimple s!"hfactor{k}")
    let proof ← if k == fit.lowerIndex then
        `(tactic| exact sub_nonneg.mpr (le_of_lt $hL))
      else if k == fit.lowerIndex + 1 then
        `(tactic| exact sub_nonneg.mpr (le_of_lt $hU))
      else `(tactic| (
        beta_reduce at $hL $hU ⊢
        push_cast at $hL $hU ⊢
        rr_row_field))
    factorTactics := factorTactics.push (← `(tactic|
      have $hfactor : 0 ≤ $factor := by
        $proof:tactic))
    product? ← match product? with
      | none => pure (some factor)
      | some product => some <$> `($product * $factor)
    productProof? ← match productProof? with
      | none => pure (some hfactor)
      | some proof => some <$> `(mul_nonneg $proof $hfactor)
  let some product := product?
    | throwError "rr_row: the endpoint coefficient has no rational roots"
  let some productProof := productProof?
    | throwError "rr_row: no endpoint product proof"
  let aTerm := A
  let lead ← endpointRatFunTerm fit.lead n
  let effectiveLead ← if (fit.degree - fit.lowerIndex - 1) % 2 == 0 then
      pure lead
    else `(-$lead)
  let hATactic ← `(tactic| (
    intro $n:ident $x:ident $hL:ident $hU:ident
    $factorTactics*
    have hproduct : 0 ≤ $product := $productProof
    have heffective : $effectiveLead ≤ 0 := by
      beta_reduce
      rr_row_field
    have hfactorization : ($aTerm $n).eval $x = $effectiveLead * $product := by
      beta_reduce
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
        Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_zero]
      field_simp <;> ring
    rw [hfactorization]
    exact mul_nonpos_of_nonpos_of_nonneg heffective hproduct))
  let hrecRaw ← r.hrecTerm 0
  let hrecName := mkIdent `h_endpointWindowRec
  evalTactic (← `(tactic|
    have $hrecName:ident : ∀ q : ℕ,
        $Pi (q + 1) = ($A : ℕ → ℝ[X]) q * ($Pi q).derivative +
          ($B : ℕ → ℝ[X]) q * $Pi q := by
      intro q
      have hraw : $Pi (q + 1) =
          ($rawA : ℕ → ℝ[X]) q * ($Pi q).derivative +
            ($rawB : ℕ → ℝ[X]) q * $Pi q := $hrecRaw q
      rw [hraw]
      rr_cf_identity))
  evalTactic (← `(tactic| (
    refine RealRooted.derivativeRecurrence_interlaces_of_endpoint_evaluations
      (P := $Pi) (D₀ := $Dq) $L $U $hrecName
      (fun m => $degreeLemma m) (fun m => $posLemma m)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $t)))
  let [hLmono, hUmono, hA, hAL, hAU, hBL, hBU, h0, hW0, h01] ← getGoals
    | throwError "rr_row: unexpected endpoint-window side goals"
  for goal in [hLmono, hUmono] do
    let (_, goal) ← goal.intro1P
    setGoals [goal]
    evalTactic (← `(tactic| beta_reduce))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| push_cast))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| rw [div_le_div_iff₀ (by positivity) (by positivity)]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| ring_nf))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| nlinarith))
  setGoals [hA]
  evalTactic hATactic
  let endpointEval ← `(tactic| (
    intro n
    beta_reduce
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_zero]
    rr_row_field))
  for goal in [hAL, hAU, hBL, hBU] do
    setGoals [goal]
    evalTactic endpointEval
  setGoals [h0]
  evalTactic (← `(tactic|
    exact Polynomial.Splits.of_natDegree_eq_zero (by
      simpa using $degreeLemma 0)))
  setGoals [hW0]
  evalTactic (← `(tactic|
    exact roots_window_of_natDegree_zero (by simpa using $degreeLemma 0)))
  setGoals [h01]
  let (_, h01) ← h01.intro1P
  setGoals [h01]
  if D₀ == 0 then
    evalTactic (← `(tactic|
      exact interlaces_of_natDegree_eq_zero_of_natDegree_eq_one
        (Polynomial.leadingCoeff_ne_zero.mp (by exact ($posLemma 0).ne'))
        (by simpa using $degreeLemma 0)
        (by simpa using $degreeLemma 1)))
  else
    evalTactic (← `(tactic| norm_num at *))

end RealRooted.Tactic
