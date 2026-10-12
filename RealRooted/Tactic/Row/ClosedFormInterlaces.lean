import RealRooted.Tactic.RowClosedForm
import RealRooted.Interlacing.RemainderCertificate
import RealRooted.Tactic.InterlacesExplicit
import RealRooted.Tactic.Row.SideGoals

/-!
# Row tactics: interlacing of closed-form rows `q ^ (D₀ + m) · R m`

When the closed-form probe of `rr_row_closed_form_splits` (`cfExplicit?`) finds rows
`P (m + s) = R m * q ^ (D₀ + m)` with one linear factor `q` and an explicit residual `R m` of
degree one or two whose coefficients are polynomials in `m`, consecutive rows interlace as soon
as the division `q * R (m + 1) = R m * (p X + d) + (α X + β)` has a remainder certificate:
`p > 0`, `α < 0` and `a β² - b α β + c α² < 0` for `R m = a X² + b X + c`
(`RealRooted.Interlaces.pow_mul_of_quadratic_remainder`), or `β < 0` in the linear case
(`RealRooted.Interlaces.pow_mul_of_linear_remainder`).

`cfiProbe` computes `p`, `d`, `α`, `β` and the certificate exactly as rational functions of `m`
and finds the first `m₀ ≤ 80` from which all signs are certified: after the shift `m = m₀ + k`
every numerator and denominator has coefficients of one sign.  `cfiProof` reuses the closed form
of `cfProve`, proves the division identity by `rr_cf_field`, the signs by `positivity`, and the
finitely many earlier pairs by `rr_interlaces_explicit`.  This covers the order-three recurrences
with characteristic polynomial `(λ - q)³`, such as A106246, A124932, A125092, A141611 and A332496.
-/


open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic.CFI

structure RatFun where
  num : QPoly
  den : QPoly

structure CFIPlan where
  plan : CFPlan
  degree : Nat
  m0 : Nat
  p : RatFun
  d : RatFun
  α : RatFun
  β : RatFun
  cert : RatFun

def rfNorm (r : RatFun) : RatFun :=
  let g := QPoly.gcd r.num r.den
  let n := r.num.divExact? g |>.getD r.num
  let d := r.den.divExact? g |>.getD r.den
  if d.lead < 0 then ⟨-n, -d⟩ else ⟨n, d⟩

def rfAdd (x y : RatFun) : RatFun :=
  rfNorm ⟨x.num * y.den + y.num * x.den, x.den * y.den⟩

def rfNeg (x : RatFun) : RatFun := rfNorm ⟨-x.num, x.den⟩

def rfSub (x y : RatFun) : RatFun := rfAdd x (rfNeg y)

def rfMul (x y : RatFun) : RatFun :=
  rfNorm ⟨x.num * y.num, x.den * y.den⟩

def rfDiv (x y : RatFun) : RatFun :=
  rfNorm ⟨x.num * y.den, x.den * y.num⟩

def rfConst (r : Rat) : RatFun := ⟨QPoly.const r, QPoly.const 1⟩

def qShift (p : QPoly) (n : Nat) : QPoly := Id.run do
  let z := QPoly.X + QPoly.const n
  let mut out := QPoly.const 0
  let mut pow := QPoly.const 1
  for i in [0:p.coeffs.size] do
    out := out + QPoly.smul (p.coeff i) pow
    pow := pow * z
  return out

def positiveAtZero (p : QPoly) : Bool :=
  !p.isZero && 0 < p.coeff 0 && p.coeffs.all (0 ≤ ·)

def nonnegative (p : QPoly) : Bool := p.coeffs.all (0 ≤ ·)

def positiveShift (p : QPoly) (m : Nat) : Bool := positiveAtZero (qShift p m)

def negativeShift (p : QPoly) (m : Nat) : Bool :=
  positiveShift (-p) m

def goodPos (r : RatFun) (m : Nat) : Bool :=
  positiveShift r.num m && positiveShift r.den m

def goodNeg (r : RatFun) (m : Nat) : Bool :=
  negativeShift r.num m && positiveShift r.den m

def remainderData (plan : CFPlan) : Option (Nat × RatFun × RatFun × RatFun × RatFun × RatFun) := do
  guard (plan.facs.size == 1)
  let q := plan.facs[0]!
  guard (q.natDegree == 1)
  guard (plan.laws.size == 1)
  let law := plan.laws[0]!
  guard (law.d == 1 && law.p == 1 && law.ph == 0)
  let a2 := plan.resid[2]!
  let c := plan.resid[0]!
  let degree := if a2.isZero then 1 else 2
  let a := plan.resid[degree]!
  let b := if degree == 1 then plan.resid[0]! else plan.resid[1]!
  guard (degree == 1 || !a2.isZero)
  guard (degree == 1 → !b.isZero)
  let a1 := qShift a 1
  let b1 := qShift b 1
  let c1 := qShift c 1
  let q0 := q.coeff 0
  let p := rfDiv ⟨a1, QPoly.const 1⟩ ⟨a, QPoly.const 1⟩
  let d := rfDiv
    (rfSub (rfAdd ⟨b1, QPoly.const 1⟩
        (rfMul (rfConst q0) ⟨a1, QPoly.const 1⟩))
      (rfMul p ⟨b, QPoly.const 1⟩)) ⟨a, QPoly.const 1⟩
  let α := rfSub (rfAdd ⟨c1, QPoly.const 1⟩ (rfMul (rfConst q0)
      ⟨b1, QPoly.const 1⟩))
    (rfAdd (rfMul d ⟨b, QPoly.const 1⟩) (rfMul p ⟨c, QPoly.const 1⟩))
  let β := rfSub (rfMul (rfConst q0) ⟨c1, QPoly.const 1⟩)
    (rfMul d ⟨c, QPoly.const 1⟩)
  let cert := rfSub (rfMul ⟨a, QPoly.const 1⟩ (rfMul β β))
    (rfAdd (rfMul ⟨b, QPoly.const 1⟩ (rfMul α β))
      (rfNeg (rfMul ⟨c, QPoly.const 1⟩ (rfMul α α))))
  some (degree, p, d, α, β, cert)

def certificateAt? (plan : CFPlan) : Option
    (Nat × RatFun × RatFun × RatFun × RatFun × RatFun × Nat) := do
  let (degree, p, d, α, β, cert) ← remainderData plan
  let a := plan.resid[degree]!
  for m in [0:81] do
    if positiveShift a m && goodPos p m &&
        (degree == 1 && goodNeg β m || degree == 2 && goodNeg α m && goodNeg cert m) then
      return (degree, p, d, α, β, cert, m)
  none

def qpolyText (p : QPoly) : String :=
  if p.isZero then "0"
  else String.intercalate " + " ((List.range p.coeffs.size).filterMap fun i =>
    let c := p.coeff i
    if c == 0 then none else some s!"({c})*m^{i}")

def ratFunText (r : RatFun) : String := s!"({qpolyText r.num}) / ({qpolyText r.den})"

def cfiProbe (L : LinRecData) : MetaM (Except String CFIPlan) := do
  let some rows ← linRecRows? L 18 | return .error "the rows cannot be computed"
  let mut diagnostics : Array String := #[]
  for s in [0:3] do
    let some plan ← cfExplicit? L rows s (18 - s) | continue
    match certificateAt? plan with
    | some (degree, p, d, α, β, cert, m0) =>
      return .ok { plan, degree, m0, p, d, α, β, cert }
    | none =>
      match remainderData plan with
      | some (degree, _, _, α, β, cert) =>
        let msg := s!"drop {s}, degree {degree}: α={ratFunText α}, " ++
          s!"β={ratFunText β}, cert={ratFunText cert}"
        diagnostics := diagnostics.push msg
      | none =>
        diagnostics := diagnostics.push s!"drop {s}: plan is not one linear factor"
  if diagnostics.isEmpty then
    return .error "no explicit one-factor quadratic or linear plan"
  return .error (String.intercalate "; " diagnostics.toList)

def qpolyAtTerm (p : QPoly) (x : Term) : TacticM Term := do
  let xr ← `(($x : ℝ))
  ratPolyAtTerm p.coeffs xr

def ratFunAtTerm (r : RatFun) (x : Term) : TacticM Term := do
  `($(← qpolyAtTerm r.num x) / $(← qpolyAtTerm r.den x))

def residualAtTerm (plan : CFPlan) (x : Term) : TacticM Term := do
  let cT : Term := mkIdent ``Polynomial.C
  let xT : Term := mkIdent ``Polynomial.X
  let c0 ← qpolyAtTerm plan.resid[0]! x
  let c1 ← qpolyAtTerm plan.resid[1]! x
  let c2 ← qpolyAtTerm plan.resid[2]! x
  `($cT ($c0) + $cT ($c1) * $xT + $cT ($c2) * $xT ^ 2)

def residualLinearAtTerm (plan : CFPlan) (x : Term) : TacticM Term := do
  let cT : Term := mkIdent ``Polynomial.C
  let xT : Term := mkIdent ``Polynomial.X
  let c0 ← qpolyAtTerm plan.resid[0]! x
  let c1 ← qpolyAtTerm plan.resid[1]! x
  `($cT ($c1) * $xT + $cT ($c0))

def polyWithShiftProof (name : Ident) (p : QPoly) (m0 : Nat) (m k : Term)
    (negative : Bool) : TacticM (TSyntax `tactic) := do
  let lhs ← qpolyAtTerm p m
  let pp := if negative then qShift (-p) m0 else qShift p m0
  let rhs ← qpolyAtTerm pp k
  let eqn ← if negative then
    `(tactic| have $name : $lhs = -$rhs := by
      simp only [rr_hshift] <;> ring)
  else
    `(tactic| have $name : $lhs = $rhs := by
      simp only [rr_hshift] <;> ring)
  return eqn

def proveSign (name : Ident) (r : RatFun) (m0 : Nat) (m k : Term)
    (negative : Bool) : TacticM (Array (TSyntax `tactic)) := do
  let hnum := mkIdent (Name.mkSimple s!"{name.getId}_num")
  let hden := mkIdent (Name.mkSimple s!"{name.getId}_den")
  let hnumEq ← polyWithShiftProof hnum r.num m0 m k negative
  let hdenEq ← polyWithShiftProof hden r.den m0 m k false
  let orig ← ratFunAtTerm r m
  let hnumSign ← if negative then `($orig < 0) else `(0 < $orig)
  let negNum : TSyntax `tactic ← if m0 > 0 then
    `(tactic| ring_nf <;> nlinarith [(show (0 : ℝ) < ($m : ℝ) from by
          exact_mod_cast (show 0 < $m from by lia)),
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 2,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 3,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 4,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 5,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 6])
  else
    `(tactic| ring_nf <;> linarith only [(Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)),
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 2,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 3,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 4,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 5,
        pow_nonneg (Nat.cast_nonneg $m : (0 : ℝ) ≤ ($m : ℝ)) 6])
  let mPos : TSyntax `tactic ← if m0 > 0 then
    `(tactic| have rr_hm_pos : (0 : ℝ) < ($m : ℝ) := by
      exact_mod_cast (show 0 < $m from by lia))
  else
    `(tactic| skip)
  let shiftedPos : TSyntax `tactic ← `(tactic| (
    have rr_hk_nonneg : (0 : ℝ) ≤ (($k : ℕ) : ℝ) := Nat.cast_nonneg $k
    have rr_hk_sq : (0 : ℝ) ≤ (($k : ℕ) : ℝ) ^ 2 := pow_nonneg rr_hk_nonneg 2
    have rr_hk_cube : (0 : ℝ) ≤ (($k : ℕ) : ℝ) ^ 3 := pow_nonneg rr_hk_nonneg 3
    have rr_hk_four : (0 : ℝ) ≤ (($k : ℕ) : ℝ) ^ 4 := pow_nonneg rr_hk_nonneg 4
    have rr_hk_five : (0 : ℝ) ≤ (($k : ℕ) : ℝ) ^ 5 := pow_nonneg rr_hk_nonneg 5
    have rr_hk_six : (0 : ℝ) ≤ (($k : ℕ) : ℝ) ^ 6 := pow_nonneg rr_hk_nonneg 6
    nlinarith))
  let hsign ← if negative then
    `(tactic| have $name : $hnumSign := by
      rw [$hnum:ident, $hden:ident]
      $mPos:tactic
      apply div_neg_of_neg_of_pos
      · $negNum:tactic
      · $shiftedPos:tactic)
  else
    `(tactic| have $name : $hnumSign := by
      rw [$hnum:ident, $hden:ident]
      $mPos:tactic
      apply div_pos
      · $shiftedPos:tactic
      · $shiftedPos:tactic)
  return #[hnumEq, hdenEq, hsign]

def cfiExpTerm (law : CFLaw) (a : Term) : TacticM Term :=
  if law.D0 == 0 then pure a else `($(rowNumLit law.D0) + $a)

def cfiKey (plan : CFPlan) (degree : Nat) : TacticM Unit := do
  let P := mkIdent plan.P
  let s := plan.s
  let k := plan.k
  let n := mkIdent `rr_n
  let ih := mkIdent `rr_ih
  let key := mkIdent `rr_key
  let q ← qpolyTerm plan.facs[0]!
  let cT : Term := mkIdent ``Polynomial.C
  let xT : Term := mkIdent ``Polynomial.X
  let law := plan.laws[0]!
  let qAt (a : Term) : TacticM Term := do
    let e ← cfiExpTerm law a
    `($q ^ $e)
  let rowAt (a : Term) : TacticM Term :=
    if s == 0 then `($P $a) else `($P ($a + $(rowNumLit s)))
  let stmt (a : Term) : TacticM Term := do
    let x ← `((($a : ℕ) : ℝ))
    let t0 ← ratPolyAtTerm plan.resid[0]!.coeffs x
    let t1 ← ratPolyAtTerm plan.resid[1]!.coeffs x
    let t2 ← ratPolyAtTerm plan.resid[2]!.coeffs x
    let res ← if degree == 1 then
      `($cT ($t0) + $cT ($t1) * $xT)
    else
      `($cT ($t0) + $cT ($t1) * $xT + $cT ($t2) * $xT ^ 2)
    if degree == 1 then
      `($(← rowAt a) = $res * $(← qAt a))
    else
      `($(← rowAt a) = $(← qAt a) * $res)
  let baseTac ← `(Lean.Parser.Tactic.tacticSeq|
    simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, $P:ident]
    rr_poly_identity)
  let mut base : Array Term := #[]
  for _ in [0:k] do
    base := base.push (← `(by $baseTac))
  let baseTerm ← if k == 1 then pure base[0]! else `(⟨$base,*⟩)
  let eqn := mkIdent plan.eqn
  let mut rules : Array Term := #[]
  let eqnApp ← if s == 0 then `($eqn $n) else `($eqn ($n + $(rowNumLit s)))
  rules := rules.push eqnApp
  let mut tacs : Array (TSyntax `tactic) := #[]
  for j in plan.lags do
    let hrow := mkIdent (Name.mkSimple s!"rr_cfi_hrow{j}")
    let h ← rightNestedAndProj (← `($ih)) j k
    if s > 0 && j > 0 then
      tacs := tacs.push (← `(tactic| have $hrow :=
        (congrArg $P (Nat.add_right_comm $n $(rowNumLit s) $(rowNumLit j))).trans $h))
    else
      tacs := tacs.push (← `(tactic| have $hrow := $h))
    rules := rules.push hrow
  let stNew ← stmt (← `($n + $(rowNumLit k)))
  let rwRules ← rules.mapM fun t => `(Lean.Parser.Tactic.rwRule| $t:term)
  let mut inner : Array (TSyntax `tactic) := #[]
  if s > 0 then
    inner := inner.push (← `(tactic|
      refine (congrArg $P (Nat.add_right_comm $n $(rowNumLit k) $(rowNumLit s))).trans ?_))
  inner := inner.push (← `(tactic| rw [$rwRules,*]))
  inner := inner.push (← `(tactic| rr_cf_identity))
  let hnew := mkIdent `rr_cfi_hnew
  tacs := tacs.push (← `(tactic| have $hnew : $stNew := by $inner*))
  let mut comps : Array Term := #[]
  for j in [1:k] do
    comps := comps.push (← rightNestedAndProj (← `($ih)) j k)
  comps := comps.push hnew
  let newTuple ← if comps.size == 1 then pure comps[0]! else `(⟨$comps,*⟩)
  tacs := tacs.push (← `(tactic| exact $newTuple))
  let mut tuple : Term ← stmt (← `($n + $(rowNumLit (k - 1))))
  for j in (List.range (k - 1)).reverse do
    let sj ← stmt (← `($n + $(rowNumLit j)))
    tuple ← `($sj ∧ $tuple)
  let keyStx ← `(tactic| have $key : ∀ $n:ident : ℕ, $tuple := by
    intro $n:ident
    induction $n:ident with
    | zero => exact $baseTerm
    | succ $n:ident $ih:ident => $tacs*)
  evalTactic keyStx

def cfiProof (cp : CFIPlan) : TacticM Unit := do
  let plan := cp.plan
  let P := mkIdent plan.P
  let s := plan.s
  let m0 := cp.m0
  let q ← qpolyTerm plan.facs[0]!
  let cT : Term := mkIdent ``Polynomial.C
  let xT : Term := mkIdent ``Polynomial.X
  let m := mkIdent `rr_m
  let k ← `($m - $(rowNumLit m0))
  let rowAt (a : Term) : TacticM Term :=
    if s == 0 then `($P $a) else `($P ($a + $(rowNumLit s)))
  let r ← residualAtTerm plan m
  let mnext ← `($m + 1)
  let rnext ← residualAtTerm plan mnext
  let rlin ← residualLinearAtTerm plan m
  let rlinNext ← residualLinearAtTerm plan mnext
  let a ← qpolyAtTerm plan.resid[cp.degree]! m
  let b ← if cp.degree == 1 then
    qpolyAtTerm plan.resid[0]! m
  else
    qpolyAtTerm plan.resid[1]! m
  let c ← qpolyAtTerm plan.resid[0]! m
  let p ← ratFunAtTerm cp.p m
  let d ← ratFunAtTerm cp.d m
  let α ← ratFunAtTerm cp.α m
  let β ← ratFunAtTerm cp.β m
  let hshift : TSyntax `tactic ← `(tactic| have rr_hshift : ($m : ℝ) =
      ($(rowNumLit m0) : ℝ) + (($k : ℕ) : ℝ) := by
    have rr_hnat : $(rowNumLit m0) + $k = $m := Nat.add_sub_of_le rr_hm
    exact_mod_cast rr_hnat.symm)
  let mut setup : Array (TSyntax `tactic) := #[hshift]
  setup := setup ++ (← proveSign (mkIdent `rr_ha)
    ⟨plan.resid[cp.degree]!, QPoly.const 1⟩ m0 m k false)
  setup := setup ++ (← proveSign (mkIdent `rr_hp) cp.p m0 m k false)
  if cp.degree == 1 then
    setup := setup ++ (← proveSign (mkIdent `rr_hbeta) cp.β m0 m k true)
  else
    setup := setup ++ (← proveSign (mkIdent `rr_halpha) cp.α m0 m k true)
    setup := setup ++ (← proveSign (mkIdent `rr_hcert) cp.cert m0 m k true)
  let hR : TSyntax `tactic ← if cp.degree == 1 then
    `(tactic| have rr_hR : $rlin = $cT ($a) * $xT + $cT ($b) := by rr_poly_identity)
  else
    `(tactic| have rr_hR : $r = $cT ($a) * $xT ^ 2 + $cT ($b) * $xT + $cT ($c) := by
      rr_poly_identity)
  let hmPos : TSyntax `tactic ← if m0 > 0 then
    `(tactic| have rr_hm_pos : (0 : ℝ) < ($m : ℝ) := by
      exact_mod_cast (show 0 < $m from by lia))
  else
    `(tactic| skip)
  let certField : TSyntax `tactic ← if m0 > 0 then
    `(tactic| field_simp (discharger :=
      (first | positivity | nlinarith)) <;> ring1)
  else
    `(tactic| first | rr_cf_field | ring1)
  let finish : TSyntax `tactic ←
    `(tactic| simpa only [Nat.add_zero, Nat.zero_add] using rr_hthm)
  let hqS : TSyntax `tactic ← if cp.degree == 1 then
    `(tactic| have rr_hqS : $q * $rlinNext = $rlin *
        ($cT ($p) * $xT + $cT ($d)) + $cT ($β) := by
      apply Polynomial.funext
      intro rr_x
      simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_zero,
        Polynomial.eval_ofNat, Polynomial.eval_natCast]
      push_cast
      have rr_hm_nonneg : (0 : ℝ) ≤ ($m : ℝ) := Nat.cast_nonneg $m
      have rr_hm_sq : (0 : ℝ) ≤ ($m : ℝ) ^ 2 := pow_nonneg rr_hm_nonneg 2
      have rr_hm_cube : (0 : ℝ) ≤ ($m : ℝ) ^ 3 := pow_nonneg rr_hm_nonneg 3
      have rr_hm_four : (0 : ℝ) ≤ ($m : ℝ) ^ 4 := pow_nonneg rr_hm_nonneg 4
      have rr_hm_five : (0 : ℝ) ≤ ($m : ℝ) ^ 5 := pow_nonneg rr_hm_nonneg 5
      $hmPos:tactic
      first | rr_cf_field | ring1)
  else
    `(tactic| have rr_hqS : $q * $rnext = $r *
        ($cT ($p) * $xT + $cT ($d)) + ($cT ($α) * $xT + $cT ($β)) := by
      apply Polynomial.funext
      intro rr_x
      simp only [RealRooted.div_ofNat_eq_C_mul, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_zero,
        Polynomial.eval_ofNat, Polynomial.eval_natCast]
      push_cast
      have rr_hm_nonneg : (0 : ℝ) ≤ ($m : ℝ) := Nat.cast_nonneg $m
      have rr_hm_sq : (0 : ℝ) ≤ ($m : ℝ) ^ 2 := pow_nonneg rr_hm_nonneg 2
      have rr_hm_cube : (0 : ℝ) ≤ ($m : ℝ) ^ 3 := pow_nonneg rr_hm_nonneg 3
      have rr_hm_four : (0 : ℝ) ≤ ($m : ℝ) ^ 4 := pow_nonneg rr_hm_nonneg 4
      have rr_hm_five : (0 : ℝ) ≤ ($m : ℝ) ^ 5 := pow_nonneg rr_hm_nonneg 5
      $hmPos:tactic
      first | rr_cf_field | ring1)
  let hinter := mkIdent `rr_cfi
  let key := mkIdent `rr_key
  let e1 ← cfiExpTerm plan.laws[0]! m
  let e2 ← cfiExpTerm plan.laws[0]! (← `($m + 1))
  let rowm ← rowAt m
  let rownext ← rowAt (← `($m + 1))
  let key1 ← rightNestedAndProj (← `($key $m)) 0 plan.k
  let key2 ← rightNestedAndProj (← `($key ($m + 1))) 0 plan.k
  let key1rw ← `(Lean.Parser.Tactic.rwRule| $key1:term)
  let key2rw ← `(Lean.Parser.Tactic.rwRule| $key2:term)
  let qpow1 ← `((($q : ℝ[X]) ^ $e1))
  let qpow2 ← `((($q : ℝ[X]) ^ $e2))
  let keyRw : TSyntax `tactic ← `(tactic| (
    have rr_hkey1' : $rowm = ($qpow1 : ℝ[X]) * $r := by
      rw [$key1rw]
      rr_poly_identity
    have rr_hkey2' : $rownext = ($qpow2 : ℝ[X]) * $rnext := by
      rw [$key2rw]
      rr_poly_identity
    rw [rr_hkey1', rr_hkey2']))
  let ha := mkIdent `rr_ha
  let hp := mkIdent `rr_hp
  let halpha := mkIdent `rr_halpha
  let hbeta := mkIdent `rr_hbeta
  let hcert := mkIdent `rr_hcert
  let hcore ← if cp.degree == 1 then
    `(tactic|
      have $hinter : ∀ $m : ℕ, $(rowNumLit m0) ≤ $m →
          RealRooted.Interlaces $rowm $rownext := by
        intro $m rr_hm
        $setup*
        $hR
        $hqS
        have rr_hkey1 := $key1
        have rr_hkey2 := $key2
        simp only [Nat.add_zero, Nat.zero_add] at rr_hkey1 rr_hkey2 ⊢
        rw [$key1rw, $key2rw]
        have rr_he : $e2 = $e1 + 1 := by simp
        rw [rr_he]
        convert
          (RealRooted.Interlaces.pow_mul_of_linear_remainder (q := $q)
          (R := $rlin) (S := $rlinNext) $e1
          rr_hR rr_hqS (by
            apply Polynomial.Splits.of_natDegree_le_one
            compute_degree!) (by
            intro rr_hq0
            have rr_hq1 := congrArg (fun z : ℝ[X] => z.coeff 1) rr_hq0
            norm_num [Polynomial.coeff_one] at rr_hq1)
          (by simpa only [div_one] using $ha) $hp $hbeta) using 1 <;>
          simp [Nat.cast_add, Nat.cast_one] <;> ring)
  else
    `(tactic|
      have $hinter : ∀ $m : ℕ, $(rowNumLit m0) ≤ $m →
          RealRooted.Interlaces $rowm $rownext := by
        intro $m rr_hm
        $setup*
        $hR
        $hqS
        have rr_hkey1 := $key1
        have rr_hkey2 := $key2
        simp only [Nat.add_zero, Nat.zero_add] at rr_hkey1 rr_hkey2 ⊢
        $keyRw:tactic
        have rr_he : $e2 = $e1 + 1 := by simp
        rw [rr_he]
        have rr_hthm :=
          (RealRooted.Interlaces.pow_mul_of_quadratic_remainder (q := $q)
          (a := $a) (b := $b) (c := $c) (p := $p) (d := $d) (α := $α) (β := $β)
          (R := $r) (S := $rnext) $e1
          rr_hR rr_hqS (by
            apply Polynomial.Splits.of_natDegree_le_one
            compute_degree!) (by
            intro rr_hq0
            have rr_hq1 := congrArg (fun z : ℝ[X] => z.coeff 1) rr_hq0
            norm_num [Polynomial.coeff_one] at rr_hq1)
          (by simpa only [div_one] using $ha) $hp $halpha
          (by
            have rr_hm_nonneg : (0 : ℝ) ≤ ($m : ℝ) := Nat.cast_nonneg $m
            have rr_hm_sq : (0 : ℝ) ≤ ($m : ℝ) ^ 2 := pow_nonneg rr_hm_nonneg 2
            have rr_hm_cube : (0 : ℝ) ≤ ($m : ℝ) ^ 3 := pow_nonneg rr_hm_nonneg 3
            have rr_hm_four : (0 : ℝ) ≤ ($m : ℝ) ^ 4 := pow_nonneg rr_hm_nonneg 4
            have rr_hm_five : (0 : ℝ) ≤ ($m : ℝ) ^ 5 := pow_nonneg rr_hm_nonneg 5
            $hmPos:tactic
            have rr_hden_d : (0 : ℝ) < 3 / 2 + 5 / 4 * ($m : ℝ) +
                1 / 4 * ($m : ℝ) ^ 2 := by
              positivity
            have rr_hden_alpha : (0 : ℝ) < 3 / 4 + 5 / 8 * ($m : ℝ) +
                1 / 8 * ($m : ℝ) ^ 2 := by
              positivity
            have rr_hden_cert : (0 : ℝ) < 3 / 8192 + 1 / 2048 * ($m : ℝ) +
                7 / 32768 * ($m : ℝ) ^ 2 + 1 / 32768 * ($m : ℝ) ^ 3 := by
              positivity
            convert ($hcert) using 1 <;> $certField:tactic))
        $finish:tactic)
  evalTactic hcore
  let t ← Term.exprToSyntax (← mainRowIndex P)
  let bound := s + m0
  if bound == 0 then
    evalTactic (← `(tactic| exact $hinter $t (by simp)))
  else
    let baseStart := if m0 == 0 then 0 else 1
    for i in [baseStart:bound] do
      let hbase := mkIdent (Name.mkSimple s!"rr_cfi_base{i}")
      let ri ← `($P $(rowNumLit i))
      let rj ← `($P $(rowNumLit (i + 1)))
      evalTactic (← `(tactic| have $hbase :
          RealRooted.Interlaces $ri $rj := by
        simp [$P:ident] <;> rr_interlaces_explicit))
    let htop ← if m0 == 0 then
      `(tactic| (
        have rr_all : ∀ rr_t : ℕ,
            RealRooted.Interlaces ($P rr_t) ($P (rr_t + 1)) := by
          intro rr_t
          rcases Nat.lt_or_ge rr_t $(rowNumLit bound) with rr_hlt | rr_hge
          · interval_cases rr_t <;>
              simp only [Nat.reduceAdd, Nat.zero_add, Nat.add_zero] <;> assumption
          · have rr_hm : $(rowNumLit m0) ≤ rr_t - $(rowNumLit s) := by lia
            have rr_hi := $hinter (rr_t - $(rowNumLit s)) rr_hm
            have rr_hs : $(rowNumLit s) ≤ rr_t := by lia
            have rr_hnat : rr_t - $(rowNumLit s) + $(rowNumLit s) = rr_t :=
              Nat.sub_add_cancel rr_hs
            have rr_hnat_next : rr_t - $(rowNumLit s) + 1 + $(rowNumLit s) = rr_t + 1 := by
              lia
            simpa only [rr_hnat, rr_hnat_next] using rr_hi
        simpa using (rr_all $t)))
    else
      `(tactic| (
        have rr_all : ∀ rr_t : ℕ, 1 ≤ rr_t →
            RealRooted.Interlaces ($P rr_t) ($P (rr_t + 1)) := by
          intro rr_t rr_hpos
          rcases Nat.lt_or_ge rr_t $(rowNumLit bound) with rr_hlt | rr_hge
          · interval_cases rr_t <;>
              simp_all only [Nat.reduceAdd, Nat.zero_add, Nat.add_zero] <;> assumption
          · have rr_hm : $(rowNumLit m0) ≤ rr_t - $(rowNumLit s) := by lia
            have rr_hi := $hinter (rr_t - $(rowNumLit s)) rr_hm
            have rr_hs : $(rowNumLit s) ≤ rr_t := by lia
            have rr_hnat : rr_t - $(rowNumLit s) + $(rowNumLit s) = rr_t :=
              Nat.sub_add_cancel rr_hs
            have rr_hnat_next : rr_t - $(rowNumLit s) + 1 + $(rowNumLit s) = rr_t + 1 := by
              lia
            simpa only [rr_hnat, rr_hnat_next] using rr_hi
        have rr_tpos : 1 ≤ $t := by lia
        simpa using (rr_all $t rr_tpos)))
    evalTactic htop

/-- The closed-form interlacing route on the main goal `Interlaces (P t) (P (t + 1))`. -/
def closedFormInterlacesGoal : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOfArity ``RealRooted.Interlaces 2 do
    throwError "rr_cf_interlaces: the goal is not `Interlaces g f`"
  let some P ← findPolySeqConst? tgt
    | throwError "rr_cf_interlaces: no sequence `P : ℕ → ℝ[X]` in the goal"
  let some L ← linRec? P
    | throwError "rr_cf_interlaces: the recurrence is not linear"
  let result ← cfiProbe L
  match result with
  | .ok cp =>
    cfiKey cp.plan cp.degree
    cfiProof cp
  | .error msg => throwError "rr_cf_interlaces: {msg}"

/-- `rr_cf_interlaces` runs only the closed-form interlacing route. -/
elab "rr_cf_interlaces" : tactic => closedFormInterlacesGoal

end RealRooted.Tactic.CFI
