module

public import RealRooted.Tactic.Row.Reverse
public import RealRooted.Tactic.Row.FTransform
public import RealRooted.Interlacing.ReversalLeftDegree
public meta import RealRooted.Tactic.Row.Reverse
public meta import RealRooted.Tactic.Row.FTransform
public meta import RealRooted.Interlacing.ReversalLeftDegree

/-!
# Rational-coefficient reversal route

This inverts the reflected-row construction for first-order derivative
recurrences whose low-degree preimage multipliers have a common positive
denominator.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted

/-- Transfer consecutive interlacing through reflection when the reflected
rows have positive constant coefficient.  This variant derives negativity of
their roots directly and does not ask for degree data about the target rows. -/
theorem interlaces_of_eq_reflect_of_coeff_zero_pos
    {P R : ℕ → ℝ[X]} {D₀ : ℕ}
    (hPR : ∀ n, P n = reflect (D₀ + n) (R n))
    (hdeg : ∀ n, (R n).natDegree = D₀ + n)
    (hnn : ∀ n, HasNonnegCoeffs (R n))
    (hzero : ∀ n, 0 < (R n).coeff 0)
    (hR : ∀ n, Interlaces (R n) (R (n + 1))) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  have hneg : ∀ m, ∀ t ∈ (R m).roots, t < 0 := by
    intro m t ht
    refine lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs (hnn m) t ht) ?_
    intro h
    have hroot := isRoot_of_mem_roots ht
    rw [h, IsRoot.def, ← coeff_zero_eq_eval_zero] at hroot
    exact (hzero m).ne' hroot
  intro n
  rw [hPR n, hPR (n + 1)]
  simpa only [reverse, hdeg] using
    interlaces_reverse_of_roots_neg (hR n) (hneg (n + 1)) (hneg n)

end RealRooted

namespace RealRooted.Tactic

local syntax (name := rrRationalReverseAuxInterlaces)
  "rr_rational_reverse_aux_interlaces" : tactic

elab_rules : tactic
  | `(tactic| rr_rational_reverse_aux_interlaces) => fTransformInterlacesGoal

/-- The data of the reflected first-order recurrence whose multipliers are rational functions of
`n`. -/
structure RationalReversal where
  /-- The linear recurrence data of the original sequence. -/
  L : LinRecData
  /-- The degree of row `0`, so that row `n` has degree `D₀ + n`. -/
  D₀ : Nat
  /-- The reflected first row `X ^ D₀ * P 0 (1 / X)`. -/
  base : QPoly
  /-- The multiplier of the derivative term, by powers of `X`, each by powers of `n`, before
  dividing by `den`. -/
  a₁ : Array (Array Rat)
  /-- The multiplier of the undifferentiated term, by powers of `X`, each by powers of `n`,
  before dividing by `den`. -/
  a₀ : Array (Array Rat)
  /-- The common positive denominator of the multipliers, by powers of `n`. -/
  den : Array Rat

/-- Exact recognizer for a non-palindromic first-order family whose inverse
reflection has rational-function multipliers. -/
def rationalReversal? (P : Name) : MetaM (Option RationalReversal) := do
  let some L ← linRec? P | return none
  unless L.offset == 1 &&
      L.terms.all (fun (j, i, _) => j == 0 && i ≤ 1) &&
      L.terms.any (·.2.1 == 1) do return none
  let (some gate₁, some gate₀) :=
    (← L.coeffAt? 0 1 0, ← L.coeffAt? 0 0 0) | return none
  unless gate₁.natDegree ≤ 3 && gate₀.natDegree ≤ 2 do return none
  let some gateReflected₁ := (-gate₁).divExact? QPoly.X | return none
  unless gateReflected₁.natDegree ≤ 2 do return none
  let some baseRows ← linRecBaseRows? P | return none
  let some r0 := baseRows[0]? | return none
  let D₀ := r0.natDegree
  let mut a₁s : Array QPoly := #[]
  let mut a₀s : Array QPoly := #[]
  for n in [0:12] do
    let (some target₁, some target₀) :=
      (← L.coeffAt? 0 1 n, ← L.coeffAt? 0 0 n) | return none
    unless target₁.natDegree ≤ 3 && target₀.natDegree ≤ 2 do
      return none
    let some reflected₁ := (-target₁).divExact? QPoly.X | return none
    unless reflected₁.natDegree ≤ 2 do return none
    let N : Rat := D₀ + n
    let reflected₀ := target₀ - QPoly.smul N reflected₁
    unless reflected₀.natDegree ≤ 1 do return none
    a₁s := a₁s.push (reflected₁.reflect 2)
    a₀s := a₀s.push (reflected₀.reflect 1)
  let some (a₁, a₀, den) := fitRationalXPolys? a₁s a₀s | return none
  let some rows ← linRecRows? L 12 | return none
  let mut palindromic := true
  for m in [0:12] do
    let some p := rows[m]? | return none
    if p.isZero || p.natDegree != D₀ + m || p.coeff 0 == 0 || p.lead ≤ 0 then
      return none
    unless p.coeffs.all (0 ≤ ·) do return none
    if (p.reflect (D₀ + m)).coeffs != p.coeffs then palindromic := false
  if palindromic then return none
  return some { L, D₀, base := r0.reflect D₀, a₁, a₀, den }

private def rationalLrCoeffFun (L : LinRecData) (i : Nat) : TacticM Term := do
  let n := mkIdent `n
  let mut acc : Option Term := none
  for (j', i', A) in L.terms do
    if j' != 0 || i' != i then continue
    let t ← Term.exprToSyntax A
    acc ← match acc with
      | none => pure (some (← `($t $n:ident)))
      | some s => pure (some (← `($s + $t $n:ident)))
  match acc with
  | some t => `(fun $n:ident : ℕ => $t)
  | none => `(fun _ : ℕ => (0 : ℝ[X]))

/-- Define the rational reflected auxiliary family and certify its link to the
original rows. -/
def rationalReversalLink (P : Name) (rv : RationalReversal) :
    TacticM (Ident × Ident × Ident × Ident) := do
  let nm ← freshAuxName "ratRevAux"
  let R := mkIdent nm
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let a₁ ← rationalXPolyTerm rv.a₁ rv.den N
  let a₀ ← rationalXPolyTerm rv.a₀ rv.den N
  elabAuxCommand (← `(command|
    noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
      | 0 => $(← qpolyTerm rv.base)
      | $n:ident + 1 => $a₁ * ($R $n).derivative + $a₀ * $R $n))
  let Pi := mkIdent P
  let eqn := mkIdent rv.L.eqn
  let D₀ := rowNumLit rv.D₀
  let simpReflect ← `(tactic|
    simp only [reflect_add, reflect_neg, reflect_C_mul, reflect_C_mul_X_pow,
      reflect_C, reflect_monomial, reflect_X, reflect_one, reflect_ofNat_mul,
      reflect_zero, revAt_eq_ite, neg_mul, one_mul, mul_one, zero_mul,
      mul_zero, add_zero, zero_add])
  let identity ← `(tactic| first
    | ($simpReflect:tactic <;> norm_num <;> rr_cf_identity)
    | ($simpReflect:tactic <;> rr_cf_identity)
    | rr_cf_identity)
  let hP ← `(fun $n:ident => by beta_reduce; rw [$R:ident] <;> ring)
  let hR ← `(fun $n:ident => by beta_reduce; rw [$eqn:ident $n:ident] <;> ring)
  let deg ← `(fun $n:ident => by
    beta_reduce
    first | (compute_degree <;> norm_num) | simp)
  let hPdeg ← `(fun $n:ident => le_of_eq (by rr_row_natDegree))
  let base ← `(by
    simp only [$R:ident, $Pi:ident]
    first
      | done
      | ($simpReflect:tactic <;> norm_num <;> done)
      | ($simpReflect:tactic <;> rr_poly_identity))
  let zero ← `(fun _ : ℕ => (0 : ℝ[X]))
  let A₁ ← `(fun $n:ident : ℕ =>
    $(← rationalXPolyTerm rv.a₁ rv.den N))
  let A₀ ← `(fun $n:ident : ℕ =>
    $(← rationalXPolyTerm rv.a₀ rv.den N))
  let proof ← `(RealRooted.eq_reflect_of_secondOrderDerivativeRecurrence_of_left_degree
    (P := $R) (R := $Pi) (D₀ := $D₀)
    (A₂ := $zero) (A₁ := $A₁) (A₀ := $A₀)
    (B₂ := $zero) (B₁ := $(← rationalLrCoeffFun rv.L 1))
    (B₀ := $(← rationalLrCoeffFun rv.L 0))
    $hP $hR $deg $deg $deg
    (fun $n:ident => by beta_reduce; $identity:tactic)
    (fun $n:ident => by beta_reduce; $identity:tactic)
    (fun $n:ident => by beta_reduce; $identity:tactic)
    $hPdeg $base)
  let backName ← freshAuxName "ratRevBack"
  let back := mkIdent backName
  elabAuxCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ backName)) (n : ℕ) :
        $R n = Polynomial.reflect ($D₀ + n) ($Pi n) :=
      $proof n))
  let linkName ← freshAuxName "ratRevLink"
  let link := mkIdent linkName
  elabAuxCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ linkName)) (n : ℕ) :
        $Pi n = Polynomial.reflect ($D₀ + n) ($R n) := by
      rw [$back n, Polynomial.reflect_reflect]))
  let nonnegName ← freshAuxName "ratRevNonneg"
  let nonneg := mkIdent nonnegName
  elabAuxCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ nonnegName)) (m : ℕ) :
        RealRooted.HasNonnegCoeffs ($R m) := by
      refine RealRooted.derivativeRecurrence_hasNonnegCoeffs
        (P := $R) (A := $A₁) (B := $A₀)
        (fun n => by rw [$R:ident]) ?_ ?_ ?_ m
      · intro n
        beta_reduce
        rr_row_side
      · intro n
        beta_reduce
        rr_row_side
      · simp only [$R:ident]
        rr_row_side))
  let positiveZeroName ← freshAuxName "ratRevPositiveZero"
  let positiveZero := mkIdent positiveZeroName
  elabAuxCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ positiveZeroName)) (m : ℕ) :
        0 < ($R m).coeff 0 := by
      induction m with
      | zero => norm_num [$R:ident]
      | succ n ih =>
          rw [Polynomial.coeff_zero_eq_eval_zero, $R:ident,
            Polynomial.eval_add]
          have hder : 0 ≤ ($R n).derivative.eval 0 := by
            exact (RealRooted.HasNonnegCoeffs.derivative
              ($nonneg n)).eval_nonneg le_rfl
          have ha : 0 ≤ ($A₁ n).eval 0 := by
            beta_reduce
            simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
              Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_zero]
            rr_row_field
          have hb : 0 < ($A₀ n).eval 0 := by
            beta_reduce
            simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
              Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_zero]
            rr_row_field
          have ih' : 0 < ($R n).eval 0 := by
            simpa only [Polynomial.coeff_zero_eq_eval_zero] using ih
          apply add_pos_of_nonneg_of_pos
          · rw [Polynomial.eval_mul]
            exact mul_nonneg ha hder
          · rw [Polynomial.eval_mul]
            exact mul_pos hb ih'))
  return (R, link, nonneg, positiveZero)

/-- Transfer through the rational reflected auxiliary rows using
`interlaces_of_eq_reflect`. -/
def rationalReverseInterlacesGoal : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let isRationalAux := match P with
    | .str _ s => s.startsWith "ratRevAux"
    | _ => false
  if isRevAux P || isRationalAux then
    throwError "rr_row: no reversal of a reversed sequence"
  let some rv ← rationalReversal? P
    | throwError "rr_row: the reversed rows have no rational fit"
  let t ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let (R, link, nonneg, positiveZero) ← rationalReversalLink P rv
  evalTactic (← `(tactic|
    exact RealRooted.interlaces_of_eq_reflect_of_coeff_zero_pos (R := $R) $link
      (fun n => by rr_row_natDegree) $nonneg
      $positiveZero
      (fun n => by rr_rational_reverse_aux_interlaces) $t))

end RealRooted.Tactic
