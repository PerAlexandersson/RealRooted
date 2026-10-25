module

public import RealRooted.SymmetricDecomposition.FPolynomialSequence
public import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
public import RealRooted.MaWang.DerivativeStep
public import RealRooted.Tactic.Row.Support
public meta import RealRooted.SymmetricDecomposition.FPolynomialSequence
public meta import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
public meta import RealRooted.MaWang.DerivativeStep
public meta import RealRooted.Tactic.Row.Support

/-!
# Row tactics: the `f`-polynomial transform

Rows `P n = fPolynomial n (Q n)` of the Brändén–Solus transform
`fPolynomial d h = ∑ hₖ Xᵏ (X + 1)^(d - k)`: a first-order derivative recurrence
`Q (n + 1) = a n * Q n' + b n * Q n` with `deg a ≤ 2`, `deg b ≤ 1` transforms into
`P (n + 1) = (X + 1) f₂(a n) P n' + (f₁(b n) - n f₂(a n)) P n`
(`RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero`).
Conversely, when the recurrence of
`P` has that shape, `fTransform?` reads `a` and `b` off it exactly (`A n = (X + 1) Ã n`,
`a n = (1 - t)² Ã n (t / (1 - t))`, `b n = (1 - t) (B n + n Ã n) (t / (1 - t))`), and
`fTransformSplitsGoal` defines `Q` as an auxiliary recursive sequence, proves the link and
transfers splitting from `Q` (`RealRooted.splits_of_eq_fPolynomial`).  The alternating-runs rows
A008970, A059427 and A186370 have this shape: their `Q` grows by half a degree per step, so
`rr_row_splits` proves it where it cannot prove `P` directly.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The inverse transform in the degree box `d`: `(1 - t)^d p (t / (1 - t))`. -/
def QPoly.invF (d : Nat) (p : QPoly) : QPoly := Id.run do
  let oneMinus : QPoly := QPoly.const 1 - QPoly.X
  let mut acc : QPoly := QPoly.const 0
  for j in [0:d + 1] do
    acc := acc + QPoly.smul (p.coeff j) (QPoly.pow QPoly.X j * QPoly.pow oneMinus (d - j))
  return acc

/-- The transformed recurrence: the base row and the numerators of the
multipliers `a`, `b`, fitted over one denominator in `n`. -/
structure FTransData where
  /-- The linear recurrence data of the original sequence. -/
  L : LinRecData
  /-- The first row of the original sequence, a nonzero constant polynomial. -/
  base : QPoly
  /-- The second row of the transformed sequence, `a 0 * base' + b 0 * base`. -/
  shiftedBase : QPoly
  /-- The numerators of the multiplier `a n` of the derivative term, by powers of
  `X`, each by powers of `n`. -/
  a : Array (Array Rat)
  /-- The numerators of the multiplier `b n` of the undifferentiated term, by powers of
  `X`, each by powers of `n`. -/
  b : Array (Array Rat)
  /-- Common denominator of every coefficient of `a` and `b`. -/
  den : Array Rat
  /-- `0` for degree `n / 2`, `1` for `(n + 1) / 2`, and `2` for `n - 1`. -/
  degreeShift : Nat

/-- Fit several rational sequences with one denominator having positive
constant term and nonnegative coefficients.  The returned numerator arrays
and denominator are validated on every supplied exact sample. -/
def fitCommonPositiveDenominator? (vals : Array (Array Rat)) :
    Option (Array (Array Rat) × Array Rat) := Id.run do
  if vals.isEmpty then return none
  let samples := vals[0]!.size
  unless vals.all (·.size == samples) do return none
  for numDegree in [0:7] do
    for denDegree in [0:5] do
      let numWidth := numDegree + 1
      let denWidth := denDegree + 1
      let cols := vals.size * numWidth + denWidth
      let mut rows : Array (Array Rat) := #[]
      for i in [0:vals.size] do
        for n in [0:samples] do
          let x : Rat := n
          let v := (vals[i]!)[n]!
          let row := (Array.range cols).map fun c =>
            if c < vals.size * numWidth then
              let block := c / numWidth
              let power := c % numWidth
              if block == i then x ^ power else 0
            else
              -v * x ^ (c - vals.size * numWidth)
          rows := rows.push row
      for w in ratNullspace rows cols do
        let d0 := w[vals.size * numWidth]!
        if d0 == 0 then continue
        let sgn : Rat := if d0 < 0 then -1 else 1
        let den := QPoly.norm <| (Array.range denWidth).map fun j =>
          sgn * w[vals.size * numWidth + j]!
        unless 0 < den.coeff 0 && den.coeffs.all (0 ≤ ·) do continue
        let nums := (Array.range vals.size).map fun i =>
          (QPoly.norm <| (Array.range numWidth).map fun j =>
            sgn * w[i * numWidth + j]!).coeffs
        let valid := (List.range vals.size).all fun i =>
          (List.range samples).all fun n =>
            (QPoly.norm nums[i]!).eval n == (vals[i]!)[n]! * den.eval n
        if valid then return some (nums, den.coeffs)
  return none

/-- Fit two sampled `X`-polynomial sequences over one positive denominator. -/
def fitRationalXPolys? (as bs : Array QPoly) :
    Option (Array (Array Rat) × Array (Array Rat) × Array Rat) := Id.run do
  let aw := as.foldl (fun w q => max w (q.natDegree + 1)) 0
  let bw := bs.foldl (fun w q => max w (q.natDegree + 1)) 0
  let vals := (Array.range (aw + bw)).map fun j =>
    if j < aw then as.map (·.coeff j) else bs.map (·.coeff (j - aw))
  let some (nums, den) := fitCommonPositiveDenominator? vals | return none
  return (nums.extract 0 aw, nums.extract aw (aw + bw), den)

/-- An `X`-polynomial whose coefficient functions share a scalar
denominator, emitted with that denominator explicitly cleared. -/
def rationalXPolyTerm (nums : Array (Array Rat)) (den : Array Rat)
    (N : Term) : TacticM Term := do
  let p ← xPolyTerm nums N
  if den.size == 1 && den[0]! == 1 then return p
  let d ← nPolyTerm den N
  `(Polynomial.C (($d)⁻¹) * $p)

/-- Read `Q (n + 1) = a n Q n' + b n Q n` off a first-order derivative
recurrence `P (n + 1) = A n P n' + B n P n` with `P 0` constant and
`X + 1 ∣ A n`; the transformed rows must have real roots on the computed
range.  Coefficients rational in `n` are fitted over a common positive
denominator. -/
def fTransform? (P : Name) : MetaM (Option FTransData) := do
  let some L ← linRec? P | return none
  unless L.offset == 1 && L.terms.all (fun (j, i, _) => j == 0 && i ≤ 1) &&
      L.terms.any (·.2.1 == 1) do return none
  let some rows ← linRecRows? L 10 | return none
  let some r0 := rows[0]? | return none
  if r0.isZero || r0.natDegree != 0 then return none
  let xPlusOne : QPoly := QPoly.X + QPoly.const 1
  let mut as : Array QPoly := #[]
  let mut bs : Array QPoly := #[]
  for n in [0:12] do
    let (some A, some B) := (← L.coeffAt? 0 1 n, ← L.coeffAt? 0 0 n) | return none
    let some At := A.divExact? xPlusOne | return none
    unless At.natDegree ≤ 2 do return none
    let Bt := B + QPoly.smul (n : Rat) At
    unless Bt.isZero || Bt.natDegree ≤ 1 do return none
    as := as.push (QPoly.invF 2 At)
    bs := bs.push (QPoly.invF 1 Bt)
  -- the transformed rows must have real roots, the input of the transfer
  let shiftedBase := as[0]! * r0.derivative + bs[0]! * r0
  let mut q := r0
  let mut floorDegrees := true
  let mut ceilDegrees := true
  let mut predDegrees := true
  for n in [0:10] do
    unless q.natDegree == 0 || q.realRooted do return none
    floorDegrees := floorDegrees && q.natDegree == n / 2
    ceilDegrees := ceilDegrees && q.natDegree == (n + 1) / 2
    predDegrees := predDegrees && q.natDegree == n - 1
    q := as[n]! * q.derivative + bs[n]! * q
  let some (a, b, den) := fitRationalXPolys? as bs
    | return none
  let degreeShift? := if ceilDegrees then some 1 else if floorDegrees then some 0
    else if predDegrees then some 2 else none
  let some degreeShift := degreeShift? | return none
  return some { L, base := r0, shiftedBase, a, b, den, degreeShift }

/-- `rr_row_splits` through the transformed rows. -/
def fTransformSplitsGoal : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let some d ← fTransform? P | throwError "rr_row: the recurrence is not an f-transform"
  let t ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let nm ← freshAuxName "fAux"
  let Q := mkIdent nm
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let aT ← rationalXPolyTerm d.a d.den N
  let bT ← rationalXPolyTerm d.b d.den N
  elabAuxCommand (← `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
    | 0 => $(← qpolyTerm d.base)
    | $n:ident + 1 => $aT * ($Q $n).derivative + $bT * $Q $n))
  let Pi := mkIdent P
  let eqn := mkIdent d.L.eqn
  let link := mkIdent `hlink_f
  let identity ← `(tactic| first
    | (simp only [RealRooted.fPolynomial_two, RealRooted.fPolynomial_one, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X]
       norm_num [map_ofNat]
       ring)
    | rr_cf_identity)
  withMainContext do
  evalTactic (← `(tactic|
    have $link:ident := RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero
      (P := $Pi) (Q := $Q) (a := fun $n:ident : ℕ => $aT) (b := fun $n:ident : ℕ => $bT)
      (ha := fun $n:ident => by compute_degree) (hb := fun $n:ident => by compute_degree)
      (hQ := fun $n:ident => by rw [$Q:ident])
      (h0deg := by simp [$Q:ident])
      (hP := fun $n:ident => by rw [$eqn:ident $n:ident]; $identity:tactic)
      (h0 := by simp [$Pi:ident, $Q:ident, RealRooted.fPolynomial, map_ofNat])))
  withMainContext do
  evalTactic (← `(tactic|
    exact RealRooted.splits_of_eq_fPolynomial $link
      (RealRooted.natDegree_le_of_derivRec (Q := $Q) (a := fun $n:ident : ℕ => $aT)
        (b := fun $n:ident : ℕ => $bT) (fun $n:ident => by compute_degree)
        (fun $n:ident => by compute_degree) (fun $n:ident => by rw [$Q:ident]) (by simp [$Q:ident]))
      (fun $n:ident => by rr_row_splits) $t))

local syntax (name := rrFTransformHalfMultiplier)
  "rr_f_transform_half_multiplier" : tactic

local syntax (name := rrFTransformFloorHalfMultiplier)
  "rr_f_transform_floor_half_multiplier" : tactic

local syntax (name := rrFTransformPredMultiplier)
  "rr_f_transform_pred_multiplier" : tactic

private def predMultiplierGoal : TacticM Unit := do
  evalTactic (← `(tactic| (
    intro n i j hj
    have hjNat : j ≤ n := le_trans hj (Nat.sub_le n 1)
    have hjReal : (j : ℝ) ≤ n := Nat.cast_le.mpr hjNat
    rcases i with _ | _ | _ | i <;>
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_neg, Polynomial.coeff_C_mul,
        Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
        Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat,
        Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
        Polynomial.coeff_zero, neg_mul, one_mul] <;>
      push_cast <;>
      first | positivity | nlinarith | rr_row_field)))

elab_rules : tactic
  | `(tactic| rr_f_transform_half_multiplier) => halfMultiplierGoal 0 1
  | `(tactic| rr_f_transform_floor_half_multiplier) => halfMultiplierGoal 0 0
  | `(tactic| rr_f_transform_pred_multiplier) => predMultiplierGoal

/-- Consecutive strict interlacing for a nonnegative derivative-recurrence sequence whose
degree is `(n + 1) / 2`, including the degree-zero initial row. -/
private theorem derivativeRecurrence_strictInterl_of_half_degree
    {Q A B : ℕ → ℝ[X]}
    (hrec : ∀ n, Q (n + 1) = A n * (Q n).derivative + B n * Q n)
    (hdeg : ∀ n, (Q n).natDegree = (n + 1) / 2)
    (hpos : ∀ n, 0 < (Q n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (Q n))
    (hA : ∀ n r, r ≤ 0 → (A n).eval r ≤ 0) :
    ∀ n, StrictInterl (Q n) (Q (n + 1))
  | 0 =>
      (interlaces_of_natDegree_eq_zero_of_natDegree_eq_one
        (Polynomial.leadingCoeff_ne_zero.mp (hpos 0).ne') (hdeg 0) (hdeg 1)).toStrictInterl
  | n + 1 => by
      refine derivativeRecurrence_strictInterl_step (hrec (n + 1))
        (derivativeRecurrence_strictInterl_of_half_degree hrec hdeg hpos hnn hA n).2.1.2
        (by rw [hdeg]; grind) (hpos (n + 1)) (hpos (n + 2))
        (by rw [hdeg, hdeg]; grind) (by rw [hdeg, hdeg]; grind) ?_
      intro r hr
      apply hA (n + 1) r
      exact roots_nonpos_of_hasNonnegCoeffs (hnn (n + 1)) r
        ((Polynomial.mem_roots
          (Polynomial.leadingCoeff_ne_zero.mp (hpos (n + 1)).ne')).mpr hr)

/-- Consecutive strict interlacing for a nonnegative derivative recurrence of
degree `n / 2`.  The Ma--Wang constant-row branch handles the initial
constant-to-constant step. -/
private theorem derivativeRecurrence_strictInterl_of_floor_half_degree
    {Q A B : ℕ → ℝ[X]}
    (hrec : ∀ n, Q (n + 1) = A n * (Q n).derivative + B n * Q n)
    (hdeg : ∀ n, (Q n).natDegree = n / 2)
    (hpos : ∀ n, 0 < (Q n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (Q n))
    (hA : ∀ n r, r ≤ 0 → (A n).eval r ≤ 0) :
    ∀ n, StrictInterl (Q n) (Q (n + 1)) := by
  have hstep (n : ℕ) (hs : (Q n).Splits) :
      StrictInterl (Q n) (Q (n + 1)) := by
    have hstrict := MaWang.strictInterl_derivative_of_nonpos_of_splits
      (u := B n) (v := A n) hs
      (by rw [add_comm, ← hrec n, hdeg, hdeg]; grind)
      (by rw [add_comm, ← hrec n, hdeg, hdeg]; grind)
      (by rw [add_comm, ← hrec n]; exact hpos (n + 1)) (hpos n) (by
        intro r hr
        apply hA n r
        exact roots_nonpos_of_hasNonnegCoeffs (hnn n) r
          ((Polynomial.mem_roots
            (Polynomial.leadingCoeff_ne_zero.mp (hpos n).ne')).mpr hr))
    rw [add_comm, ← hrec n] at hstrict
    exact hstrict
  intro n
  induction n with
  | zero =>
      exact hstep 0 (Polynomial.Splits.of_natDegree_eq_zero (by rw [hdeg]))
  | succ n ih => exact hstep (n + 1) ih.2.1.2

/-- The weak consecutive relation obtained from the strict half-growth
`f`-polynomial transfer, including its constant-to-linear initial step. -/
private theorem interlaces_fPolynomial_sequence
    (q : ℕ → ℝ[X])
    (hq_nonneg : ∀ j, HasNonnegCoeffs (q j))
    (hq_ne : ∀ j, q j ≠ 0)
    (hq_splits : ∀ j, (q j).Splits)
    (hq_deg : ∀ j, (q j).natDegree = (j + 1) / 2)
    (hq_interl : ∀ j, StrictInterl (q j) (q (j + 1)))
    (n : ℕ) : Interlaces (fPolynomial n (q n)) (fPolynomial (n + 1) (q (n + 1))) := by
  rcases n with _ | n
  · have hq0 : (q 0).natDegree ≤ 0 := by rw [hq_deg]
    have hq1 : (q 1).natDegree ≤ 1 := by rw [hq_deg]
    have h0 := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
      hq0 (hq_ne 0) (hq_splits 0) (hq_nonneg 0)
    have hdeg0 := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hq0 (hq_nonneg 0) (hq_ne 0)
    have hdeg1 := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hq1 (hq_nonneg 1) (hq_ne 1)
    exact interlaces_of_natDegree_eq_zero_of_natDegree_eq_one h0.1 hdeg0 hdeg1
  · have hstrict := StrictInterl.fPolynomial_sequence q hq_nonneg hq_ne hq_splits
      hq_deg hq_interl (n := n + 1) (by lia)
    apply hstrict.toInterlaces
    have hqn : (q (n + 1)).natDegree ≤ n + 1 := by rw [hq_deg]; grind
    have hqnext : (q (n + 1 + 1)).natDegree ≤ n + 1 + 1 := by rw [hq_deg]; grind
    rw [fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
        hqn (hq_nonneg (n + 1)) (hq_ne (n + 1)),
      fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
        hqnext (hq_nonneg (n + 1 + 1)) (hq_ne (n + 1 + 1))]

/-- Floor-half companion to `interlaces_fPolynomial_sequence`, with the same
constant-to-linear transformed base step. -/
private theorem interlaces_fPolynomial_sequence_floor
    (q : ℕ → ℝ[X])
    (hq_nonneg : ∀ j, HasNonnegCoeffs (q j))
    (hq_ne : ∀ j, q j ≠ 0)
    (hq_splits : ∀ j, (q j).Splits)
    (hq_deg : ∀ j, (q j).natDegree = j / 2)
    (hq_interl : ∀ j, StrictInterl (q j) (q (j + 1)))
    (n : ℕ) : Interlaces (fPolynomial n (q n))
      (fPolynomial (n + 1) (q (n + 1))) := by
  rcases n with _ | n
  · have hq0 : (q 0).natDegree ≤ 0 := by rw [hq_deg]
    have hq1 : (q 1).natDegree ≤ 1 := by rw [hq_deg]; lia
    have h0 := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
      hq0 (hq_ne 0) (hq_splits 0) (hq_nonneg 0)
    have hdeg0 := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hq0 (hq_nonneg 0) (hq_ne 0)
    have hdeg1 := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hq1 (hq_nonneg 1) (hq_ne 1)
    exact interlaces_of_natDegree_eq_zero_of_natDegree_eq_one h0.1 hdeg0 hdeg1
  · have hstrict := StrictInterl.fPolynomial_sequence_floor q hq_nonneg
      hq_ne hq_splits hq_deg hq_interl (n := n + 1)
    apply hstrict.toInterlaces
    have hqn : (q (n + 1)).natDegree ≤ n + 1 := by rw [hq_deg]; grind
    have hqnext : (q (n + 1 + 1)).natDegree ≤ n + 1 + 1 := by
      rw [hq_deg]
      grind
    rw [fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
        hqn (hq_nonneg (n + 1)) (hq_ne (n + 1)),
      fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
        hqnext (hq_nonneg (n + 1 + 1)) (hq_ne (n + 1 + 1))]

/-- Predecessor-degree companion to `interlaces_fPolynomial_sequence`. -/
private theorem interlaces_fPolynomial_sequence_pred
    (q : ℕ → ℝ[X])
    (hq_nonneg : ∀ j, HasNonnegCoeffs (q j))
    (hq_ne : ∀ j, q j ≠ 0)
    (hq_splits : ∀ j, (q j).Splits)
    (hq_deg : ∀ j, (q j).natDegree = j - 1)
    (hq_interl : ∀ j, StrictInterl (q j) (q (j + 1)))
    (n : ℕ) : Interlaces (fPolynomial n (q n))
      (fPolynomial (n + 1) (q (n + 1))) := by
  have hstrict := StrictInterl.fPolynomial_sequence_pred q hq_nonneg
    hq_ne hq_splits hq_deg hq_interl (n := n)
  apply hstrict.toInterlaces
  have hqn : (q n).natDegree ≤ n := by rw [hq_deg]; grind
  have hqnext : (q (n + 1)).natDegree ≤ n + 1 := by rw [hq_deg]; grind
  rw [fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hqn (hq_nonneg n) (hq_ne n),
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hqnext (hq_nonneg (n + 1)) (hq_ne (n + 1))]

private theorem strictInterl_of_natDegree_eq_zero {f g : ℝ[X]}
    (hfdeg : f.natDegree = 0) (hgdeg : g.natDegree = 0)
    (hfpos : 0 < f.leadingCoeff) (hgpos : 0 < g.leadingCoeff) :
    StrictInterl f g := by
  have hf0 : 0 < f.coeff 0 := by
    simpa only [leadingCoeff, hfdeg] using hfpos
  have hg0 : 0 < g.coeff 0 := by
    simpa only [leadingCoeff, hgdeg] using hgpos
  rw [Polynomial.eq_C_of_natDegree_eq_zero hfdeg,
    Polynomial.eq_C_of_natDegree_eq_zero hgdeg]
  simpa only [mul_one] using
    ((StrictInterl.refl (f := (1 : ℝ[X])) one_ne_zero (Polynomial.Splits.C _)).C_mul_left
      hf0.ne').C_mul_right hg0.ne'

/-- Prove consecutive interlacing by transferring a half-growth auxiliary
sequence through the `f`-polynomial transform. -/
def fTransformInterlacesGoal : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let some d ← fTransform? P | throwError "rr_row: the recurrence is not an f-transform"
  let t ← Term.exprToSyntax (← mainRowIndex (mkIdent P))
  let nm ← freshAuxName "fAuxInterlaces"
  let Q := mkIdent nm
  let n := mkIdent `n
  let N ← `(($n : ℝ))
  let aT ← rationalXPolyTerm d.a d.den N
  let bT ← rationalXPolyTerm d.b d.den N
  let degreeT ← if d.degreeShift == 0 then `(($n : ℕ) / 2)
    else if d.degreeShift == 1 then `((($n : ℕ) + 1) / 2)
    else `(($n : ℕ) - 1)
  let multiplierTac ← if d.degreeShift == 0 then
      `(tactic| rr_f_transform_floor_half_multiplier)
    else if d.degreeShift == 1 then `(tactic| rr_f_transform_half_multiplier)
    else `(tactic| rr_f_transform_pred_multiplier)
  elabAuxCommand (← `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
    | 0 => $(← qpolyTerm d.base)
    | $n:ident + 1 => $aT * ($Q $n).derivative + $bT * $Q $n))
  let shiftedName ← freshAuxName "fAuxInterlacesShift"
  let S := mkIdent shiftedName
  let shiftedInterlacesName ← freshAuxName "fAuxInterlacesShiftInterlaces"
  let shiftedInterlaces := mkIdent shiftedInterlacesName
  if d.degreeShift == 2 then
    let j := mkIdent `j
    let J ← `((($j : ℝ) + 1))
    let aS ← rationalXPolyTerm d.a d.den J
    let bS ← rationalXPolyTerm d.b d.den J
    elabAuxCommand (← `(command|
      noncomputable def $(mkIdent (`_root_ ++ shiftedName)) : ℕ → ℝ[X]
        | 0 => $(← qpolyTerm d.shiftedBase)
        | $j:ident + 1 => $aS * ($S $j).derivative + $bS * $S $j))
    let some movingTacRaw := (Parser.runParserCategory (← getEnv) `tactic
        "rr_row_interlaces (thm := \
          RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div)").toOption
      | throwError "rr_row: failed to parse the moving-upper auxiliary tactic"
    let movingTac : TSyntax `tactic := ⟨movingTacRaw⟩
    elabAuxCommand (← `(command|
      theorem $(mkIdent (`_root_ ++ shiftedInterlacesName)) ($j:ident : ℕ) :
          Interlaces ($S $j) ($S ($j + 1)) := by
        $movingTac:tactic))
  let Pi := mkIdent P
  let eqn := mkIdent d.L.eqn
  let link := mkIdent `hlink_f_interlaces
  let qdeg := mkIdent `hqdeg_f_interlaces
  let qpos := mkIdent `hqpos_f_interlaces
  let qnn := mkIdent `hqnn_f_interlaces
  let qsplits := mkIdent `hqsplits_f_interlaces
  let qinterl := mkIdent `hqinterl_f_interlaces
  let shiftLink := mkIdent `hshift_f_interlaces
  let identity ← if d.den.size == 1 && d.den[0]! == 1 then
      `(tactic| first
        | (simp only [RealRooted.fPolynomial_two, RealRooted.fPolynomial_one,
            Polynomial.coeff_add, Polynomial.coeff_C_mul,
            Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
            Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X]
           norm_num [map_ofNat]
           ring)
        | rr_cf_identity)
    else `(tactic| (
      simp only [RealRooted.fPolynomial_two, RealRooted.fPolynomial_one,
        Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X]
      norm_num [map_ofNat]
      rr_cf_identity))
  withMainContext do
  evalTactic (← `(tactic|
    have $link:ident :=
      RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero
      (P := $Pi) (Q := $Q) (a := fun $n:ident : ℕ => $aT)
      (b := fun $n:ident : ℕ => $bT)
      (ha := fun $n:ident => by compute_degree) (hb := fun $n:ident => by compute_degree)
      (hQ := fun $n:ident => by rw [$Q:ident])
      (h0deg := by simp [$Q:ident])
      (hP := fun $n:ident => by rw [$eqn:ident $n:ident]; $identity:tactic)
      (h0 := by simp [$Pi:ident, $Q:ident, RealRooted.fPolynomial, map_ofNat])))
  withMainContext do
  evalTactic (← `(tactic|
    have $qdeg:ident : ∀ $n:ident, ($Q $n).natDegree = $degreeT := fun $n => by
      rr_row_natDegree))
  withMainContext do
  evalTactic (← `(tactic|
    have $qpos:ident : ∀ j, 0 < ($Q j).leadingCoeff := fun j => by
      rr_row_leadingCoeff_pos))
  withMainContext do
  evalTactic (← `(tactic|
    have $qnn:ident : ∀ j, HasNonnegCoeffs ($Q j) := by
      refine RealRooted.derivativeRecurrence_hasNonnegCoeffs_of_mult_le
        (P := $Q) (A := fun $n:ident : ℕ => $aT) (B := fun $n:ident : ℕ => $bT)
        (D := fun $n:ident => $degreeT) ?_ ?_ ?_ ?_ ?_
      · intro j
        rw [$Q:ident]
      · intro j
        rw [$qdeg:ident]
      · intro j
        first
          | (norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul,
              Polynomial.coeff_X_pow, Polynomial.coeff_X,
              Polynomial.coeff_C] <;>
              first | done | positivity | nlinarith | rr_row_field)
          | rr_row_field
      · $multiplierTac:tactic
      · rw [$Q:ident]
        exact RealRooted.hasNonnegCoeffs_C (by positivity)))
  if d.degreeShift == 0 then
    withMainContext do
    evalTactic (← `(tactic|
      have $qinterl:ident : ∀ j, StrictInterl ($Q j) ($Q (j + 1)) :=
        derivativeRecurrence_strictInterl_of_floor_half_degree
          (Q := $Q) (A := fun $n:ident : ℕ => $aT) (B := fun $n:ident : ℕ => $bT)
          (fun j => by rw [$Q:ident]) $qdeg $qpos $qnn (by
            intro j r hr
            simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X, Polynomial.eval_pow]
            first | nlinarith [sq_nonneg r] | rr_row_field)))
  else if d.degreeShift == 1 then
    withMainContext do
    evalTactic (← `(tactic|
      have $qinterl:ident : ∀ j, StrictInterl ($Q j) ($Q (j + 1)) :=
        derivativeRecurrence_strictInterl_of_half_degree
          (Q := $Q) (A := fun $n:ident : ℕ => $aT) (B := fun $n:ident : ℕ => $bT)
          (fun j => by rw [$Q:ident]) $qdeg $qpos $qnn (by
            intro j r hr
            simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X, Polynomial.eval_pow]
            first | nlinarith [sq_nonneg r] | rr_row_field)))
  else
    withMainContext do
    evalTactic (← `(tactic|
      have $shiftLink:ident : ∀ j, $S j = $Q (j + 1) := by
        intro j
        induction j with
        | zero =>
            rw [$S:ident, $Q:ident, $Q:ident]
            norm_num [Polynomial.derivative_one]
            rr_poly_identity
        | succ j ih =>
            rw [$S:ident, $Q:ident, ih]
            norm_num [Nat.cast_add, Nat.cast_one]))
    withMainContext do
    evalTactic (← `(tactic|
      have $qinterl:ident : ∀ j, StrictInterl ($Q j) ($Q (j + 1)) :=
        fun j => by
          rcases j with _ | j
          · exact strictInterl_of_natDegree_eq_zero ($qdeg 0) ($qdeg 1)
              ($qpos 0) ($qpos 1)
          · rw [← $shiftLink j, ← $shiftLink (j + 1)]
            exact ($shiftedInterlaces j).toStrictInterl))
  withMainContext do
  evalTactic (← `(tactic|
    have $qsplits:ident : ∀ j, ($Q j).Splits := by
      intro j
      rcases j with _ | j
      · rw [$Q:ident]
        exact Polynomial.Splits.C (R := ℝ) _
      · exact ($qinterl j).2.1.2))
  withMainContext do
  evalTactic (← `(tactic|
    rw [$link $t, $link ($t + 1)]))
  if d.degreeShift == 0 then
    withMainContext do
    evalTactic (← `(tactic|
      exact interlaces_fPolynomial_sequence_floor $Q $qnn
        (fun j => Polynomial.leadingCoeff_ne_zero.mp ($qpos j).ne') $qsplits $qdeg
        $qinterl $t))
  else if d.degreeShift == 1 then
    withMainContext do
    evalTactic (← `(tactic|
      exact interlaces_fPolynomial_sequence $Q $qnn
        (fun j => Polynomial.leadingCoeff_ne_zero.mp ($qpos j).ne') $qsplits $qdeg
        $qinterl $t))
  else
    withMainContext do
    evalTactic (← `(tactic|
      exact interlaces_fPolynomial_sequence_pred $Q $qnn
        (fun j => Polynomial.leadingCoeff_ne_zero.mp ($qpos j).ne') $qsplits $qdeg
        $qinterl $t))

end RealRooted.Tactic
