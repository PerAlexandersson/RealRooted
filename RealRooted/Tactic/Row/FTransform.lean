import RealRooted.SymmetricDecomposition.FPolynomialSequence
import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
import RealRooted.Tactic.Row.Support

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

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- The inverse transform in the degree box `d`: `(1 - t)^d p (t / (1 - t))`. -/
def QPoly.invF (d : Nat) (p : QPoly) : QPoly := Id.run do
  let oneMinus : QPoly := QPoly.const 1 - QPoly.X
  let mut acc : QPoly := QPoly.const 0
  for j in [0:d + 1] do
    acc := acc + QPoly.smul (p.coeff j) (QPoly.pow QPoly.X j * QPoly.pow oneMinus (d - j))
  return acc

/-- The transformed recurrence: the base row and the multipliers `a`, `b` fitted as polynomials
in `n`. -/
structure FTransData where
  L : LinRecData
  base : QPoly
  a : Array (Array Rat)
  b : Array (Array Rat)

/-- Read `Q (n + 1) = a n Q n' + b n Q n` off a first-order derivative recurrence
`P (n + 1) = A n P n' + B n P n` with `P 0` constant, `X + 1 ∣ A n`; the transformed rows must
have real roots on the computed range. -/
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
  let mut q := r0
  for n in [0:10] do
    unless q.natDegree == 0 || q.realRooted do return none
    q := as[n]! * q.derivative + bs[n]! * q
  let (some a, some b) := (fitXPoly? as, fitXPoly? bs) | return none
  return some { L, base := r0, a, b }

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
  let aT ← xPolyTerm d.a N
  let bT ← xPolyTerm d.b N
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

elab_rules : tactic
  | `(tactic| rr_f_transform_half_multiplier) => halfMultiplierGoal 0 1

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
  let aT ← xPolyTerm d.a N
  let bT ← xPolyTerm d.b N
  elabAuxCommand (← `(command| noncomputable def $(mkIdent (`_root_ ++ nm)) : ℕ → ℝ[X]
    | 0 => $(← qpolyTerm d.base)
    | $n:ident + 1 => $aT * ($Q $n).derivative + $bT * $Q $n))
  let Pi := mkIdent P
  let eqn := mkIdent d.L.eqn
  let link := mkIdent `hlink_f_interlaces
  let qdeg := mkIdent `hqdeg_f_interlaces
  let qpos := mkIdent `hqpos_f_interlaces
  let qnn := mkIdent `hqnn_f_interlaces
  let qsplits := mkIdent `hqsplits_f_interlaces
  let qinterl := mkIdent `hqinterl_f_interlaces
  let identity ← `(tactic| first
    | (simp only [RealRooted.fPolynomial_two, RealRooted.fPolynomial_one,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X]
       norm_num [map_ofNat]
       ring)
    | rr_cf_identity)
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
    have $qdeg:ident : ∀ j, ($Q j).natDegree = (j + 1) / 2 := fun j => by
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
        (D := fun j => (j + 1) / 2) ?_ ?_ ?_ ?_ ?_
      · intro j
        rw [$Q:ident]
      · intro j
        rw [$qdeg:ident]
      · intro j
        norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      · rr_f_transform_half_multiplier
      · rw [$Q:ident]
        exact RealRooted.hasNonnegCoeffs_C (by positivity)))
  withMainContext do
  evalTactic (← `(tactic|
    have $qinterl:ident : ∀ j, StrictInterl ($Q j) ($Q (j + 1)) :=
      derivativeRecurrence_strictInterl_of_half_degree
        (Q := $Q) (A := fun $n:ident : ℕ => $aT) (B := fun $n:ident : ℕ => $bT)
        (fun j => by rw [$Q:ident]) $qdeg $qpos $qnn (by
          intro j r hr
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_pow]
          nlinarith [sq_nonneg r])))
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
  withMainContext do
  evalTactic (← `(tactic|
    exact interlaces_fPolynomial_sequence $Q $qnn
      (fun j => Polynomial.leadingCoeff_ne_zero.mp ($qpos j).ne') $qsplits $qdeg
      $qinterl $t))

end RealRooted.Tactic
