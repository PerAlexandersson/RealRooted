module

public import RealRooted.DerivativeRecurrence.FiniteLagCoefficients
public import RealRooted.Tactic.SideGoals
public import RealRooted.Tactic.Recurrence.RowSide

/-!
# Coefficient positivity from finite-lag differential recurrences

Pair the derivative and multiplication summands at each lag, then propagate
nonnegative coefficients together with an affine degree envelope. Rational probes
choose the envelope only; every degree and sign obligation is proved symbolically.
-/

public meta section

open Lean Elab Tactic Meta Polynomial

namespace RealRooted.Tactic

/-- Select an affine degree envelope from exact samples of the multipliers and base rows.
The returned numbers are candidates; the generated theorem application checks all indices. -/
private def coefficientEnvelope (L : LinRecData) : MetaM (Nat × Nat) := do
  let mut d := 0
  for (j, i, c) in L.sampleTerms do
    for n in [0:3] do
      let some a ← evalCoeffAt? c n | throwError "cannot sample a recurrence multiplier"
      let gap := L.offset - j
      d := max d ((a.natDegree - i + gap - 1) / gap)
  let some base ← linRecBaseRowsOf? L | throwError "cannot sample initial rows"
  let mut D := 0
  for j in [0:base.size] do
    D := max D (base[j]!.natDegree - d * j)
  return (D, d)

/-- Group all multiplier expressions of derivative order `order` by their row lag. -/
private def pairedCoefficients (L : LinRecData) (order : Nat) : TacticM Term := do
  let n := mkIdent `rr_n
  let j := mkIdent `rr_j
  let mut body : Term ← `(0)
  for lag in (List.range L.offset).reverse do
    let mut summand : Term ← `(0)
    for (l, i, c) in L.terms do
      if l == lag && i == order then
        let c ← certTerm c
        summand ← `($summand + ($c) $n)
    body ← `(if $j = $(rowNumLit lag) then $summand else $body)
  `(fun ($n : ℕ) ($j : ℕ) => ($body : ℝ[X]))

/-- Discharge the coefficient-multiplier inequalities after splitting the finite lags.
Natural-number bounds are retained over the reals for linear and polynomial arithmetic. -/
elab (name := rrRowCoefficientMultipliers) "rr_row_coefficient_multipliers" : tactic => do
  evalTactic (← `(tactic| (
    intro n j hj i r hr
    have hr' := (Nat.cast_le (α := ℝ)).mpr hr
    interval_cases j <;>
      simp only [ite_true, ite_false, Nat.reduceEqDiff, zero_add, add_zero,
        Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one,
        Polynomial.coeff_zero, Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_ofNat,
        Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ] <;>
      norm_num <;>
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
        Nat.cast_one, zero_add, one_mul] at hr' <;>
      split_ifs <;> first | positivity | (exfalso; lia) | nlinarith)))

/-- Prove positive leading coefficient by propagating nonnegative coefficients within a
certified affine degree envelope. This route requires a nonzero-row premise. -/
def coefficientRowLeadingCoeff : TacticM Cert := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some f ← findPolySeqApp? tgt | throwError "no polynomial family in the goal"
  let some L ← linRec? f.name f.params | throwError "no linear recurrence"
  unless L.offset > 0 && L.terms.all (fun t => t.2.1 ≤ 1) do
    throwError "expected a finite-lag recurrence with at most first derivatives"
  let (D, d) ← coefficientEnvelope L
  let P ← certTerm (mkAppN (← mkConstWithFreshMVarLevels f.name) f.params)
  let eqn ← certTerm (mkAppN (← mkConstWithFreshMVarLevels L.eqn) f.params)
  let A ← pairedCoefficients L 1
  let B ← pairedCoefficients L 0
  let degree ← `(fun n : ℕ => $(rowNumLit D) + $(rowNumLit d) * n)
  let recProof ← `(by
    intro n
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [$eqn:term]
    rr_row_unfold
    norm_num
    ring1)
  let bounds ← `(by
    intro n j hj
    interval_cases j <;> norm_num <;> compute_degree!)
  let constant ← `(by
    intro n j hj
    interval_cases j <;> norm_num <;> positivity)
  let multipliers ← `(by rr_row_coefficient_multipliers)
  let base ← `(by
    intro j hj
    interval_cases j <;> constructor <;>
      simp only [$(mkIdent f.name):ident] <;>
      rr_row_unfold <;> first | compute_degree! | rr_nonneg_coeffs)
  let cert ← `(tactic|
    exact ((RealRooted.LinRec.natDegree_le_and_hasNonnegCoeffs
      (P := $P) (k := $(rowNumLit L.offset)) (D := $degree) (A := $A) (B := $B)
      $recProof (by intro n j hj; lia) $bounds $bounds $constant $multipliers
      $base _).2).pos_leadingCoeff (by assumption))
  evalTactic cert
  return #[cert]

end RealRooted.Tactic
