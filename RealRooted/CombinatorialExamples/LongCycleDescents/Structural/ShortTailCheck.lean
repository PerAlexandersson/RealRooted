/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortKernelBounds
public meta import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortCoefficients
public meta import RealRooted.IntervalDifferential.EulerCoefficientTable
public meta import Lean.Elab.Tactic
public import RealRooted.Mathlib.Data.Array.GetD
import Mathlib.Tactic

/-!
# Exact low-cutoff tail certificates

We recompute the difference coefficients through rank 31 and the short-kernel
norms through rank 64. The only remaining input is a geometric tail majorant.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- Integer numerator of the geometric kernel tail, at denominator `5^64`. -/
def shortKernelTailNumerator (k : ℕ) : ℤ :=
  ∑ j ∈ range (k - 1), ∑ d ∈ (j + 1).divisors,
    (4 : ℤ) ^ (65 - (j + 1) / d) * 5 ^ ((j + 1) / d)

/-- Integer coefficients of the rank-31 anchor, from the difference table. -/
def shortAnchorNumerator (H : ℕ) (rows : Array (Array ℤ)) (h : ℕ) : ℤ :=
  ∑ n ∈ range (H + 1), ((H.factorial / n.factorial : ℕ) : ℤ) *
    (rows.getD n #[]).getD h 0

/-- Integer numerator of the anchor's coefficient margin. -/
def shortMarginNumerator (H : ℕ) (rows : Array (Array ℤ)) : ℤ :=
  shortAnchorNumerator H rows 0 * (5 : ℤ) ^ H -
    ∑ h ∈ Ico 1 (H + 1), |shortAnchorNumerator H rows h| * 4 ^ h * 5 ^ (H - h)

/-- Integer numerator of a short-kernel norm; only its possible exponents are visited. -/
def shortKernelNormNumerator (k i : ℕ) : ℤ :=
  ∑ q ∈ Icc 1 (min i (k - 1)),
    |shortKernelCell k i (i - q)| * (4 : ℤ) ^ (i - q) * 5 ^ (64 - (i - q))

/-- Integer numerator of the exact finite kernel tail plus its geometric budget. -/
def shortTailNumerator (k l : ℕ) : ℤ :=
  (∑ i ∈ Ico l 65, shortKernelNormNumerator k i) + shortKernelTailNumerator k

/-- Check the finite anchor against the subsequent tail, using integer arithmetic only. -/
def shortTailCertificate (k H : ℕ) : Bool :=
  let rows := shortCoefficientTable k H
  decide (shortTailNumerator k 1 < (H + 1 : ℕ) * (5 : ℤ) ^ 64 ∧
    (∑ j ∈ range (H + 1), ((H.factorial / j.factorial : ℕ) : ℤ) *
      arrayNormNumerator H (rows.getD j #[]) * shortTailNumerator k (H + 1 - j)) <
      ((H + 1 : ℕ) * (5 : ℤ) ^ 64 - shortTailNumerator k 1) * shortMarginNumerator H rows)

/-- Check every coefficient margin between rank eighteen and the anchor. -/
def shortPrefixCertificate (k H : ℕ) : Bool :=
  let rows := shortCoefficientTable k H
  (List.range (H + 1)).all (fun n => if 18 ≤ n then
    decide (0 < shortMarginNumerator n rows) else true)

/-- The tail numerator satisfies a one-step backward recurrence. -/
theorem shortTailNumerator_eq_add (k : ℕ) {l : ℕ} (hl : l < 65) :
    shortTailNumerator k l = shortKernelNormNumerator k l + shortTailNumerator k (l + 1) := by
  simp only [shortTailNumerator]
  rw [sum_eq_sum_Ico_succ_bot hl]
  ring

meta section

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

/-- Propose the entire bounded table once; scalar recurrences verify every entry. -/
elab "short_table_candidate" k:num H:num : term => do
  let count := quote (H.getNat + 1)
  let e ← Term.elabTerm (← `(eulerCoefficientTable $H (shortKernelSupport $k)
    (fun i h => -shortKernelCell $k i h) $count)) none
  let ty ← Term.elabTerm (← `(Array (Array Int))) none
  let value ← unsafe evalExpr (Array (Array Int)) ty e
  return toExpr value

/-- Copy a proposed row to an independent literal, keeping kernel lookups short. -/
elab "short_proposed_row" proposal:ident n:num : term => do
  let e ← Term.elabTerm (← `(($proposal : Array (Array Int)).getD $n #[])) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← Term.elabTerm (← `(Array Int)) none
  let value ← unsafe evalExpr (Array Int) ty e
  return toExpr value

/-- Check each scalar recurrence with references to previously checked constants,
rather than repeating their large integer literals in every proof branch. -/
elab "check_short_row" k:num H:num n:num "from" old:term "using" row:term : tactic => do
  let mut entries ← `(tactic| exact fun i => Fin.elim0 i)
  for _ in [:H.getNat + 1] do
    entries ← `(tactic| exact Fin.cases (by decide +kernel) (by $entries:tactic))
  evalTactic (← `(tactic| change eulerTableStep $H (shortKernelSupport $k)
    (fun i h => -shortKernelCell $k i h) $n $old = $row))
  evalTactic (← `(tactic| unfold eulerTableStep))
  evalTactic (← `(tactic| apply Array.ofFn_eq_of_getD (d := 0)))
  evalTactic (← `(tactic| decide +kernel))
  evalTactic entries

/-- Cache kernel-checked scalar tails before checking the final integer inequality. -/
elab "check_short_tail" k:num H:num "from" rows:term : tactic => do
  evalTactic (← `(tactic| unfold shortTailCertificate shortCoefficientTable))
  evalTactic (← `(tactic| rw [$rows:term]))
  let count := H.getNat + 1
  let ty ← Term.elabTerm (← `(Int)) none
  let candidate (l : Nat) := do
    let ln := quote l
    let e ← Term.elabTerm (← `(shortTailNumerator $k $ln)) none
    let value ← unsafe evalExpr Int ty e
    Term.exprToSyntax (toExpr value)
  let mut previous := mkIdent (← mkFreshUserName `tail)
  let start := quote (count + 1)
  let literal ← candidate (count + 1)
  evalTactic (← `(tactic| have $previous : shortTailNumerator $k $start = ($literal : Int) := by
    decide +kernel))
  let mut facts : Array Ident := #[]
  for offset in [:count] do
    let l := count - offset
    let ln := quote l
    let literal ← candidate l
    let current := mkIdent (← mkFreshUserName `tail)
    evalTactic (← `(tactic| have $current : shortTailNumerator $k $ln = ($literal : Int) := by
      rw [shortTailNumerator_eq_add $k (by decide), $previous:term]
      decide +kernel))
    previous := current
    facts := facts.push current
  evalTactic (← `(tactic| simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]))
  for fact in facts do
    evalTactic (← `(tactic| simp only [$fact:term]))
  evalTactic (← `(tactic| decide +kernel))

/-- Verify the earlier scalar margins using the already checked coefficient table. -/
elab "check_short_prefix" k:num H:num "from" rows:term : tactic => do
  evalTactic (← `(tactic| change shortPrefixCertificate $k $H = true))
  evalTactic (← `(tactic| unfold shortPrefixCertificate shortCoefficientTable))
  evalTactic (← `(tactic| rw [$rows:term]))
  evalTactic (← `(tactic| decide +kernel))

/-- Generate small kernel-checked transitions, then the tail and prefix inequalities.
Native evaluation proposes integers only; every recurrence is kernel-checked. -/
macro "certify_short_cutoff" result:ident k:num H:num : command => do
  let mut commands : Array Syntax := #[]
  let proposal := mkIdent (result.getId.appendAfter "_proposal")
  commands := commands.push (← `(command| private def $proposal : Array (Array Int) :=
    short_table_candidate $k $H))
  let mut data := mkIdent (result.getId.appendAfter "_data0")
  commands := commands.push (← `(command| private def $data : Array (Array Int) := #[]))
  let initial := mkIdent (result.getId.appendAfter "_row0")
  commands := commands.push (← `(command| private theorem $initial :
    eulerCoefficientTable $H (shortKernelSupport $k)
      (fun i h => -shortKernelCell $k i h) 0 = $data := rfl))
  let mut previous ← `($initial:ident)
  let mut rowNames : Array (TSyntax `term) := #[]
  for n in [:H.getNat + 1] do
    let index := Syntax.mkNumLit (toString n)
    let next := Syntax.mkNumLit (toString (n + 1))
    let row := mkIdent (result.getId.appendAfter s!"_dataRow{n}")
    let rowProof := mkIdent (result.getId.appendAfter s!"_step{n}")
    let nextData := mkIdent (result.getId.appendAfter s!"_data{n + 1}")
    let name := mkIdent (result.getId.appendAfter s!"_row{n + 1}")
    commands := commands.push (← `(command| private def $row : Array Int :=
      short_proposed_row $proposal $index))
    commands := commands.push (← `(command| private theorem $rowProof :
      eulerTableStep $H (shortKernelSupport $k) (fun i h => -shortKernelCell $k i h)
        $index $data = $row := by
      check_short_row $k $H $index from $data using $row))
    rowNames := rowNames.push (← `($row:ident))
    commands := commands.push (← `(command| private def $nextData : Array (Array Int) :=
      #[$rowNames,*]))
    commands := commands.push (← `(command| private theorem $name :
      eulerCoefficientTable $H (shortKernelSupport $k)
        (fun i h => -shortKernelCell $k i h) $next = $nextData := by
      rw [eulerCoefficientTable, $previous:term, $rowProof:term]
      rfl))
    data := nextData
    previous ← `($name:ident)
  commands := commands.push (← `(command|
    /-- The exact finite anchor bounds the entire subsequent coefficient tail. -/
    private theorem $result : shortTailCertificate $k $H = true := by
      check_short_tail $k $H from $previous))
  let prefixName := mkIdent (result.getId.appendAfter "_prefix")
  commands := commands.push (← `(command|
    /-- Every earlier margin from rank eighteen to the anchor is strictly positive. -/
    private theorem $prefixName : shortPrefixCertificate $k $H = true := by
      check_short_prefix $k $H from $previous))
  return ⟨mkNullNode commands⟩

end

end RealRooted.LongCycleDescents.Structural
