/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public meta import Lean.Elab.Tactic
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.MixtureTransfer
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortKernel
public meta import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortKernel
import RealRooted.IntervalDifferential.ConvolutionBounds
public import RealRooted.IntervalDifferential.EulerRecurrence
public meta import RealRooted.IntervalDifferential.EulerRecurrence
import RealRooted.Mathlib.Data.Array.GetD
import Mathlib.Tactic

/-!
# Uniform bounds from short-cutoff certificates

Denominator-cleared integer checks certify the anchor, prefix margins, and kernel
tails. The finite anchor bounds every later row through the Euler tail estimate.
Together with the long-cutoff estimate, this covers all ranks from eighteen.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

public noncomputable section

open Finset

@[expose] section

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

end

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

/-- The same finite table computes every earlier anchor exactly. -/
theorem shortAnchorNumerator_eq_of_le (k H n : ℕ) (hn : n ≤ H) {h : ℕ} (hh : h ≤ n) :
    (shortAnchorNumerator n (shortCoefficientTable k H) h : ℚ) =
      (n.factorial : ℚ) * (lossRow k n).coeff h := by
  rw [shortAnchorNumerator, lossRow_eq_sum_differenceRow, finsetSum_coeff]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [shortCoefficientTable_correct k H (hjn.trans hn) (hh.trans hn)]
  have hf : ((n.factorial / j.factorial : ℕ) : ℚ) * j.factorial = n.factorial := by
    exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hjn)
  linear_combination (differenceRow k j).coeff h * hf

/-- The computed anchor coefficients are factorial-scaled genuine alphabet coefficients. -/
theorem shortAnchorNumerator_eq (k H : ℕ) {h : ℕ} (hh : h ≤ H) :
    (shortAnchorNumerator H (shortCoefficientTable k H) h : ℚ) =
      (H.factorial : ℚ) * (lossRow k H).coeff h :=
  shortAnchorNumerator_eq_of_le k H H le_rfl hh

private theorem norm_nonconstant_lossRow (k H : ℕ) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0)) =
      ∑ h ∈ Ico 1 (H + 1), |(lossRow k H).coeff h| * (4 / 5 : ℚ) ^ h := by
  have hs : (lossRow k H).support ⊆ range (H + 1) := by
    intro h hh
    exact mem_range.mpr (Nat.lt_succ_of_le
      ((le_natDegree_of_mem_supp h hh).trans (natDegree_lossRow_le k H)))
  have he := coefficientNorm_eq_abs_constant_add (4 / 5 : ℚ) (lossRow k H)
  rw [coefficientNorm_eq_sum hs,
    ← sum_range_add_sum_Ico (fun h => |(lossRow k H).coeff h| * (4 / 5 : ℚ) ^ h)
      (by lia : 1 ≤ H + 1)] at he
  simp only [sum_range_one, pow_zero, mul_one] at he
  exact (add_left_cancel he).symm

/-- A finite table computes every earlier rational coefficient margin. -/
theorem shortMarginNumerator_eq_of_le (k H n : ℕ) (hn : n ≤ H) :
    (shortMarginNumerator n (shortCoefficientTable k H) : ℚ) =
      (n.factorial : ℚ) * 5 ^ n * ((lossRow k n).coeff 0 -
        coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0))) := by
  rw [shortMarginNumerator, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    shortAnchorNumerator_eq_of_le k H n hn (Nat.zero_le n),
    sum_abs_mul_pow_eq n (Ico 1 (n + 1)) (fun h hh => by have := mem_Ico.mp hh; lia)]
  have he : (∑ h ∈ Ico 1 (n + 1),
      |(shortAnchorNumerator n (shortCoefficientTable k H) h : ℚ)| * (4 / 5 : ℚ) ^ h) =
      (n.factorial : ℚ) * ∑ h ∈ Ico 1 (n + 1),
        |(lossRow k n).coeff h| * (4 / 5 : ℚ) ^ h := by
    rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    rw [shortAnchorNumerator_eq_of_le k H n hn (by have := mem_Ico.mp hh; lia), abs_mul,
      abs_of_nonneg (Nat.cast_nonneg n.factorial)]
    ring
  rw [he, ← norm_nonconstant_lossRow]
  ring

/-- The integer anchor margin is its exact rational coefficient margin. -/
theorem shortMarginNumerator_eq (k H : ℕ) :
    (shortMarginNumerator H (shortCoefficientTable k H) : ℚ) =
      (H.factorial : ℚ) * 5 ^ H * ((lossRow k H).coeff 0 -
        coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0))) :=
  shortMarginNumerator_eq_of_le k H H le_rfl

/-- Prefix margins from the same table cover the ranks before its tail anchor. -/
theorem coefficientNorm_lt_of_shortPrefixCertificate {k H n : ℕ}
    (hn : 18 ≤ n) (hH : n ≤ H) (hc : shortPrefixCertificate k H = true) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  dsimp only [shortPrefixCertificate] at hc
  have hh : 0 < shortMarginNumerator n (shortCoefficientTable k H) := by
    have he := List.all_eq_true.mp hc n (List.mem_range.mpr (by lia))
    simpa only [ite_eq_left hn, decide_eq_true_eq] using he
  have hpos : (0 : ℚ) < shortMarginNumerator n (shortCoefficientTable k H) := by
    exact_mod_cast hh
  rw [shortMarginNumerator_eq_of_le k H n hH] at hpos
  have hfac : (0 : ℚ) < (n.factorial : ℚ) * 5 ^ n := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hfac).mp hpos)

/-- The sparse integer kernel norm has denominator exactly `5^64`. -/
theorem shortKernelNormNumerator_eq (k : ℕ) {i : ℕ} (hi : i ≤ 64) :
    (shortKernelNormNumerator k i : ℚ) = (5 : ℚ) ^ 64 * shortKernelNorm k i := by
  have he := sum_shortKernelCell_reflect k i
    (fun h => |shortKernelCell k i h| * (4 : ℤ) ^ h * 5 ^ (64 - h))
    (fun h hz => by rw [hz]; simp)
  rw [shortKernelNormNumerator, ← he,
    sum_abs_mul_pow_eq 64 (range (i + 1)) (fun h hh => by have := mem_range.mp hh; lia)]
  rfl

/-- The integer geometric remainder has the same denominator. -/
theorem shortKernelTailNumerator_eq {k : ℕ} (hk : k ≤ 66) :
    (shortKernelTailNumerator k : ℚ) = (5 : ℚ) ^ 64 * shortKernelTail k := by
  have hc : (5 : ℚ) ^ 64 * (4 / 5) ^ 65 / (1 - 4 / 5) = 4 ^ 65 := by norm_num
  have hp {q : ℕ} (hq : q ≤ 65) : (4 : ℚ) ^ (65 - q) * 5 ^ q =
      (5 / 4 : ℚ) ^ q * ((5 : ℚ) ^ 64 * (4 / 5) ^ 65 / (1 - 4 / 5)) := by
    rw [hc, div_pow]
    have he : (4 : ℚ) ^ (65 - q) * 4 ^ q = 4 ^ 65 := by
      rw [← pow_add, Nat.sub_add_cancel hq]
    field_simp
    rw [← he]
  calc
    _ = ∑ j ∈ range (k - 1), ∑ d ∈ (j + 1).divisors,
        (5 / 4 : ℚ) ^ ((j + 1) / d) * ((5 : ℚ) ^ 64 * (4 / 5) ^ 65 / (1 - 4 / 5)) := by
      simp only [shortKernelTailNumerator, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro d _
      exact hp ((Nat.div_le_self _ _).trans (by have := mem_range.mp hj; lia))
    _ = _ := by
      simp only [shortKernelTail, shortKernelScale, div_eq_mul_inv, sum_mul, mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro d _
      ring

/-- Every integer tail numerator is the corresponding rational tail budget. -/
theorem shortTailNumerator_eq {k : ℕ} (hk : k ≤ 66) (l : ℕ) :
    (shortTailNumerator k l : ℚ) = (5 : ℚ) ^ 64 * shortTailBound k l := by
  rw [shortTailNumerator, Int.cast_add, Int.cast_sum, shortKernelTailNumerator_eq hk,
    shortTailBound, mul_add, mul_sum]
  congr 1
  exact sum_congr rfl (fun i hi => shortKernelNormNumerator_eq k
    (by have := mem_Ico.mp hi; lia))

/-- A successful integer check gives the exact rational anchor and tail inequalities. -/
theorem shortTailCertificate_sound {k H : ℕ} (hk : k ≤ 66)
    (hc : shortTailCertificate k H = true) :
    shortTailBound k 1 < (H + 1 : ℕ) ∧
      (∑ j ∈ range (H + 1), coefficientNorm (4 / 5 : ℚ) (differenceRow k j) *
        shortTailBound k (H + 1 - j)) <
      ((H + 1 : ℕ) - shortTailBound k 1) * ((lossRow k H).coeff 0 -
        coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0))) := by
  dsimp only [shortTailCertificate] at hc
  have hh := of_decide_eq_true hc
  have hB : (0 : ℚ) < 5 ^ 64 := by positivity
  have hA : (0 : ℚ) < (H.factorial : ℚ) * 5 ^ H := by positivity
  have h1 : (shortTailNumerator k 1 : ℚ) < ((H + 1 : ℕ) : ℚ) * 5 ^ 64 := by
    exact_mod_cast hh.1
  rw [shortTailNumerator_eq hk] at h1
  have h2 : ((∑ j ∈ range (H + 1), ((H.factorial / j.factorial : ℕ) : ℤ) *
      arrayNormNumerator H ((shortCoefficientTable k H).getD j #[]) *
        shortTailNumerator k (H + 1 - j) : ℤ) : ℚ) <
      (((H + 1 : ℕ) : ℚ) * 5 ^ 64 - (shortTailNumerator k 1 : ℚ)) *
        (shortMarginNumerator H (shortCoefficientTable k H) : ℚ) := by
    exact_mod_cast hh.2
  have hb : ((∑ j ∈ range (H + 1), ((H.factorial / j.factorial : ℕ) : ℤ) *
      arrayNormNumerator H ((shortCoefficientTable k H).getD j #[]) *
        shortTailNumerator k (H + 1 - j) : ℤ) : ℚ) =
      (H.factorial : ℚ) * 5 ^ H * 5 ^ 64 *
        ∑ j ∈ range (H + 1), coefficientNorm (4 / 5 : ℚ) (differenceRow k j) *
          shortTailBound k (H + 1 - j) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjH := Nat.le_of_lt_succ (mem_range.mp hj)
    rw [arrayNormNumerator_shortCoefficientTable hjH, shortTailNumerator_eq hk]
    have hf : ((H.factorial / j.factorial : ℕ) : ℚ) * j.factorial = H.factorial := by
      exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hjH)
    linear_combination (5 : ℚ) ^ H * 5 ^ 64 *
      coefficientNorm (4 / 5 : ℚ) (differenceRow k j) * shortTailBound k (H + 1 - j) * hf
  rw [hb, shortTailNumerator_eq hk, shortMarginNumerator_eq] at h2
  constructor
  · apply (mul_lt_mul_iff_right₀ hB).mp
    simpa only [mul_comm] using h1
  · apply (mul_lt_mul_iff_right₀ (mul_pos hA hB)).mp
    convert h2 using 1; ring

end RealRooted.LongCycleDescents.Structural

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

certify_short_cutoff checked3 3 18
certify_short_cutoff checked4 4 23
certify_short_cutoff checked5 5 24
certify_short_cutoff checked6 6 25
certify_short_cutoff checked7 7 25
certify_short_cutoff checked8 8 27
certify_short_cutoff checked9 9 27
certify_short_cutoff checked10 10 29
certify_short_cutoff checked11 11 29
certify_short_cutoff checked12 12 31

/-- Every short cutoff has both checked prefix margins and a tail anchor. -/
theorem exists_shortCertificates {k : ℕ} (hk : 3 ≤ k) (hk12 : k ≤ 12) :
    ∃ H ≤ 31, shortTailCertificate k H = true ∧ shortPrefixCertificate k H = true := by
  interval_cases k
  · exact ⟨18, by decide, checked3, checked3_prefix⟩
  · exact ⟨23, by decide, checked4, checked4_prefix⟩
  · exact ⟨24, by decide, checked5, checked5_prefix⟩
  · exact ⟨25, by decide, checked6, checked6_prefix⟩
  · exact ⟨25, by decide, checked7, checked7_prefix⟩
  · exact ⟨27, by decide, checked8, checked8_prefix⟩
  · exact ⟨27, by decide, checked9, checked9_prefix⟩
  · exact ⟨29, by decide, checked10, checked10_prefix⟩
  · exact ⟨29, by decide, checked11, checked11_prefix⟩
  · exact ⟨31, by decide, checked12, checked12_prefix⟩

/-- Every short cutoff has a checked anchor at rank at most thirty-one. -/
theorem exists_shortTailCertificate {k : ℕ} (hk : 3 ≤ k) (hk12 : k ≤ 12) :
    ∃ H ≤ 31, shortTailCertificate k H = true := by
  obtain ⟨H, hH, hc, _⟩ := exists_shortCertificates hk hk12
  exact ⟨H, hH, hc⟩

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- A finite tail check proves strict coefficient dominance at every subsequent rank. -/
theorem coefficientNorm_lt_of_shortTailCertificate {k H n : ℕ} (hk : k ≤ 66)
    (hH : H ≤ 64) (hn : H ≤ n) (hc : shortTailCertificate k H = true) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  have hchecked := shortTailCertificate_sound hk hc
  let e i := coefficientNorm (4 / 5 : ℚ) (differenceRow k i)
  have he i : 0 ≤ e i := coefficientNorm_nonneg (by norm_num) _
  have hrec (i : ℕ) (hi : i ≠ 0) : (i : ℚ) * e i ≤
      ∑ j ∈ range i, shortKernelNorm k (i - j) * e j := by
    have hh := coefficientNorm_eulerCoeff_equation (by norm_num : (0 : ℚ) ≤ 4 / 5)
      (-shortKernel k) hi
    simpa only [e, differenceRow, Pi.neg_apply, coefficientNorm_neg, shortKernelNorm_eq] using hh
  have htail := sum_euler_tail_bound (shortKernelNorm k) e (shortTailBound k) he hrec
    (by lia : 0 < H + 1) (by lia : H + 1 ≤ n + 1) (by
      intro l _ hl B
      exact sum_shortKernelNorm_le (by lia : l ≤ 65) k B)
  have hpos : (0 : ℚ) < ((H + 1 : ℕ) : ℚ) - shortTailBound k 1 :=
    sub_pos.mpr hchecked.1
  have hb : (∑ i ∈ Ico (H + 1) (n + 1), e i) < (lossRow k H).coeff 0 -
      coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0)) := by
    apply (mul_lt_mul_iff_right₀ hpos).mp
    convert htail.trans_lt hchecked.2 using 1
  let R := ∑ i ∈ Ico (H + 1) (n + 1), differenceRow k i
  have hR : coefficientNorm (4 / 5 : ℚ) R < (lossRow k H).coeff 0 -
      coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0)) :=
    (coefficientNorm_sum_le (by norm_num) _ _).trans_lt hb
  have hrow : lossRow k n = lossRow k H + R := by
    rw [lossRow_eq_sum_differenceRow k n, lossRow_eq_sum_differenceRow k H,
      ← sum_range_add_sum_Ico (differenceRow k) (by lia : H + 1 ≤ n + 1)]
  rw [hrow]
  exact coefficientNorm_add_sub_constant_lt (by norm_num) _ _ hR

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

/-- Every genuine long-cutoff alphabet is strictly coefficient-dominant from rank 18. -/
theorem coefficientNorm_lossRow_sub_constant_lt_of_rank {n k : ℕ}
    (hn : 18 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  by_cases h13 : 13 ≤ k
  · exact coefficientNorm_lossRow_sub_constant_lt h13 hkn
  · obtain ⟨H, hH, hc, hp⟩ := exists_shortCertificates hk (by lia)
    by_cases hHn : H ≤ n
    · exact coefficientNorm_lt_of_shortTailCertificate (by lia) (by lia) hHn hc
    · exact coefficientNorm_lt_of_shortPrefixCertificate hn (by lia) hp

/-- Coefficient dominance for every actual alphabet from rank 18. -/
theorem descentAlphabetPolynomial_coefficientNorm_lt_of_rank {n k : ℕ}
    (hn : 18 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) :
    coefficientNorm (4 / 5 : ℝ) (reflect n (descentAlphabetPolynomial n k) -
      C ((descentAlphabetPolynomial n k).coeff n)) <
      (descentAlphabetPolynomial n k).coeff n :=
  descentAlphabetPolynomial_coefficientNorm_lt_of_lossRow (by lia)
    (coefficientNorm_lossRow_sub_constant_lt_of_rank hn hk hkn)

/-- The strict `5/4` disk holds for every nonzero nonnegative alphabet mixture from rank 18. -/
theorem norm_root_sum_descentAlphabetPolynomial_lt_of_rank {n : ℕ} (hn : 18 ≤ n)
    {s : Finset ℕ} (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) {z : ℂ}
    (hz : (((∑ k ∈ s, C (w k) * descentAlphabetPolynomial n k).map
      (algebraMap ℝ ℂ)).eval z) = 0) : ‖z‖ < 5 / 4 :=
  norm_root_sum_descentAlphabetPolynomial_lt_of_dominance
    (fun k hk => descentAlphabetPolynomial_coefficientNorm_lt_of_rank hn
      (hs k hk).1 (hs k hk).2) hw hp hz

/-- All long-cutoff descent mixtures have simple nonpositive roots from rank 18. -/
theorem mixture_roots_of_rank {n : ℕ} (hn : 18 ≤ n) {s : Finset ℕ}
    (hs : ∀ k ∈ s, 3 ≤ k ∧ k ≤ n) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : ∃ k ∈ s, 0 < w k) :
    let p := ∑ k ∈ s, C (w k) * realDescentPolynomial n k
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = n - 2 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by lia⟩
  simpa only [show m + 3 - 2 = m + 1 by lia] using
    mixture_roots_of_coefficientNorm_lt (by lia : 15 ≤ m) hs
      (fun k hk => descentAlphabetPolynomial_coefficientNorm_lt_of_rank hn
        (hs k hk).1 (hs k hk).2) hw hp

/-- Every actual long-cutoff row has the structural simple-root conclusion from rank 18. -/
theorem realDescentPolynomial_roots_of_rank {n k : ℕ} (hn : 18 ≤ n)
    (hk : 3 ≤ k) (hkn : k ≤ n) :
    let p := realDescentPolynomial n k
    p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = n - 2 ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  simpa using mixture_roots_of_rank hn (s := {k}) (w := fun _ => 1)
    (by simpa using And.intro hk hkn) (by simp) (by simp)

end RealRooted.LongCycleDescents.Structural
