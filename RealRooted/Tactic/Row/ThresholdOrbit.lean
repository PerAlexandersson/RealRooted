module

public import RealRooted.ThresholdMatrix.Orbit
public meta import RealRooted.ThresholdMatrix.Orbit
public import RealRooted.Tactic.Row.Core
public meta import RealRooted.Tactic.Row.Core
public import RealRooted.Tactic.Recurrence.RowSide
public meta import RealRooted.Tactic.Recurrence.RowSide
public import RealRooted.Tactic.InterlacesExplicit
public meta import RealRooted.Tactic.InterlacesExplicit

/-!
# Row tactics: order-three recurrences as threshold-matrix orbits

A pure-lag recurrence `P (n + 3) = A₂ * P (n + 2) + A₁ * P (n + 1) + A₀ * P n` with constant
multipliers may be the scalar shadow of a vector recurrence `S (n + 1) = G * S n` with a
threshold matrix `G` (Haglund–Zhang markers `1, 1 + X`, or Gustafsson–Solus markers `0, 1`):
`P (m + t) = (S m).sum`.  The threshold-matrix theorems keep `S n` an interlacing sequence of
real-rooted polynomials, so every row of `P` is real-rooted.

`thresholdProbe?` searches, in exact rational arithmetic, the `3 × 3` threshold matrices of both
families, the inputs `S₀ ∈ {0, 1, X}³` and the offsets `t ≤ 4` for which the orbit sums reproduce
the computed rows.  `thresholdOrbitSplits` proves the identification by induction on three
consecutive rows (each step unfolds three matrix steps on `S m = [a, b, c]` and closes by
`ring`), checks the rows below `t` explicitly, and concludes with `splits_orbit_sum`.  This
covers A120987, A330509, A340620 (Haglund–Zhang) and A304429 (Gustafsson–Solus).
-/

public meta section

open Lean Elab Tactic Meta Polynomial

attribute [rr_threshold_unfold] RealRooted.HaglundZhang.orbit_succ
  RealRooted.GustafssonSolus.orbit_succ RealRooted.HaglundZhang.orbit
  RealRooted.GustafssonSolus.orbit RealRooted.matPolyAction RealRooted.HaglundZhang.matrix
  RealRooted.thresholdMatrix RealRooted.thresholdRow RealRooted.thresholdEntry List.range_succ
  List.range_zero List.map
  List.zipWith List.sum_cons List.sum_nil List.nil_append List.cons_append
  List.singleton_append Nat.zero_add ite_true ite_false RealRooted.Interl

namespace RealRooted.Tactic

/-- The two threshold-matrix families. -/
private inductive ThrFamily where
  | haglundZhang
  | gustafssonSolus
  deriving BEq

/-- A threshold-orbit certificate: family, rows `(threshold, marker)` with markers coded as
`0 ↦ 0`, `1 ↦ 1`, `2 ↦ 1 + X`, input `S₀` coded as `0 ↦ 0`, `1 ↦ 1`, `2 ↦ X`, and offset. -/
private structure ThrPlan where
  fam : ThrFamily
  rows : Array (Nat × Nat)
  input : Array Nat
  offset : Nat

private def thrMarker (c : Nat) : QPoly :=
  match c with
  | 0 => QPoly.const 0
  | 1 => QPoly.const 1
  | _ => QPoly.const 1 + QPoly.X

private def thrInput (c : Nat) : QPoly :=
  match c with
  | 0 => QPoly.const 0
  | 1 => QPoly.const 1
  | _ => QPoly.X

/-- The entry of the threshold row `(t, α)` in column `j`. -/
private def thrEntry (t : Nat) (α : QPoly) (j : Nat) : QPoly :=
  if j < t then QPoly.X else if j == t then α else QPoly.const 1

/-- All row lists of length three satisfying `RowData` for the family. -/
private def thrCandidates (fam : ThrFamily) : Array (Array (Nat × Nat)) := Id.run do
  let markers := if fam == .haglundZhang then #[1, 2] else #[0, 1]
  let mut out := #[]
  for t₀ in [0:4] do
    for t₁ in [t₀:4] do
      for t₂ in [t₁:4] do
        for m₀ in markers do
          for m₁ in markers do
            for m₂ in markers do
              let rows := #[(t₀, m₀), (t₁, m₁), (t₂, m₂)]
              -- equal-threshold compatibility
              let bad : Nat := if fam == .haglundZhang then 2 else 0
              let mut ok := true
              for i in [0:3] do
                for j in [i:3] do
                  if rows[i]!.1 == rows[j]!.1 && rows[i]!.2 == bad && rows[j]!.2 != bad then
                    ok := false
              if ok then out := out.push rows
  return out

/-- One step `S ↦ G S`. -/
private def thrStep (rows : Array (Nat × Nat)) (S : Array QPoly) : Array QPoly :=
  rows.map fun (t, m) =>
    (List.range 3).foldl (fun acc j => acc + thrEntry t (thrMarker m) j * S[j]!) (QPoly.const 0)

/-- Search a threshold-orbit certificate for a pure-lag recurrence of order three with
constant multipliers. -/
private def thresholdProbe? (L : LinRecData) : MetaM (Option ThrPlan) := do
  unless L.offset == 3 && L.terms.all (fun (_, i, _) => i == 0) do return none
  -- the multipliers must not depend on `n`
  for (_, _, A) in L.terms do
    let some a₀ ← evalCoeffAt? A 0 | return none
    for m in [1:4] do
      let some a ← evalCoeffAt? A m | return none
      unless a == a₀ do return none
  let some rows ← linRecRows? L 20 | return none
  for fam in #[ThrFamily.haglundZhang, .gustafssonSolus] do
    for cand in thrCandidates fam do
      for c₀ in [0:3] do
        for c₁ in [0:3] do
          for c₂ in [0:3] do
            if c₀ + c₁ + c₂ == 0 then continue
            let S₀ := #[thrInput c₀, thrInput c₁, thrInput c₂]
            -- the orbit sums for 14 steps
            let mut S := S₀
            let mut sums : Array QPoly := #[]
            for _ in [0:14] do
              sums := sums.push (S.foldl (· + ·) (QPoly.const 0))
              S := thrStep cand S
            for t in [0:5] do
              if (List.range 14).all fun m => sums[m]! == rows[t + m]! then
                return some { fam, rows := cand, input := #[c₀, c₁, c₂], offset := t }
  return none

/-- `rr_row_splits` for an order-three sequence whose rows are threshold-matrix orbit sums
(see the module documentation). -/
def thresholdOrbitSplits : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some Pn ← findSeqConstDeep? tgt | throwError "rr_row_splits: no sequence in the goal"
  let some L ← linRec? Pn | throwError "rr_row_splits: {Pn} has no linear recurrence"
  let some plan ← thresholdProbe? L
    | throwError "rr_row_splits: no threshold-matrix orbit reproduces the rows of {Pn}"
  let (idx, c) ← rowIndexParts Pn
  let e ← indexTerm idx c
  let P := mkIdent Pn
  let eqn := mkIdent L.eqn
  let ns : Name := if plan.fam == .haglundZhang then `RealRooted.HaglundZhang
    else `RealRooted.GustafssonSolus
  let orbitI := mkIdent (ns ++ `orbit)
  let rowDataI := mkIdent (ns ++ `RowData)
  let certI := mkIdent (ns ++ `orbit_certificate)
  let sumI := mkIdent (ns ++ `splits_orbit_sum)
  let markerT (m : Nat) : TacticM Term :=
    match m with
    | 0 => `((0 : ℝ[X]))
    | 1 => `((1 : ℝ[X]))
    | _ => `((1 + Polynomial.X : ℝ[X]))
  let inputT (m : Nat) : TacticM Term :=
    match m with
    | 0 => `((0 : ℝ[X]))
    | 1 => `((1 : ℝ[X]))
    | _ => `((Polynomial.X : ℝ[X]))
  let mut rowTs : Array Term := #[]
  for (t, m) in plan.rows do
    rowTs := rowTs.push (← `(($(rowNumLit t), $(← markerT m))))
  let rowsT ← `([$rowTs,*])
  let mut inTs : Array Term := #[]
  for m in plan.input do
    inTs := inTs.push (← inputT m)
  let S₀T ← `([$inTs,*])
  let t := plan.offset
  let m := mkIdent `m
  -- the index `m + c`, written `m` when `c = 0`
  let idx (c : Nat) : TacticM Term :=
    if c == 0 then `($m) else `($m + $(rowNumLit c))
  let unfold ← `(tactic| simp only [rr_threshold_unfold, Nat.reduceLT, Nat.reduceEqDiff, reduceIte])
  let normIdx ← `(tactic| try simp only [Nat.add_assoc, Nat.reduceAdd])
  let orb (k : Term) : TacticM Term := `(($orbitI:ident 3 $rowsT $S₀T $k).sum)
  let (i₀, i₁, i₂) := (← idx t, ← idx (t + 1), ← idx (t + 2))
  let o₀ ← orb m
  let o₁ ← orb (← `($m + 1))
  let o₂ ← orb (← `($m + 2))
  let stmt ← `(∀ $m:ident, $P ($i₀) = $o₀ ∧ $P ($i₁) = $o₁ ∧ $P ($i₂) = $o₂)
  let finish : TSyntax `tactic ← if t == 0 then
      `(tactic| (
        have rr_hne : $P $e ≠ 0 := by rr_row_ne_zero
        rw [(rr_heq $e).1] at rr_hne ⊢
        exact $sumI:ident (q := 3) rr_hrows rfl rfl rr_hS₀ rr_hS₀r $e rr_hne))
    else
      `(tactic| (
        refine (Nat.lt_or_ge $e $(rowNumLit t)).elim (fun rr_hlt => ?_) (fun rr_hge => ?_)
        · interval_cases $e <;> first | (simp only [$P:ident]; rr_splits_explicit) | simp [$P:ident]
        · obtain ⟨$m:ident, hm⟩ := Nat.exists_eq_add_of_le' rr_hge
          have rr_hne : $P $e ≠ 0 := by rr_row_ne_zero
          rw [hm, (rr_heq $m).1] at *
          exact $sumI:ident (q := 3) rr_hrows rfl rfl rr_hS₀ rr_hS₀r $m rr_hne))
  let rr_script ← `(tactic| (
    have rr_hrows : $rowDataI:ident $rowsT := by
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with hp | hp | hp <;> subst hp <;> simp
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
    have rr_hS₀ : RealRooted.IsInterlacingSeq0Nonneg $S₀T := by
      constructor
      · intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [rr_threshold_unfold, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
        all_goals exact RealRooted.StrictInterl.refl (by simp) (by simp)
      · intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with hf | hf | hf <;> subst hf <;>
          first
            | exact RealRooted.hasNonnegCoeffs_one
            | exact RealRooted.hasNonnegCoeffs_zero
            | exact RealRooted.hasNonnegCoeffs_X
    have rr_hS₀r : ∀ f ∈ $S₀T, f ≠ 0 → (f ≠ 0 ∧ Polynomial.Splits f) := by
      intro f hf hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with hf | hf | hf <;> subst hf <;> simp_all
    have rr_hstate : ∀ $m:ident, ∃ a b c, $orbitI:ident 3 $rowsT $S₀T $m = [a, b, c] :=
      fun $m:ident =>
        List.length_eq_three.mp ($certI:ident rr_hrows rfl rfl rr_hS₀ rr_hS₀r $m).1
    have rr_heq : $stmt := by
      intro $m:ident
      induction $m:ident
      · refine ⟨?_, ?_, ?_⟩ <;>
          (simp only [$P:ident, rr_threshold_unfold, Nat.reduceLT, Nat.reduceEqDiff,
              reduceIte]
           first | rfl | ring | simp)
      · rename_i $m:ident ih
        obtain ⟨h₀, h₁, h₂⟩ := ih
        obtain ⟨a, b, c, h⟩ := rr_hstate $m
        refine ⟨?_, ?_, ?_⟩
        · $normIdx:tactic
          exact h₁
        · $normIdx:tactic
          exact h₂
        · $normIdx:tactic
          rw [$eqn:ident]
          $normIdx:tactic
          rw [h₀, h₁, h₂]
          simp only [rr_threshold_unfold, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
          rw [h]
          $unfold:tactic
          ring
    $finish:tactic))
  evalTactic rr_script

end RealRooted.Tactic
