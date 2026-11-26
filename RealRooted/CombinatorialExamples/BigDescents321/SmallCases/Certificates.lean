/-
Based on the finite cases from scripts/gen_big_descents_small_cases.py.
-/
module

import RealRooted.CombinatorialExamples.BigDescents321.SmallCases.Literals
import RealRooted.Basic.PolynomialFacts
import RealRooted.Bezoutian.Successor
import RealRooted.Tactic.InterlacesExplicit
public import RealRooted.CombinatorialExamples.BigDescents321.Basic
import RealRooted.Interlacing.Euclid
import RealRooted.ThreeTermRecurrence.Interlacing
public import RealRooted.Basic.ProperPosition
public meta import RealRooted.Tactic.Recurrence.Eval
public meta import RealRooted.CombinatorialExamples.BigDescents321.SmallCases.ListPoly

/-!
# Finite interlacing certificates for the small big-descent polynomials

For `3 ≤ n ≤ 24`, `M_(n-2)` interlaces `A_n`, by the exact Euclid chain of
`rr_interlaces_explicit`. An integer Bezout identity `U A_n + V M_(n-2) = D`, checked as an
integer-list computation, shows that the two polynomials have no common root, so both have
simple roots. The existing extended Euclidean algorithm supplies the integral data; the
producer is untrusted, and every list identity and nonzero scale is checked by the kernel.
-/

public section

open Polynomial

namespace RealRooted.BigDescents321.SmallCases

/-- Interlacing together with a Bezout identity `U * A + V * M = D`, `D ≠ 0`, gives simple
roots of both polynomials and no common root. -/
theorem nodup_of_interlaces_of_bezout {A M U V : ℝ[X]} {D : ℝ} (hI : Interlaces M A)
    (hB : U * A + V * M = C D) (hD' : D ≠ 0) :
    A.roots.Nodup ∧ M.roots.Nodup ∧ ∀ x, M.IsRoot x → ¬ A.IsRoot x := by
  have hcop : IsCoprime M A :=
    ⟨C D⁻¹ * V, C D⁻¹ * U, by
      rw [mul_assoc, mul_assoc, ← mul_add, add_comm, hB, ← C_mul, inv_mul_cancel₀ hD', C_1]⟩
  have hdisj : ∀ x, A.IsRoot x → ¬ M.IsRoot x := fun x hA hM ↦ hcop.not_isRoot_right hM hA
  exact ⟨(hI.roots_nodup_of_disjoint hdisj).1, (hI.roots_nodup_of_disjoint hdisj).2,
    fun x hM hA ↦ hdisj x hA hM⟩

/-- Propose integral Bezout witnesses using the existing extended Euclidean algorithm. -/
private meta def bezoutWitness (a m : RealRooted.Tactic.QPoly) : List ℤ × List ℤ × ℤ := Id.run do
  let (d, u₀, v₀) := a.xgcd m
  let u := u₀.smul d.lead⁻¹
  let v := v₀.smul d.lead⁻¹
  let den := (u.coeffs ++ v.coeffs).foldl (fun d c => d.lcm c.den) 1
  let integral (p : RealRooted.Tactic.QPoly) : List ℤ :=
    p.coeffs.toList.map fun c => c.num * ((den / c.den : ℕ) : ℤ)
  return (integral u, integral v, den)

/-- The producer only supplies data: Lean checks the entire integer-list identity and scale. -/
local elab "nodup_from_bezout " h:term : tactic => Lean.Elab.Tactic.withMainContext do
  let hi ← Lean.Elab.Term.elabTerm h none
  let ty ← Lean.Meta.inferType hi
  let m := ty.appFn!.appArg!
  let a := ty.appArg!
  let read (e : Lean.Expr) : Lean.MetaM RealRooted.Tactic.QPoly := do
    unless e.isAppOf ``ofList do
      Lean.throwError "Expected an integer-list polynomial, got {e}"
    let xs ← unsafe Lean.Meta.evalExpr (List ℤ)
      (Lean.mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Int)) e.appArg!
    return RealRooted.Tactic.QPoly.norm (xs.toArray.map fun z : ℤ => (z : Rat))
  let mq ← read m
  let aq ← read a
  let (u, v, d) := bezoutWitness aq mq
  let aa := aq.coeffs.toList.map Rat.num
  let mm := mq.coeffs.toList.map Rat.num
  let k := (addList (mulList u aa) (mulList v mm)).length - 1
  let u ← Lean.Elab.Term.exprToSyntax (Lean.toExpr u)
  let v ← Lean.Elab.Term.exprToSyntax (Lean.toExpr v)
  let d ← Lean.Elab.Term.exprToSyntax (Lean.toExpr d)
  let k := Lean.Syntax.mkNumLit (toString k)
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    refine nodup_of_interlaces_of_bezout (U := ofList $u) (V := ofList $v)
      (D := (($d : ℤ) : ℝ)) $h ?_ ?_
    · rw [← ofList_mulList, ← ofList_mulList, ← ofList_addList]
      trans ofList (($d : ℤ) :: List.replicate $k 0)
      · exact congrArg ofList (by decide +kernel)
      · exact ofList_cons_replicate_zero _ _
    · exact_mod_cast (by decide +kernel : ($d : ℤ) ≠ 0))))

/-- Replay the same interlacing and coprimality argument at each literal row. -/
local elab "small_case_certificate" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.Elab.Tactic.getMainTarget
  let interlaces := target.appFn!.appArg!
  let n ← unsafe Lean.Meta.evalExpr Nat (Lean.mkConst ``Nat) interlaces.appArg!.appArg!
  unless 3 ≤ n && n ≤ 24 do Lean.throwError "Expected a small-case index in [3, 24]"
  let ns := `RealRooted.BigDescents321.SmallCases
  let hm := Lean.mkIdent (ns ++ Lean.Name.mkSimple s!"motzkinRef_{n - 2}")
  let ha := Lean.mkIdent (ns ++ Lean.Name.mkSimple s!"bigDescentPoly_{n}")
  let hm ← `(Lean.Parser.Tactic.rwRule| $hm:term)
  let ha ← `(Lean.Parser.Tactic.rwRule| $ha:term)
  let statement ← Lean.Elab.Term.exprToSyntax interlaces
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    have hI : $statement := by
      rw [$hm, $ha]
      simp only [ofList_cons, ofList_nil, Int.cast_ofNat, Int.cast_one, map_ofNat, map_one,
        mul_zero, add_zero, mul_one]
      rr_interlaces_explicit
    refine ⟨hI, ?_⟩
    rw [$hm, $ha] at hI ⊢
    nodup_from_bezout hI)))

theorem interlaces_and_nodup_3 :
    Interlaces (motzkinRef 1 : ℝ[X]) (bigDescentPoly 3) ∧
      (bigDescentPoly 3 : ℝ[X]).roots.Nodup ∧ (motzkinRef 1 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 1 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 3 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_4 :
    Interlaces (motzkinRef 2 : ℝ[X]) (bigDescentPoly 4) ∧
      (bigDescentPoly 4 : ℝ[X]).roots.Nodup ∧ (motzkinRef 2 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 2 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 4 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_5 :
    Interlaces (motzkinRef 3 : ℝ[X]) (bigDescentPoly 5) ∧
      (bigDescentPoly 5 : ℝ[X]).roots.Nodup ∧ (motzkinRef 3 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 3 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 5 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_6 :
    Interlaces (motzkinRef 4 : ℝ[X]) (bigDescentPoly 6) ∧
      (bigDescentPoly 6 : ℝ[X]).roots.Nodup ∧ (motzkinRef 4 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 4 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 6 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_7 :
    Interlaces (motzkinRef 5 : ℝ[X]) (bigDescentPoly 7) ∧
      (bigDescentPoly 7 : ℝ[X]).roots.Nodup ∧ (motzkinRef 5 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 5 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 7 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_8 :
    Interlaces (motzkinRef 6 : ℝ[X]) (bigDescentPoly 8) ∧
      (bigDescentPoly 8 : ℝ[X]).roots.Nodup ∧ (motzkinRef 6 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 6 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 8 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_9 :
    Interlaces (motzkinRef 7 : ℝ[X]) (bigDescentPoly 9) ∧
      (bigDescentPoly 9 : ℝ[X]).roots.Nodup ∧ (motzkinRef 7 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 7 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 9 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_10 :
    Interlaces (motzkinRef 8 : ℝ[X]) (bigDescentPoly 10) ∧
      (bigDescentPoly 10 : ℝ[X]).roots.Nodup ∧ (motzkinRef 8 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 8 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 10 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_11 :
    Interlaces (motzkinRef 9 : ℝ[X]) (bigDescentPoly 11) ∧
      (bigDescentPoly 11 : ℝ[X]).roots.Nodup ∧ (motzkinRef 9 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 9 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 11 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_12 :
    Interlaces (motzkinRef 10 : ℝ[X]) (bigDescentPoly 12) ∧
      (bigDescentPoly 12 : ℝ[X]).roots.Nodup ∧ (motzkinRef 10 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 10 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 12 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_13 :
    Interlaces (motzkinRef 11 : ℝ[X]) (bigDescentPoly 13) ∧
      (bigDescentPoly 13 : ℝ[X]).roots.Nodup ∧ (motzkinRef 11 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 11 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 13 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_14 :
    Interlaces (motzkinRef 12 : ℝ[X]) (bigDescentPoly 14) ∧
      (bigDescentPoly 14 : ℝ[X]).roots.Nodup ∧ (motzkinRef 12 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 12 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 14 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_15 :
    Interlaces (motzkinRef 13 : ℝ[X]) (bigDescentPoly 15) ∧
      (bigDescentPoly 15 : ℝ[X]).roots.Nodup ∧ (motzkinRef 13 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 13 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 15 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_16 :
    Interlaces (motzkinRef 14 : ℝ[X]) (bigDescentPoly 16) ∧
      (bigDescentPoly 16 : ℝ[X]).roots.Nodup ∧ (motzkinRef 14 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 14 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 16 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_17 :
    Interlaces (motzkinRef 15 : ℝ[X]) (bigDescentPoly 17) ∧
      (bigDescentPoly 17 : ℝ[X]).roots.Nodup ∧ (motzkinRef 15 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 15 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 17 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_18 :
    Interlaces (motzkinRef 16 : ℝ[X]) (bigDescentPoly 18) ∧
      (bigDescentPoly 18 : ℝ[X]).roots.Nodup ∧ (motzkinRef 16 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 16 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 18 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_19 :
    Interlaces (motzkinRef 17 : ℝ[X]) (bigDescentPoly 19) ∧
      (bigDescentPoly 19 : ℝ[X]).roots.Nodup ∧ (motzkinRef 17 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 17 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 19 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_20 :
    Interlaces (motzkinRef 18 : ℝ[X]) (bigDescentPoly 20) ∧
      (bigDescentPoly 20 : ℝ[X]).roots.Nodup ∧ (motzkinRef 18 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 18 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 20 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_21 :
    Interlaces (motzkinRef 19 : ℝ[X]) (bigDescentPoly 21) ∧
      (bigDescentPoly 21 : ℝ[X]).roots.Nodup ∧ (motzkinRef 19 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 19 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 21 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_22 :
    Interlaces (motzkinRef 20 : ℝ[X]) (bigDescentPoly 22) ∧
      (bigDescentPoly 22 : ℝ[X]).roots.Nodup ∧ (motzkinRef 20 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 20 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 22 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_23 :
    Interlaces (motzkinRef 21 : ℝ[X]) (bigDescentPoly 23) ∧
      (bigDescentPoly 23 : ℝ[X]).roots.Nodup ∧ (motzkinRef 21 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 21 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 23 : ℝ[X]).IsRoot x := by
  small_case_certificate

theorem interlaces_and_nodup_24 :
    Interlaces (motzkinRef 22 : ℝ[X]) (bigDescentPoly 24) ∧
      (bigDescentPoly 24 : ℝ[X]).roots.Nodup ∧ (motzkinRef 22 : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef 22 : ℝ[X]).IsRoot x → ¬ (bigDescentPoly 24 : ℝ[X]).IsRoot x := by
  small_case_certificate

/-- The finite cases `3 ≤ n + 3 ≤ 24`: `M_(n+1)` interlaces `A_(n+3)`, both have simple
roots, and they have no common root. -/
theorem interlaces_and_nodup_of_le {n : ℕ} (hn : n ≤ 21) :
    Interlaces (motzkinRef (n + 1) : ℝ[X]) (bigDescentPoly (n + 3)) ∧
      (bigDescentPoly (n + 3) : ℝ[X]).roots.Nodup ∧
      (motzkinRef (n + 1) : ℝ[X]).roots.Nodup ∧
      ∀ x, (motzkinRef (n + 1) : ℝ[X]).IsRoot x →
        ¬ (bigDescentPoly (n + 3) : ℝ[X]).IsRoot x := by
  interval_cases n
  · exact interlaces_and_nodup_3
  · exact interlaces_and_nodup_4
  · exact interlaces_and_nodup_5
  · exact interlaces_and_nodup_6
  · exact interlaces_and_nodup_7
  · exact interlaces_and_nodup_8
  · exact interlaces_and_nodup_9
  · exact interlaces_and_nodup_10
  · exact interlaces_and_nodup_11
  · exact interlaces_and_nodup_12
  · exact interlaces_and_nodup_13
  · exact interlaces_and_nodup_14
  · exact interlaces_and_nodup_15
  · exact interlaces_and_nodup_16
  · exact interlaces_and_nodup_17
  · exact interlaces_and_nodup_18
  · exact interlaces_and_nodup_19
  · exact interlaces_and_nodup_20
  · exact interlaces_and_nodup_21
  · exact interlaces_and_nodup_22
  · exact interlaces_and_nodup_23
  · exact interlaces_and_nodup_24

end RealRooted.BigDescents321.SmallCases
