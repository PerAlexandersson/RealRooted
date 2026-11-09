/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Wronskian.Successor.Splits

/-!
# Splitting from sign alternation at the roots of a derivative-degree companion

Let `G` be a split real polynomial with simple roots `r₀ < ⋯ < r_{n-1}` and let `F` be a real
polynomial of degree `n + 1` whose leading coefficient has the same sign as that of `G`.
If `F (rₖ) * G' (rₖ) < 0` at every root `rₖ` of `G`, then `F` takes alternating signs at the
roots of `G`, hence has a root in each gap, one below `r₀` and one above `r_{n-1}`: `F` has
`n + 1` distinct real roots and splits.  This is the Wronskian-positivity argument of
`RealRooted.splits_of_wronskian_neg_succ_of_isRoot`, which needs the Wronskian only at the
roots of `G`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- **Splitting from sign alternation.** Let `G` be a split real polynomial and `F` a real
polynomial of degree `deg G + 1` whose leading coefficient has the same sign as that of `G`.
If `F ρ * G' ρ < 0` at every root `ρ` of `G`, then `F` splits. -/
theorem splits_of_eval_mul_derivative_neg {F G : ℝ[X]} (hG : G.Splits)
    (hdeg : F.natDegree = G.natDegree + 1) (hlc : 0 < F.leadingCoeff * G.leadingCoeff)
    (hsign : ∀ ρ, G.IsRoot ρ → F.eval ρ * (derivative G).eval ρ < 0) : F.Splits := by
  have hG0 : G.leadingCoeff ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hlc
    exact lt_irrefl _ hlc
  rcases Nat.eq_zero_or_pos G.natDegree with h0 | hn
  · exact Splits.of_natDegree_le_one (by lia)
  obtain ⟨n, hn'⟩ : ∃ n, G.natDegree = n + 1 := ⟨G.natDegree - 1, by lia⟩
  rcases lt_or_gt_of_ne hG0 with hneg | hpos
  · have hF : F.leadingCoeff < 0 := by nlinarith
    have := splits_of_wronskian_neg_succ_of_isRoot (f := -G) (g := -F) (n := n)
      (by simpa [HasPosLeadingCoeff] using hneg) (by simpa [HasPosLeadingCoeff] using hF)
      (by simpa using hn') (by simpa [hn'] using hdeg) hG.neg
      (fun ρ hρ => by simpa [mul_comm] using hsign ρ (by simpa using hρ))
    simpa using this.neg
  · have hF : HasPosLeadingCoeff F := by unfold HasPosLeadingCoeff; nlinarith
    exact splits_of_wronskian_neg_succ_of_isRoot hpos hF hn' (by lia) hG
      (fun ρ hρ => by simpa [mul_comm] using hsign ρ hρ)

end RealRooted
