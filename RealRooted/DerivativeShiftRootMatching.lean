import RealRooted.IteratedDerivativeShift
import RealRooted.RootMultiplicityMatching
import RealRooted.SameDegreeMultiplicityLowerCount

/-!
# Root matching for derivative shifts

This module combines coefficient continuity of `TDeriv` with the
multiplicity-aware finite matching API. It provides the root transport needed
when derivative shifts are used to regularize a compatible polynomial pair.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- For every positive radius, all roots of a sufficiently small positive
`TDeriv` shift can be matched, with multiplicity, to roots of the original
splitting polynomial within that radius. -/
theorem exists_delta_roots_rel_TDeriv
    {p : ℝ[X]} (hp : p.Splits) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → eps < δ →
      Multiset.Rel (fun r q ↦ |q - r| < ρ) p.roots (TDeriv eps p).roots := by
  obtain ⟨η, hη_pos, hηρ, hsep⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset p.roots hρ
  have hshift (nu : ℝ) :
      p + C nu * (-p.derivative) = TDeriv nu p := by
    simp only [TDeriv, sub_eq_add_neg, mul_neg]
  have hp0 : (p + C (0 : ℝ) * (-p.derivative)).Splits := by simpa using hp
  obtain ⟨δ, hδ_pos, hlocal⟩ :=
    exists_eps_forall_root_count_le_card_filter_near
      (f := p) (g := -p.derivative) (μ0 := 0) hp0 η hη_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro eps heps_pos hepsδ
  have heps_abs : |eps - 0| < δ := by simpa [abs_of_pos heps_pos] using hepsδ
  have hsplit : (p + C eps * (-p.derivative)).Splits := by
    rw [hshift]
    exact splits_tderiv heps_pos hp
  have hdeg :
      (p + C eps * (-p.derivative)).natDegree =
        (p + C (0 : ℝ) * (-p.derivative)).natDegree := by
    rw [hshift eps, hshift 0, natDegree_TDeriv, natDegree_TDeriv]
  have hcount := hlocal eps heps_abs hsplit hdeg
  rw [hshift eps, hshift 0] at hcount
  have hcount' : ∀ a ∈ p.roots.toFinset,
      p.roots.count a ≤
        ((TDeriv eps p).roots.filter (fun q ↦ |q - a| < η)).card := by
    simpa [TDeriv] using hcount
  have hcard : (TDeriv eps p).roots.card = p.roots.card := by
    rw [card_roots_of_splits (splits_tderiv heps_pos hp), natDegree_TDeriv,
      card_roots_of_splits hp]
  have hrel :=
    Multiset.rel_of_forall_le_count_of_card_eq hsep hcount' hcard
  exact hrel.mono fun _ _ _ _ hclose ↦ lt_trans hclose hηρ

end RealRooted
