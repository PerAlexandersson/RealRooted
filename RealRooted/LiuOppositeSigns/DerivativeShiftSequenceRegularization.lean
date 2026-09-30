import RealRooted.Compatibility.Basic
import RealRooted.Derivative.ShiftSequence
import RealRooted.LiuOppositeSigns.DerivativeShiftRegularization
import RealRooted.Mathlib.Data.Multiset.Rel

/-!
# Finite derivative-shift regularization for Liu's opposite-sign theorem

Liu's source proof reduces to endpoints with no common zeros and then treats
those endpoints as if all zeros were simple.  That implication is false for
individual endpoints.  The theorems below provide the required rigorous
replacement: repeatedly apply a common positive derivative shift, choosing a
new sufficiently small parameter at each stage.

Every parameter can additionally be bounded by an arbitrary `κ > 0`.  This
quantitative bound is retained for the later limiting argument rather than
merely producing one unrelated pair with simple roots.
-/

namespace RealRooted
namespace LiuOppositeSigns

open Polynomial

noncomputable section

/-- Choose bounded common shifts whose final roots stay uniformly close to the originals. -/
theorem NoCommonRoots.exists_applyTDerivList_roots_rel
    {f g : ℝ[X]} (hcomp : Compatible f g) (hno : NoCommonRoots f g)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (n : ℕ) :
    ∃ epss : List ℝ,
      epss.length = n ∧
      (∀ eps ∈ epss, 0 < eps ∧ eps < κ) ∧
      Compatible (applyTDerivList epss f) (applyTDerivList epss g) ∧
      NoCommonRoots (applyTDerivList epss f) (applyTDerivList epss g) ∧
      Multiset.Rel (fun r q ↦ |q - r| < ρ)
        f.roots (applyTDerivList epss f).roots ∧
      Multiset.Rel (fun r q ↦ |q - r| < ρ)
        g.roots (applyTDerivList epss g).roots := by
  induction n generalizing f g ρ with
  | zero =>
      refine ⟨[], rfl, by simp, by simpa using hcomp, by simpa using hno, ?_, ?_⟩
      · apply Multiset.rel_refl_of_refl_on
        intro r hr
        simpa using hρ
      · apply Multiset.rel_refl_of_refl_on
        intro r hr
        simpa using hρ
  | succ n ih =>
      have hhalf : 0 < ρ / 2 := by linarith
      obtain ⟨δno, hδno, hpreserve⟩ :=
        hno.exists_delta_TDeriv hf_ne hg_ne hf hg
      obtain ⟨δf, hδf, hfclose⟩ :=
        exists_delta_roots_rel_TDeriv hf hhalf
      obtain ⟨δg, hδg, hgclose⟩ :=
        exists_delta_roots_rel_TDeriv hg hhalf
      let δ := min δno (min δf (min δg κ))
      have hδ : 0 < δ := lt_min hδno (lt_min hδf (lt_min hδg hκ))
      have hδ_no : δ ≤ δno := min_le_left _ _
      have hδ_tail : δ ≤ min δf (min δg κ) := min_le_right _ _
      have hδ_f : δ ≤ δf := hδ_tail.trans (min_le_left _ _)
      have hδ_g : δ ≤ δg :=
        hδ_tail.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hδ_kappa : δ ≤ κ :=
        hδ_tail.trans ((min_le_right _ _).trans (min_le_right _ _))
      let eps := δ / 2
      have heps : 0 < eps := by
        dsimp [eps]
        linarith
      have heps_no : eps < δno := by
        dsimp [eps]
        linarith
      have heps_f : eps < δf := by
        dsimp [eps]
        linarith
      have heps_g : eps < δg := by
        dsimp [eps]
        linarith
      have heps_kappa : eps < κ := by
        dsimp [eps]
        linarith
      have hcomp_shift : Compatible (TDeriv eps f) (TDeriv eps g) := by
        simpa using hcomp.iterateTDeriv heps 1
      have hno_shift : NoCommonRoots (TDeriv eps f) (TDeriv eps g) :=
        hpreserve heps heps_no
      have hf_step := hfclose heps heps_f
      have hg_step := hgclose heps heps_g
      obtain ⟨epss, hlength, hbounds, hcomp_final, hno_final,
          hf_tail, hg_tail⟩ :=
        ih hcomp_shift hno_shift (TDeriv_ne_zero hf_ne) (TDeriv_ne_zero hg_ne)
          (splits_tderiv heps hf) (splits_tderiv heps hg) hhalf
      have hf_final := Multiset.Rel.comp
        (fun a b c hab hbc => by
          calc
            |c - a| = |(c - b) + (b - a)| := by ring_nf
            _ ≤ |c - b| + |b - a| := abs_add_le _ _
            _ < ρ / 2 + ρ / 2 := add_lt_add hbc hab
            _ = ρ := by ring)
        hf_step hf_tail
      have hg_final := Multiset.Rel.comp
        (fun a b c hab hbc => by
          calc
            |c - a| = |(c - b) + (b - a)| := by ring_nf
            _ ≤ |c - b| + |b - a| := abs_add_le _ _
            _ < ρ / 2 + ρ / 2 := add_lt_add hbc hab
            _ = ρ := by ring)
        hg_step hg_tail
      refine ⟨eps :: epss, by simp [hlength], ?_, ?_, ?_, ?_, ?_⟩
      · intro eta heta
        rcases List.mem_cons.mp heta with rfl | heta
        · exact ⟨heps, heps_kappa⟩
        · exact hbounds eta heta
      · simpa using hcomp_final
      · simpa using hno_final
      · simpa using hf_final
      · simpa using hg_final

end


end LiuOppositeSigns
end RealRooted
