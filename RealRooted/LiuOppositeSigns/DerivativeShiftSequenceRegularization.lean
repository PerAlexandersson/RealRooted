import RealRooted.Compatibility.Basic
import RealRooted.DerivativeShiftSequence
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

/-- Choose a prescribed number of bounded positive common derivative shifts.

At every stage, the next shift is smaller than both `κ` and the local radius
from `NoCommonRoots.exists_delta_TDeriv`.  Consequently compatibility and the
absence of common roots survive the entire sequence.
-/
theorem NoCommonRoots.exists_applyTDerivList
    {f g : ℝ[X]} (hcomp : Compatible f g) (hno : NoCommonRoots f g)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ∃ epss : List ℝ,
      epss.length = n ∧
      (∀ eps ∈ epss, 0 < eps ∧ eps < κ) ∧
      Compatible (applyTDerivList epss f) (applyTDerivList epss g) ∧
      NoCommonRoots (applyTDerivList epss f) (applyTDerivList epss g) := by
  induction n generalizing f g with
  | zero =>
      exact ⟨[], rfl, by simp, by simpa using hcomp, by simpa using hno⟩
  | succ n ih =>
      obtain ⟨δ, hδ, hpreserve⟩ :=
        hno.exists_delta_TDeriv hf_ne hg_ne hf hg
      let eps := min δ κ / 2
      have hmin : 0 < min δ κ := lt_min hδ hκ
      have heps : 0 < eps := by
        dsimp [eps]
        linarith
      have heps_delta : eps < δ := by
        have hle : min δ κ ≤ δ := min_le_left δ κ
        dsimp [eps]
        linarith
      have heps_kappa : eps < κ := by
        have hle : min δ κ ≤ κ := min_le_right δ κ
        dsimp [eps]
        linarith
      have hcomp_shift : Compatible (TDeriv eps f) (TDeriv eps g) := by
        simpa using hcomp.iterateTDeriv heps 1
      have hno_shift : NoCommonRoots (TDeriv eps f) (TDeriv eps g) :=
        hpreserve heps heps_delta
      obtain ⟨epss, hlength, hbounds, hcomp_final, hno_final⟩ :=
        ih hcomp_shift hno_shift (TDeriv_ne_zero hf_ne) (TDeriv_ne_zero hg_ne)
          (splits_tderiv heps hf) (splits_tderiv heps hg)
      refine ⟨eps :: epss, by simp [hlength], ?_, ?_, ?_⟩
      · intro eta heta
        rcases List.mem_cons.mp heta with rfl | heta
        · exact ⟨heps, heps_kappa⟩
        · exact hbounds eta heta
      · simpa using hcomp_final
      · simpa using hno_final

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

/-- Bounded common shifts regularize both endpoints while preserving all Liu hypotheses. -/
theorem NoCommonRoots.exists_simple_applyTDerivList
    {f g : ℝ[X]} (hcomp : Compatible f g) (hno : NoCommonRoots f g)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hopp : f.leadingCoeff * g.leadingCoeff < 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ epss : List ℝ,
      epss.length = max f.natDegree g.natDegree ∧
      (∀ eps ∈ epss, 0 < eps ∧ eps < κ) ∧
      Compatible (applyTDerivList epss f) (applyTDerivList epss g) ∧
      NoCommonRoots (applyTDerivList epss f) (applyTDerivList epss g) ∧
      applyTDerivList epss f ≠ 0 ∧
      applyTDerivList epss g ≠ 0 ∧
      (applyTDerivList epss f).Splits ∧
      (applyTDerivList epss g).Splits ∧
      (applyTDerivList epss f).natDegree = f.natDegree ∧
      (applyTDerivList epss g).natDegree = g.natDegree ∧
      (applyTDerivList epss f).leadingCoeff = f.leadingCoeff ∧
      (applyTDerivList epss g).leadingCoeff = g.leadingCoeff ∧
      (applyTDerivList epss f).leadingCoeff *
          (applyTDerivList epss g).leadingCoeff < 0 ∧
      HasSimpleRoots (applyTDerivList epss f) ∧
      HasSimpleRoots (applyTDerivList epss g) := by
  obtain ⟨epss, hlength, hbounds, hcomp_final, hno_final⟩ :=
    hno.exists_applyTDerivList hcomp hf_ne hg_ne hf hg hκ
      (max f.natDegree g.natDegree)
  have hpos : ∀ eps ∈ epss, 0 < eps := by
    intro eps heps
    exact (hbounds eps heps).1
  have hf_simple : HasSimpleRoots (applyTDerivList epss f) := by
    apply hasSimpleRoots_applyTDerivList_of_natDegree_le_length hpos hf_ne hf
    rw [hlength]
    exact Nat.le_max_left _ _
  have hg_simple : HasSimpleRoots (applyTDerivList epss g) := by
    apply hasSimpleRoots_applyTDerivList_of_natDegree_le_length hpos hg_ne hg
    rw [hlength]
    exact Nat.le_max_right _ _
  refine ⟨epss, hlength, hbounds, hcomp_final, hno_final,
    applyTDerivList_ne_zero hf_ne, applyTDerivList_ne_zero hg_ne,
    hf.applyTDerivList hpos, hg.applyTDerivList hpos, by simp, by simp,
    by simp, by simp, ?_, hf_simple, hg_simple⟩
  simpa using hopp

end


end LiuOppositeSigns
end RealRooted
