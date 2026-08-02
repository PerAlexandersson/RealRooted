import RealRooted.Compatibility.Basic
import RealRooted.DerivativeShiftSequence
import RealRooted.LiuOppositeSigns.DerivativeShiftRegularization

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
