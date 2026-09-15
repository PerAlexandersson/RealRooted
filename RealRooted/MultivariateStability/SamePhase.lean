import Mathlib.Topology.Algebra.MvPolynomial
import RealRooted.AffineLineRestriction
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.SamePhaseStability

/-!
# Real stability implies same-phase stability

This file transfers multivariate real stability to every nonnegative
common-phase restriction.  Strictly positive weights follow from affine-line
restriction; zero weights are obtained by a bounded-degree closed-root limit.
-/

open Filter Polynomial Topology

namespace RealRooted

noncomputable section

/-- A strictly positive common-phase restriction of a real-stable polynomial
is both nonzero and split over the reals. -/
theorem MvRealStable.commonPhaseRestriction_splits_ne_zero_of_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    (wt : σ → ℝ) (hwt : ∀ i, 0 < wt i) :
    (commonPhaseRestriction wt P).Splits ∧
      commonPhaseRestriction wt P ≠ 0 := by
  simpa [commonPhaseRestriction, realAffineLineRestriction] using
    hP.realAffineLineRestriction_splits_ne_zero (fun _ => 0) wt hwt

/-- Every real-stable multivariate polynomial is same-phase stable, including
restrictions in which some coordinate weights vanish. -/
theorem MvRealStable.samePhaseStable {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvRealStable P) :
    SamePhaseStable P := by
  intro wt hwt
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let wtApprox : ℕ → σ → ℝ := fun n i => wt i + δ n
  let q : ℕ → ℝ[X] := fun n => commonPhaseRestriction (wtApprox n) P
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    positivity
  have hwtApprox (n : ℕ) : ∀ i, 0 < wtApprox n i := by
    intro i
    exact add_pos_of_nonneg_of_pos (hwt i) (hδpos n)
  have hq_splits (n : ℕ) : (q n).Splits :=
    (hP.commonPhaseRestriction_splits_ne_zero_of_pos
      (wtApprox n) (hwtApprox n)).1
  have hq_degree (n : ℕ) : (q n).natDegree ≤ P.totalDegree := by
    simpa [q, commonPhaseRestriction, MvPolynomial.affineLineRestriction] using
      MvPolynomial.natDegree_affineLineRestriction_le
        (fun _ : σ => 0) (wtApprox n) P
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heval (z : ℂ) : Tendsto
      (fun n => ((q n).map Complex.ofRealHom).eval z) atTop
      (𝓝 (((commonPhaseRestriction wt P).map Complex.ofRealHom).eval z)) := by
    have hassign : Tendsto
        (fun n i => ((wtApprox n i : ℝ) : ℂ) * z) atTop
        (𝓝 fun i => (wt i : ℂ) * z) := by
      rw [tendsto_pi_nhds]
      intro i
      have hweight : Tendsto (fun n => wtApprox n i) atTop (𝓝 (wt i)) := by
        simpa [wtApprox] using tendsto_const_nhds.add hδ
      exact ((Complex.continuous_ofReal.tendsto (wt i)).comp hweight).mul_const z
    have hcontinuous :=
      (MvPolynomial.continuous_eval (complexifyMv P)).continuousAt.tendsto.comp
        hassign
    simpa only [Function.comp_def, q, eval_map_commonPhaseRestriction] using
      hcontinuous
  rcases Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
      hq_degree (fun n => Or.inr (hq_splits n)) heval with hzero | hsplits
  · rw [hzero]
    exact Polynomial.Splits.zero
  · exact hsplits

end

end RealRooted
