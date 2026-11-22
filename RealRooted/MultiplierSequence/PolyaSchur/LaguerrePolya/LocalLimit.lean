module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FormalJensen
import RealRooted.MultiplierSequence.JensenLimit
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.Mathlib.Analysis.Complex.LocallyUniformIteratedDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Entire extension of local Laguerre--Pólya limits

A locally uniform limit on a disk of entire Laguerre--Pólya functions extends
to an entire function in the same class. No nonzero value is required, and the
conclusion does not claim global convergence of the original sequence.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- Limits of all Taylor data of Laguerre--Pólya functions define an entire
function in the same class, without any assumed growth bound on those data. -/
theorem isLaguerrePolya_of_tendsto_iteratedDeriv {F : ℕ → ℂ → ℂ} {c : ℕ → ℝ}
    (hF : ∀ n, IsLaguerrePolya (F n))
    (hc : ∀ k, Tendsto (fun n => (iteratedDeriv k (F n) 0).re) atTop (𝓝 (c k))) :
    IsLaguerrePolya (complexExpGeneratingFunction c) := by
  apply isLaguerrePolya_of_jensenPolynomial_splits
  intro d
  exact jensenPolynomial_splits_of_tendsto d
    (fun n => (hF n).jensenPolynomial_splits d) hc

/-- A local uniform limit of entire Laguerre--Pólya functions on a nonempty
disk centered at zero has an entire Laguerre--Pólya extension. This includes
an identically zero local limit. -/
theorem exists_isLaguerrePolya_eqOn_of_local_limit {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) {r : ℝ} (hr : 0 < r)
    (hlim : TendstoLocallyUniformlyOn F g atTop (Metric.ball 0 r)) :
    ∃ G : ℂ → ℂ, IsLaguerrePolya G ∧ Set.EqOn G g (Metric.ball 0 r) := by
  have hd : ∀ᶠ n in atTop, Differentiable ℂ (F n) :=
    Eventually.of_forall fun n => (hF n).differentiable
  have hzero : (0 : ℂ) ∈ Metric.ball 0 r := by simpa using hr
  have hjet (k : ℕ) : Tendsto (fun n => iteratedDeriv k (F n) 0) atTop
      (𝓝 (iteratedDeriv k g 0)) :=
    (hlim.iteratedDeriv_of_entire hd Metric.isOpen_ball k).tendsto_at hzero
  have hjet_re (k : ℕ) := (Complex.continuous_re.tendsto _).comp (hjet k)
  have hreal (k : ℕ) : ((iteratedDeriv k g 0).re : ℂ) = iteratedDeriv k g 0 := by
    exact tendsto_nhds_unique (hjet_re k).ofReal
      ((hjet k).congr fun n => (ofReal_re_iteratedDeriv_zero (hF n).conj k).symm)
  let c : ℕ → ℝ := fun k => (iteratedDeriv k g 0).re
  refine ⟨complexExpGeneratingFunction c,
    isLaguerrePolya_of_tendsto_iteratedDeriv hF hjet_re, ?_⟩
  have hg := hlim.differentiableOn (hd.mono fun _ hi => hi.differentiableOn) Metric.isOpen_ball
  intro z hz
  rw [complexExpGeneratingFunction_eq_tsum, ← taylorSeries_eq_on_ball' hz hg]
  apply tsum_congr
  intro k
  simp only [c, ofReal_div, ofReal_natCast, hreal, sub_zero]
  ring

end RealRooted
