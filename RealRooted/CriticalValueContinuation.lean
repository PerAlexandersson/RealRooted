import RealRooted.SimpleRoots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Continuation of simple polynomial roots

This file packages the local implicit-function input used by critical-value
continuation arguments.  It deliberately records only a smooth local root
branch; formulas for the branch derivative belong in downstream applications.
-/

open Filter Polynomial Topology
open scoped ContDiff

noncomputable section

namespace RealRooted

/-- A uniform degree bound and coefficientwise continuity give continuity of
evaluation along a continuous parameter-dependent point. -/
theorem Polynomial.continuous_eval_of_continuous_coeff
    {T : Type*} [TopologicalSpace T]
    (p : T → ℝ[X]) {N : ℕ}
    (hdegree : ∀ t, (p t).natDegree ≤ N)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    {x : T → ℝ} (hx : Continuous x) :
    Continuous fun t => (p t).eval (x t) := by
  rw [show (fun t => (p t).eval (x t)) =
      fun t => ∑ i ∈ Finset.range (N + 1),
        (p t).coeff i * x t ^ i by
    funext t
    exact Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le (hdegree t)) (x t)]
  exact continuous_finsetSum _ fun i _ =>
    (hcoeff i).mul (hx.pow i)

private theorem toSpanSingleton_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  refine ⟨e, ?_⟩
  ext
  simp [e, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-- A regular real root of a jointly `C¹` polynomial family admits a local
`C¹` parameter branch. -/
theorem exists_contDiffAt_polynomial_root
    (p : ℝ → ℝ[X]) {t r : ℝ}
    (hF : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => (p z.1).eval z.2) (t, r))
    (hr : (p t).IsRoot r)
    (hregular : (p t).derivative.eval r ≠ 0) :
    ∃ ρ : ℝ → ℝ,
      ContDiffAt ℝ 1 ρ t ∧
        ρ t = r ∧
          ∀ᶠ s in 𝓝 t, (p s).IsRoot (ρ s) := by
  let F : ℝ × ℝ → ℝ := fun z => (p z.1).eval z.2
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (t, r) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hfull : HasFDerivAt F (fderiv ℝ F (t, r)) (t, r) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hA : A = ContinuousLinearMap.toSpanSingleton ℝ
      ((p t).derivative.eval r) := by
    apply HasFDerivAt.unique
    · exact hfull.comp r (hasFDerivAt_prodMk_right t r)
    · exact (p t).hasFDerivAt r
  have hAinv : A.IsInvertible := by
    rw [hA]
    exact toSpanSingleton_isInvertible hregular
  let ρ : ℝ → ℝ := hF.implicitFunction (by simp) hAinv
  have hρbase : ρ t = r :=
    hF.implicitFunction_apply_self (by simp) hAinv
  have hρroot : ∀ᶠ s in 𝓝 t, (p s).IsRoot (ρ s) := by
    have heq := hF.eventually_apply_implicitFunction (by simp) hAinv
    filter_upwards [heq] with s hs
    rw [Polynomial.IsRoot.def]
    change F (s, ρ s) = 0
    simpa only [F, Polynomial.IsRoot.def] using hs.trans (by simpa using hr)
  exact ⟨ρ, hF.contDiffAt_implicitFunction (by simp) hAinv,
    hρbase, hρroot⟩

end RealRooted
