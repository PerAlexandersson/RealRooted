module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.PointwiseLimit
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DifferentialApply
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.JensenDifferential
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Infinite differential operators under local pointwise convergence

O'Sullivan, *Zeros of Jensen polynomials and asymptotics for the Riemann xi
function*, Theorem 3.6, quotes Pólya's infinite differential-operator theorem.
The original appears as Zusatz II on page 242 of Pólya, *Algebraische
Untersuchungen über ganze Funktionen vom Geschlechte Null und Eins* (1915).

The hypothesis below is ordinary pointwise convergence of the derivative
series on a complex disk. Neither absolute nor locally uniform convergence is
assumed. Finite Jensen symbols preserve the Laguerre--Pólya class, converge at
each point by regular summation, and the pointwise local-limit theorem provides
an entire extension. The zero output and zeros at the origin are included.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

/-- A locally pointwise convergent infinite differential series with a
Laguerre--Pólya symbol and target represents an entire Laguerre--Pólya function.
This is O'Sullivan's Theorem 3.6, with ordinary convergence and zero output allowed. -/
theorem IsLaguerrePolya.exists_eqOn_differential_series {φ ψ g : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hψ : IsLaguerrePolya ψ) {r : ℝ}
    (hseries : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun n => ∑ j ∈ Finset.range n,
        iteratedDeriv j φ 0 * iteratedDeriv j ψ z / j.factorial) atTop (𝓝 (g z))) :
    ∃ G : ℂ → ℂ, IsLaguerrePolya G ∧ Set.EqOn G g (Metric.ball 0 r) := by
  let γ : ℕ → ℝ := fun j => (iteratedDeriv j φ 0).re
  let F (n : ℕ) := ((rescaledJensenPolynomial n γ).map ofRealHom).differentialApply ψ
  have hF (n : ℕ) : IsLaguerrePolya (F n) := by
    apply hψ.differentialApply
    rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
    exact (hφ.jensenPolynomial_splits n).comp_of_natDegree_le_one
      ((natDegree_C_mul_le _ _).trans (by simp))
  apply exists_isLaguerrePolya_eqOn_of_tendsto hF
  intro z hz
  apply tendsto_differentialApply_rescaledJensenPolynomial γ ψ z (g z)
  have hγ (j : ℕ) : (γ j : ℂ) = iteratedDeriv j φ 0 :=
    ofReal_re_iteratedDeriv_zero hφ.conj j
  simpa only [hγ] using hseries z hz

end RealRooted
