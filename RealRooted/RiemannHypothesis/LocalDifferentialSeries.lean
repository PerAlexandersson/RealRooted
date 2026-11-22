module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.RiemannHypothesis
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialLocal
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# Locally convergent xi differential series under RH

O'Sullivan's Theorem 3.6 applies to every derivative of the square-variable xi
function under Mathlib's Riemann hypothesis. Xi may be either the differential
symbol or the entire target. Ordinary pointwise convergence on a disk suffices;
no growth bound or absolute convergence is assumed here.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- Under RH, every shifted xi differential symbol sends a Laguerre--Pólya
target to an entire Laguerre--Pólya extension whenever its series converges
pointwise on a disk. -/
theorem exists_eqOn_riemannXi_differential_series (hRH : RiemannHypothesis) (n : ℕ)
    {ψ g : ℂ → ℂ} (hψ : IsLaguerrePolya ψ) {r : ℝ}
    (hseries : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun d => ∑ j ∈ Finset.range d,
        (riemannXiCoeff (n + j) : ℂ) * iteratedDeriv j ψ z / j.factorial)
        atTop (𝓝 (g z))) :
    ∃ G : ℂ → ℂ, IsLaguerrePolya G ∧ Set.EqOn G g (Metric.ball 0 r) := by
  have hξ := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  apply hξ.exists_eqOn_differential_series hψ
  intro z hz
  simpa only [ofReal_riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using hseries z hz

/-- Under RH, a Laguerre--Pólya differential symbol acting on any derivative
of xi has a Laguerre--Pólya entire extension as soon as its ordinary series
converges pointwise on a disk. -/
theorem exists_eqOn_differential_series_riemannXi (hRH : RiemannHypothesis) (n : ℕ)
    {φ g : ℂ → ℂ} (hφ : IsLaguerrePolya φ) {r : ℝ}
    (hseries : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun d => ∑ j ∈ Finset.range d,
        iteratedDeriv j φ 0 * iteratedDeriv (n + j) riemannXiTheta z / j.factorial)
        atTop (𝓝 (g z))) :
    ∃ G : ℂ → ℂ, IsLaguerrePolya G ∧ Set.EqOn G g (Metric.ball 0 r) := by
  apply hφ.exists_eqOn_differential_series
    ((riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n)
  intro z hz
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm]
    using hseries z hz

end RealRooted
