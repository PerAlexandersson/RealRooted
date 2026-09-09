import RealRooted.ClassicalHurwitzMatrix.Stability
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots

/-!
# Closed limits of Hurwitz-stable polynomials

This file packages the closed-root transport theorem for fixed-degree monic
polynomial sequences as a right-half-plane stability result.
-/

open Polynomial Filter Topology

namespace RealRooted

/-- A nonzero pointwise limit of fixed-degree monic right-half-plane-stable
polynomials is right-half-plane stable. -/
theorem isRightHalfPlaneStable_of_monic_tendsto_eval
    {P : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hp₀ : p₀ ≠ 0)
    (hm : ∀ k, (P k).Monic)
    (hdegree : ∀ k, (P k).natDegree = N)
    (hstable : ∀ k, IsRightHalfPlaneStable (P k))
    (heval : ∀ z : ℂ, Tendsto (fun k => (P k).eval z) atTop (𝓝 (p₀.eval z))) :
    IsRightHalfPlaneStable p₀ := by
  intro z hz hroot
  have hzroots : z ∈ p₀.roots := mem_roots'.mpr ⟨hp₀, hroot⟩
  have hzclosed : z ∈ {w : ℂ | w.re ≤ 0} := by
    apply Polynomial.roots_mem_of_tendsto_eval (N := N)
      (isClosed_le Complex.continuous_re continuous_const) hm hdegree
      (fun k w hw => ?_) heval z hzroots
    exact le_of_not_gt fun hwre => hstable k w hwre (mem_roots'.mp hw).2
  exact (not_le_of_gt hz) hzclosed

end RealRooted
