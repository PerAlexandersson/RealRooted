import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Coefficientwise limits of powers of power series

This file adds a small compatibility lemma for the product topology on power
series. It is stated in the namespace of the corresponding Mathlib API.
-/

open Filter Topology
open scoped PowerSeries.WithPiTopology

namespace PowerSeries.WithPiTopology

/-- Coefficientwise convergence of power series implies coefficientwise
convergence of every fixed power. -/
theorem tendsto_coeff_pow_of_coeff_tendsto
    {R : Type*} [TopologicalSpace R] [Semiring R] [IsTopologicalSemiring R]
    {ι : Type*} {l : Filter ι} {f : ι → PowerSeries R} {g : PowerSeries R}
    (hcoeff : ∀ i, Tendsto (fun k => PowerSeries.coeff i (f k)) l
      (𝓝 (PowerSeries.coeff i g))) (m n : ℕ) :
    Tendsto (fun k => PowerSeries.coeff n ((f k) ^ m)) l
      (𝓝 (PowerSeries.coeff n (g ^ m))) := by
  have hfg : Tendsto f l (𝓝 g) :=
    (tendsto_iff_coeff_tendsto R f l g).2 hcoeff
  exact (continuous_coeff R n).continuousAt.tendsto.comp (hfg.pow m)

end PowerSeries.WithPiTopology
