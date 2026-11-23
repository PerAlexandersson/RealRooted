module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import RealRooted.Mathlib.Analysis.Complex.CompactJets
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DifferentialMultiplicity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Eventual simplicity of finite differential images on compact sets

Cardon--de Gaston (2005), Lemma 6, follows from a uniform finite nonvanishing
jet and finite-symbol multiplicity descent. The statement here applies to any
real-rooted polynomial symbols whose degrees grow. No growth assumption on
the entire input is needed. An identically zero output is explicitly excluded.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

/-- On a fixed compact real set, every sufficiently high-degree split
finite symbol gives simple zeros in its nonzero differential image of an LP input. -/
theorem IsLaguerrePolya.exists_degree_bound_differentialApply_simple {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f ≠ 0) {K : Set ℝ} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ q : ℝ[X], q.Splits → N ≤ q.natDegree →
      (∃ z, (q.map ofRealHom).differentialApply f z ≠ 0) →
      ∀ x ∈ K, (q.map ofRealHom).differentialApply f (x : ℂ) = 0 →
        deriv ((q.map ofRealHom).differentialApply f) (x : ℂ) ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_uniform_iteratedDeriv_ne_zero hf.differentiable hf0
    (hK.image continuous_ofReal)
  refine ⟨N, ?_⟩
  intro q hq hdegree hne x hx hzero
  apply hf.deriv_differentialApply_ne_zero_of_jet hq hne ?_ hzero
  obtain ⟨k, hk, hkn⟩ := hN (x : ℂ) ⟨x, hx, rfl⟩
  exact ⟨k, by lia, hkn⟩

/-- Along any filter, split symbols with degrees tending to infinity eventually
have only simple zeros on each compact real set, whenever the output is nonzero. -/
theorem IsLaguerrePolya.eventually_differentialApply_simple {ι : Type*} {l : Filter ι}
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (hf0 : f ≠ 0)
    {q : ι → ℝ[X]} (hq : ∀ i, (q i).Splits)
    (hdegree : Tendsto (fun i => (q i).natDegree) l atTop)
    {K : Set ℝ} (hK : IsCompact K) :
    ∀ᶠ i in l, (∃ z, ((q i).map ofRealHom).differentialApply f z ≠ 0) →
      ∀ x ∈ K, ((q i).map ofRealHom).differentialApply f (x : ℂ) = 0 →
        deriv (((q i).map ofRealHom).differentialApply f) (x : ℂ) ≠ 0 := by
  obtain ⟨N, hN⟩ := hf.exists_degree_bound_differentialApply_simple hf0 hK
  filter_upwards [hdegree.eventually (eventually_ge_atTop N)] with i hi
  exact hN (q i) (hq i) hi

end RealRooted
