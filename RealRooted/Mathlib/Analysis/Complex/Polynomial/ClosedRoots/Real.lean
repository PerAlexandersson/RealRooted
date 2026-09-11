module

public import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
public import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots

public section

noncomputable section

open Filter Topology

namespace Polynomial

/-- Pointwise limits of real splitting polynomials with uniformly bounded
degree are zero or split. -/
theorem eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    {p : ℕ → ℝ[X]} {p₀ : ℝ[X]} {N : ℕ}
    (hdeg : ∀ n, (p n).natDegree ≤ N)
    (hsplit : ∀ n, p n = 0 ∨ (p n).Splits)
    (heval : ∀ z : ℂ, Tendsto
      (fun n => ((p n).map Complex.ofRealHom).eval z) atTop
        (𝓝 ((p₀.map Complex.ofRealHom).eval z))) :
    p₀ = 0 ∨ p₀.Splits := by
  by_cases hp₀ : p₀ = 0
  · exact Or.inl hp₀
  right
  apply splits_of_all_roots_real
  intro z hz
  have hzroots : z ∈ (p₀.map Complex.ofRealHom).roots :=
    (mem_roots (Polynomial.map_ne_zero hp₀)).mpr hz
  have hreal : z ∈ {z : ℂ | z.im = 0} :=
    roots_mem_of_tendsto_eval_of_natDegree_le
      (isClosed_eq Complex.continuous_im continuous_const)
      (fun n => by
        simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective] using hdeg n)
      (fun n r hr => by
        rcases hsplit n with hpzero | hpsplits
        · rw [hpzero] at hr
          simp at hr
        · rw [hpsplits.roots_map Complex.ofRealHom, Multiset.mem_map] at hr
          obtain ⟨s, -, rfl⟩ := hr
          simp)
      heval z hzroots
  exact hreal

end Polynomial
