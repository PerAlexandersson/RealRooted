import RealRooted.InterlacingClosure
import RealRooted.Mathlib.LinearAlgebra.Matrix.SpectrumClosed

/-!
# Matrix characteristic-polynomial interlacing closure

This file transports weak interlacing through entrywise limits of a pair of
fixed-size real matrices. Characteristic-polynomial coefficient continuity is
the only matrix-specific input; polynomial interlacing closure remains in
`RealRooted.InterlacingClosure`.
-/

open Filter Topology

namespace Matrix

/-- Entrywise limits preserve weak interlacing between characteristic
polynomials of matrices whose sizes differ by one. -/
theorem charpoly_interlaces_of_tendsto {n : ℕ}
    {P : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {Q : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {P₀ : Matrix (Fin n) (Fin n) ℝ}
    {Q₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hP : ∀ i j, Tendsto (fun k => P k i j) atTop (𝓝 (P₀ i j)))
    (hQ : ∀ i j, Tendsto (fun k => Q k i j) atTop (𝓝 (Q₀ i j)))
    (hInterlaces : ∀ k,
      RealRooted.Interlaces (P k).charpoly (Q k).charpoly) :
    RealRooted.Interlaces P₀.charpoly Q₀.charpoly := by
  apply RealRooted.interlaces_of_monic_of_coeff_tendsto
      (n := n) (p := fun k => (P k).charpoly) (q := fun k => (Q k).charpoly)
  · exact fun k => (P k).charpoly_monic
  · exact fun k => (Q k).charpoly_monic
  · exact P₀.charpoly_monic
  · exact Q₀.charpoly_monic
  · exact fun k => by simpa only [Fintype.card_fin] using
      (P k).charpoly_natDegree_eq_dim
  · exact fun k => by simpa only [Fintype.card_fin] using
      (Q k).charpoly_natDegree_eq_dim
  · simpa only [Fintype.card_fin] using P₀.charpoly_natDegree_eq_dim
  · simpa only [Fintype.card_fin] using Q₀.charpoly_natDegree_eq_dim
  · exact hInterlaces
  · exact fun i => tendsto_charpoly_coeff hP i
  · exact fun i => tendsto_charpoly_coeff hQ i

end Matrix
