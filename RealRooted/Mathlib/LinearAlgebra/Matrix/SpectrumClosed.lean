import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots

/-!
# Closed spectral conditions pass to matrix limits

If a sequence of real square matrices converges entrywise and every matrix in
the sequence has all its complex eigenvalues in a closed set `S`, then so does
the limit.  In particular, having real nonnegative spectrum is preserved under
entrywise limits (`charpoly_roots_nonneg_real_of_tendsto`).

This is the "root continuity" input Gantmacher-Krein needs, in a form that
avoids multiset root topology entirely.  The proof is elementary: if `μ` is a
root of the limit characteristic polynomial but every root of every
`charpoly (A k)` stays at distance at least `ε` from `μ`, then the linear
factorization of a monic polynomial over `ℂ` gives
`‖(charpoly (A k)).eval μ‖ ≥ ε ^ n`, while
`(charpoly (A k)).eval μ = det (scalar μ - A k) → det (scalar μ - A₀) = 0`
by continuity of the determinant in the entries — a contradiction.
-/

open Polynomial Filter Topology Finset

namespace Matrix

variable {n : ℕ}

/-- The determinant is continuous along entrywise-converging sequences. -/
theorem tendsto_det {M : ℕ → Matrix (Fin n) (Fin n) ℂ} {M₀ : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, Tendsto (fun k => M k i j) atTop (𝓝 (M₀ i j))) :
    Tendsto (fun k => (M k).det) atTop (𝓝 M₀.det) := by
  simp only [Matrix.det_apply]
  refine tendsto_finsetSum _ fun σ _ => ?_
  exact Tendsto.const_smul (tendsto_finsetProd _ fun i _ => h (σ i) i) _

/-- Compatibility forwarding theorem for the polynomial root-separation bound. -/
theorem le_norm_eval_of_forall_le_norm_sub {p : ℂ[X]} (hm : p.Monic) {μ : ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hfar : ∀ r ∈ p.roots, ε ≤ ‖μ - r‖) :
    ε ^ p.natDegree ≤ ‖p.eval μ‖ :=
  Polynomial.le_norm_eval_of_forall_le_norm_sub hm hε hfar

/-- Compatibility forwarding theorem for closed conditions on polynomial roots. -/
theorem roots_mem_of_tendsto_eval {S : Set ℂ} (hS : IsClosed S)
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hm : ∀ k, (p k).Monic) (hdeg : ∀ k, (p k).natDegree = N)
    (hroots : ∀ k, ∀ r ∈ (p k).roots, r ∈ S)
    (heval : ∀ μ : ℂ, Tendsto (fun k => (p k).eval μ) atTop (𝓝 (p₀.eval μ))) :
    ∀ μ ∈ p₀.roots, μ ∈ S :=
  Polynomial.roots_mem_of_tendsto_eval hS hm hdeg hroots heval

/-- **Closed spectral conditions pass to entrywise limits of real matrices.** -/
theorem charpoly_roots_mem_of_tendsto {S : Set ℂ} (hS : IsClosed S)
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A₀ i j)))
    (hroots : ∀ k, ∀ μ ∈ ((A k).map (algebraMap ℝ ℂ)).charpoly.roots, μ ∈ S) :
    ∀ μ ∈ (A₀.map (algebraMap ℝ ℂ)).charpoly.roots, μ ∈ S := by
  refine Polynomial.roots_mem_of_tendsto_eval (N := n) hS (fun k => charpoly_monic _)
    (fun k => (charpoly_natDegree_eq_dim ((A k).map (algebraMap ℝ ℂ))).trans
      (Fintype.card_fin n))
    hroots fun μ => ?_
  simp only [eval_charpoly]
  apply tendsto_det
  intro i j
  have hentry : ∀ B : Matrix (Fin n) (Fin n) ℝ,
      (Matrix.scalar (Fin n) μ - B.map (algebraMap ℝ ℂ)) i j
        = (if i = j then μ else 0) - ((B i j : ℝ) : ℂ) := by
    intro B
    simp [Matrix.scalar, Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply,
      Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [hentry]
  exact Tendsto.sub tendsto_const_nhds
    ((Complex.continuous_ofReal.tendsto _).comp (hconv i j))

/-- **Real nonnegative spectrum passes to entrywise limits**: if every matrix
in an entrywise-converging sequence has all complex eigenvalues real and
nonnegative, so does the limit.  This is the root-continuity input for
Gantmacher-Krein. -/
theorem charpoly_roots_nonneg_real_of_tendsto
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A₀ i j)))
    (hroots : ∀ k, ∀ μ ∈ ((A k).map (algebraMap ℝ ℂ)).charpoly.roots,
      ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = μ) :
    ∀ μ ∈ (A₀.map (algebraMap ℝ ℂ)).charpoly.roots,
      ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = μ := by
  have hS : IsClosed ((fun r : ℝ => (r : ℂ)) '' Set.Ici 0) :=
    (Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici)
  have h := charpoly_roots_mem_of_tendsto hS hconv (fun k μ hμ => ?_)
  · intro μ hμ
    obtain ⟨r, hr, hrμ⟩ := h μ hμ
    exact ⟨r, hr, hrμ⟩
  · obtain ⟨r, hr, hrμ⟩ := hroots k μ hμ
    exact ⟨r, hr, hrμ⟩

end Matrix
