import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

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

/-- Linear factors avoiding a ball around `μ` keep the evaluation there large. -/
private lemma le_norm_eval_multiset (μ : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ s : Multiset ℂ, (∀ r ∈ s, ε ≤ ‖μ - r‖) →
      ε ^ Multiset.card s ≤ ‖(s.map fun r => (X : ℂ[X]) - C r).prod.eval μ‖ := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    intro hfar
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul, norm_mul,
      Multiset.card_cons, pow_succ, mul_comm (ε ^ Multiset.card s) ε]
    have ha : ε ≤ ‖μ - a‖ := hfar a (Multiset.mem_cons_self a s)
    have hs := ih fun r hr => hfar r (Multiset.mem_cons_of_mem hr)
    have h1 : ‖Polynomial.eval μ (X - C a)‖ = ‖μ - a‖ := by simp
    rw [h1]
    exact mul_le_mul ha hs (pow_nonneg hε _) (norm_nonneg _)

/-- A monic complex polynomial whose roots all stay at distance at least `ε`
from `μ` satisfies `ε ^ natDegree ≤ ‖p.eval μ‖`. -/
theorem le_norm_eval_of_forall_le_norm_sub {p : ℂ[X]} (hm : p.Monic) {μ : ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hfar : ∀ r ∈ p.roots, ε ≤ ‖μ - r‖) :
    ε ^ p.natDegree ≤ ‖p.eval μ‖ := by
  have hcard : Multiset.card p.roots = p.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hfact := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
  calc ε ^ p.natDegree = ε ^ Multiset.card p.roots := by rw [hcard]
    _ ≤ ‖(p.roots.map fun r => (X : ℂ[X]) - C r).prod.eval μ‖ :=
        le_norm_eval_multiset μ hε p.roots hfar
    _ = ‖p.eval μ‖ := by rw [hfact]

/-- **Roots of a limit polynomial stay in any closed set that contains the
roots along the sequence**, provided the evaluations converge pointwise and
degrees are constant. -/
theorem roots_mem_of_tendsto_eval {S : Set ℂ} (hS : IsClosed S)
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hm : ∀ k, (p k).Monic) (hdeg : ∀ k, (p k).natDegree = N)
    (hroots : ∀ k, ∀ r ∈ (p k).roots, r ∈ S)
    (heval : ∀ μ : ℂ, Tendsto (fun k => (p k).eval μ) atTop (𝓝 (p₀.eval μ))) :
    ∀ μ ∈ p₀.roots, μ ∈ S := by
  intro μ hμ
  by_contra hμS
  -- an `ε`-ball around `μ` misses `S`
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball μ ε ⊆ Sᶜ :=
    Metric.isOpen_iff.mp hS.isOpen_compl μ hμS
  have hfar : ∀ k, ∀ r ∈ (p k).roots, ε ≤ ‖μ - r‖ := by
    intro k r hr
    by_contra hlt
    have hmem : r ∈ Metric.ball μ ε := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm]
      exact lt_of_not_ge hlt
    exact (hball hmem) (hroots k r hr)
  have hlow : ∀ k, ε ^ N ≤ ‖(p k).eval μ‖ := fun k =>
    hdeg k ▸ le_norm_eval_of_forall_le_norm_sub (hm k) hε.le (hfar k)
  have h0 : p₀.eval μ = 0 := (mem_roots'.mp hμ).2
  have hlim : Tendsto (fun k => ‖(p k).eval μ‖) atTop (𝓝 0) := by
    simpa [h0] using (heval μ).norm
  have hev : ∀ᶠ k in atTop, ‖(p k).eval μ‖ < ε ^ N :=
    hlim.eventually (gt_mem_nhds (pow_pos hε N))
  obtain ⟨k, hk⟩ := hev.exists
  exact absurd (hlow k) (not_le.mpr hk)

/-- **Closed spectral conditions pass to entrywise limits of real matrices.** -/
theorem charpoly_roots_mem_of_tendsto {S : Set ℂ} (hS : IsClosed S)
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A₀ i j)))
    (hroots : ∀ k, ∀ μ ∈ ((A k).map (algebraMap ℝ ℂ)).charpoly.roots, μ ∈ S) :
    ∀ μ ∈ (A₀.map (algebraMap ℝ ℂ)).charpoly.roots, μ ∈ S := by
  refine roots_mem_of_tendsto_eval (N := n) hS (fun k => charpoly_monic _)
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
