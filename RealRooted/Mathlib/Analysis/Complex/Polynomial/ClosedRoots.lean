import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Closed conditions on roots of polynomial limits

Pointwise limits of fixed-degree monic complex polynomials preserve any closed
condition satisfied by all roots of the approximating polynomials.
-/

open Filter Topology

namespace Polynomial

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

/-- Roots of a limit polynomial stay in any closed set that contains the roots
along the sequence, provided evaluations converge pointwise and degrees are
constant. -/
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

end Polynomial
