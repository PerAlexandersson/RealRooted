module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

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

/-- If all roots avoid an `ε`-ball around `μ`, evaluations at any two points
are related by a bound depending only on an upper bound for the degree. -/
theorem norm_eval_le_pow_mul_norm_eval_of_forall_le_norm_sub
    {p : ℂ[X]} {μ t : ℂ} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hdeg : p.natDegree ≤ N)
    (hfar : ∀ r ∈ p.roots, ε ≤ ‖μ - r‖) :
    ‖p.eval t‖ ≤ (1 + ‖t - μ‖ / ε) ^ N * ‖p.eval μ‖ := by
  let C : ℝ := 1 + ‖t - μ‖ / ε
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hε.le)
  have hfactor (r : ℂ) (hr : r ∈ p.roots) :
      ‖t - r‖ ≤ C * ‖μ - r‖ := by
    calc
      ‖t - r‖ = ‖(t - μ) + (μ - r)‖ := by ring_nf
      _ ≤ ‖t - μ‖ + ‖μ - r‖ := norm_add_le _ _
      _ = (‖t - μ‖ / ε) * ε + ‖μ - r‖ := by
        rw [div_mul_cancel₀ _ hε.ne']
      _ ≤ (‖t - μ‖ / ε) * ‖μ - r‖ + ‖μ - r‖ := by
        gcongr
        exact hfar r hr
      _ = C * ‖μ - r‖ := by ring
  have hprod_const (s : Multiset ℂ) :
      (s.map fun r => C * ‖μ - r‖).prod =
        C ^ s.card * (s.map fun r => ‖μ - r‖).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons r s ih => simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card ≤ N := by
    rw [← hsplits.natDegree_eq_card_roots]
    exact hdeg
  rw [hsplits.eval_eq_prod_roots, hsplits.eval_eq_prod_roots, norm_mul, norm_mul]
  have hprod : ‖(p.roots.map (t - ·)).prod‖ ≤
      C ^ N * ‖(p.roots.map (μ - ·)).prod‖ := by
    calc
      ‖(p.roots.map (t - ·)).prod‖ =
        (p.roots.map fun r => ‖t - r‖).prod := by
          simpa [Multiset.map_map] using
            (map_multiset_prod (normHom.toMonoidHom : ℂ →* ℝ)
              (p.roots.map (t - ·)))
      _ ≤ (p.roots.map fun r => C * ‖μ - r‖).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => norm_nonneg _)
          (fun r hr => hfactor r hr)
      _ = C ^ p.roots.card * (p.roots.map fun r => ‖μ - r‖).prod :=
        hprod_const p.roots
      _ ≤ C ^ N * (p.roots.map fun r => ‖μ - r‖).prod := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hcard)
          (Multiset.prod_map_nonneg fun _ _ => norm_nonneg _)
      _ = C ^ N * ‖(p.roots.map (μ - ·)).prod‖ := by
        congr 1
        symm
        simpa [Multiset.map_map] using
          (map_multiset_prod (normHom.toMonoidHom : ℂ →* ℝ)
            (p.roots.map (μ - ·)))
  calc
    ‖p.leadingCoeff‖ * ‖(p.roots.map (t - ·)).prod‖ ≤
        ‖p.leadingCoeff‖ *
          (C ^ N * ‖(p.roots.map (μ - ·)).prod‖) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (1 + ‖t - μ‖ / ε) ^ N *
        (‖p.leadingCoeff‖ * ‖(p.roots.map (μ - ·)).prod‖) := by
      dsimp [C]
      ring

/-- Roots of a limit polynomial stay in any closed set that contains the roots
along a sequence of uniformly bounded degree, provided evaluations converge
pointwise. -/
theorem roots_mem_of_tendsto_eval_of_natDegree_le
    {S : Set ℂ} (hS : IsClosed S)
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hdeg : ∀ k, (p k).natDegree ≤ N)
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
  have h0 : p₀.eval μ = 0 := (mem_roots'.mp hμ).2
  have hp₀ne : p₀ ≠ 0 := (mem_roots'.mp hμ).1
  obtain ⟨t, ht⟩ : ∃ t : ℂ, p₀.eval t ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hp₀ne
    exact Polynomial.funext fun x => by simpa using hnone x
  have hlimμ : Tendsto (fun k => ‖(p k).eval μ‖) atTop (𝓝 0) := by
    simpa [h0] using (heval μ).norm
  have hlimBound : Tendsto
      (fun k => (1 + ‖t - μ‖ / ε) ^ N * ‖(p k).eval μ‖)
      atTop (𝓝 0) := by
    simpa using hlimμ.const_mul ((1 + ‖t - μ‖ / ε) ^ N)
  have hlimt : Tendsto (fun k => ‖(p k).eval t‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun k => norm_eval_le_pow_mul_norm_eval_of_forall_le_norm_sub
        hε (hdeg k) (hfar k)) hlimBound
  have htzero : ‖p₀.eval t‖ = 0 :=
    tendsto_nhds_unique (heval t).norm hlimt
  exact ht (norm_eq_zero.mp htzero)

/-- Compatibility form for fixed-degree monic sequences. -/
theorem roots_mem_of_tendsto_eval {S : Set ℂ} (hS : IsClosed S)
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]} {N : ℕ}
    (hm : ∀ k, (p k).Monic) (hdeg : ∀ k, (p k).natDegree = N)
    (hroots : ∀ k, ∀ r ∈ (p k).roots, r ∈ S)
    (heval : ∀ μ : ℂ, Tendsto (fun k => (p k).eval μ) atTop (𝓝 (p₀.eval μ))) :
    ∀ μ ∈ p₀.roots, μ ∈ S := by
  exact roots_mem_of_tendsto_eval_of_natDegree_le hS
    (fun k => by
      by_cases hp : p k = 0
      · exact ((hm k).ne_zero hp).elim
      · exact (hdeg k).le)
    hroots heval

end Polynomial
