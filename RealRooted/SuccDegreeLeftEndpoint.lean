/-
# Succ-degree left endpoint via root continuity

This file proves, by a direct complex-root-continuity ("escaping root")
argument, that in a positive-combination family `f + μ g` with
`deg g = deg f + 1`, the lower-degree member `f` splits.
-/
import RealRooted.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace RealRooted

/-- Complex evaluation of a split real polynomial as a product over its real
roots. -/
lemma norm_aeval_eq_prod_norm_roots {p : ℝ[X]} (hp : p.Splits) (z : ℂ) :
    ‖(Polynomial.aeval z) p‖ =
      |p.leadingCoeff| * (p.roots.map (fun r : ℝ => ‖z - (r : ℂ)‖)).prod := by
  have h_prod :
      p = Polynomial.C p.leadingCoeff *
        Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots) := by
    convert Polynomial.Splits.eq_prod_roots hp
  conv_lhs =>
    rw [h_prod]
    simp +decide [norm_mul]
    ring_nf
  induction p.roots using Multiset.induction <;> norm_num at *
  tauto

set_option linter.flexible false in
/-- Escaping-root estimate: for a split real polynomial `p`, a complex point
`z` with `z.im ≠ 0`, and any root `r` of `p`, the distance `‖z - r‖` is
controlled by `‖p(z)‖`, since the other `card - 1` factors are bounded below by
`|z.im|`. -/
lemma leadingCoeff_mul_pow_im_mul_norm_sub_le_norm_aeval
    {p : ℝ[X]} (hp : p.Splits) {z : ℂ} (hz : z.im ≠ 0)
    {r : ℝ} (hr : r ∈ p.roots) :
    |p.leadingCoeff| * |z.im| ^ (p.roots.card - 1) * ‖z - (r : ℂ)‖
      ≤ ‖(Polynomial.aeval z) p‖ := by
  have hRHS :
      ‖(Polynomial.aeval z) p‖ =
        |p.leadingCoeff| * (p.roots.map (fun r : ℝ => ‖z - (r : ℂ)‖)).prod := by
    convert norm_aeval_eq_prod_norm_roots hp z using 1
  rw [hRHS]
  have h_prod_bound :
      |z.im| ^ ((p.roots.erase r).card) ≤
        ((p.roots.erase r).map (fun s : ℝ => ‖z - (s : ℂ)‖)).prod := by
    have h_prod_bound :
        ∀ (m : Multiset ℝ),
          (∀ s ∈ m, ‖z - (s : ℂ)‖ ≥ |z.im|) →
            |z.im| ^ m.card ≤ (m.map (fun s : ℝ => ‖z - (s : ℂ)‖)).prod := by
      intro m hm
      induction m using Multiset.induction <;> simp_all +decide [pow_succ']
      exact mul_le_mul hm.1 ‹_› (by positivity) (by positivity)
    exact h_prod_bound _ fun s hs => by
      simpa using Complex.abs_im_le_norm (z - s)
  rw [← Multiset.cons_erase hr, Multiset.map_cons, Multiset.prod_cons]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left h_prod_bound
      (by positivity : 0 ≤ |p.leadingCoeff| * ‖z - r‖)

/-- Uniform bound on the next coefficient of a split real polynomial, obtained
from the escaping estimate and Vieta's formula
`nextCoeff = -leadingCoeff * roots.sum`. -/
lemma abs_nextCoeff_le_of_splits
    {p : ℝ[X]} (hp : p.Splits) {z : ℂ} (hz : z.im ≠ 0)
    (hlc : 0 < p.leadingCoeff) :
    |p.nextCoeff| ≤
      p.leadingCoeff * p.roots.card *
        (‖z‖ + ‖(Polynomial.aeval z) p‖ /
          (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) := by
  have h_vieta : p.nextCoeff = -p.leadingCoeff * Multiset.sum p.roots :=
    hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have h_escape_bound :
      ∀ r ∈ p.roots,
        ‖(r : ℂ)‖ ≤
          ‖z‖ + ‖(Polynomial.aeval z) p‖ /
            (p.leadingCoeff * |z.im| ^ (p.roots.card - 1)) := by
    intro r hr
    have h_escape_bound :
        ‖(z - (r : ℂ))‖ ≤
          ‖(Polynomial.aeval z) p‖ /
            (p.leadingCoeff * |z.im| ^ (p.roots.card - 1)) := by
      have := leadingCoeff_mul_pow_im_mul_norm_sub_le_norm_aeval hp hz hr
      rw [le_div_iff₀] <;> first
      | positivity
      | rw [abs_of_pos hlc] at this
        linarith
    have := norm_sub_le (z : ℂ) (z - r)
    norm_num at *
    linarith
  have h_sum_escape_bound :
      ‖p.roots.sum‖ ≤
        p.roots.card *
          (‖z‖ + ‖(Polynomial.aeval z) p‖ /
            (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) := by
    have h_sum_escape_bound :
        ∀ {s : Multiset ℝ},
          (∀ r ∈ s,
            ‖(r : ℂ)‖ ≤
              ‖z‖ + ‖(Polynomial.aeval z) p‖ /
                (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) →
          ‖s.sum‖ ≤
            s.card *
              (‖z‖ + ‖(Polynomial.aeval z) p‖ /
                (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) := by
      intro s hs
      induction s using Multiset.induction <;> norm_num at *
      grind
    exact h_sum_escape_bound h_escape_bound
  simp_all +decide [mul_assoc, abs_mul, abs_neg, abs_of_pos hlc]

/-- A positive quantity cannot be bounded by `μ * M` for every `μ > 0`. -/
lemma false_of_forall_pos_mul_le {a M : ℝ} (ha : 0 < a)
    (h : ∀ μ : ℝ, 0 < μ → a ≤ μ * M) : False := by
  exact absurd
    (h (a / (2 * |M| + 1)) (by positivity))
    (by
      cases abs_cases M <;>
        nlinarith [mul_div_cancel₀ a (by positivity : (2 * |M| + 1) ≠ 0)])

set_option linter.flexible false in
/-- The per-`μ` escaping-root inequality.  Under the succ-degree family
hypotheses, for a complex root `z` of `f` with `z.im ≠ 0`, the next coefficient
of `f + μ g` is bounded by `μ` times a constant independent of `μ`. -/
lemma key_family_ineq {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (_hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1)
    {z : ℂ} (hz : z.im ≠ 0) (hzf : (Polynomial.aeval z) f = 0)
    {μ : ℝ} (hμ : 0 < μ) :
    |f.leadingCoeff + μ * g.coeff f.natDegree|
      ≤ μ * (g.leadingCoeff * (f.natDegree + 1) *
        (‖z‖ + ‖(Polynomial.aeval z) g‖ /
          (g.leadingCoeff * |z.im| ^ f.natDegree))) := by
  have := @abs_nextCoeff_le_of_splits (f + Polynomial.C μ * g) ?_ z ?_ ?_
  · convert this using 1
    · rw [Polynomial.nextCoeff]
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt] <;>
        norm_num [hsucc, hμ.ne']
      all_goals rw [Polynomial.natDegree_C_mul] <;> aesop
    · have hcard : (f + Polynomial.C μ * g).roots.card = f.natDegree + 1 := by
        have := Polynomial.Splits.natDegree_eq_card_roots (hfamily hμ |>.2)
        rw [← this, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
        all_goals rw [Polynomial.natDegree_C_mul] <;> aesop
      rw [Polynomial.leadingCoeff_add_of_degree_lt] <;>
        simp_all +decide [Polynomial.degree_eq_natDegree (show g ≠ 0 from by aesop_cat)]
      · norm_num [abs_of_pos hμ, mul_assoc, mul_div_mul_left, hμ.ne']
      · rw [Polynomial.degree_C hμ.ne']
        norm_num
        exact lt_of_le_of_lt Polynomial.degree_le_natDegree
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
  · exact hfamily hμ |>.2
  · assumption
  · rw [Polynomial.leadingCoeff_add_of_degree_lt] <;>
      simp_all +decide [Polynomial.degree_eq_natDegree (show g ≠ 0 by aesop)]
    rw [Polynomial.degree_C] <;> norm_num [hμ.ne']
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))

/-- If every member `f + C μ * g`, `μ > 0`, of the affine family is
real-rooted, both `f` and `g` have positive leading coefficients, and
`g.natDegree = f.natDegree + 1`, then the lower-degree member `f` splits. -/
theorem splits_of_add_C_mul_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits := by
  refine Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _) ?_
  intro z hz_mem
  have hzf : (Polynomial.aeval (R := ℝ) z f) = 0 := by
    aesop
  by_contra hz_im_ne_zero
  have hz_im : z.im ≠ 0 := by
    exact fun h => hz_im_ne_zero <| ⟨z.re, by simp [Complex.ext_iff, h]⟩
  have h_bound :
      ∀ μ : ℝ, 0 < μ →
        f.leadingCoeff ≤
          μ * (g.leadingCoeff * (f.natDegree + 1) *
            (‖z‖ + ‖(Polynomial.aeval (R := ℝ) z) g‖ /
              (g.leadingCoeff * |z.im| ^ f.natDegree)) +
            |g.coeff f.natDegree|) := by
    intro μ hμ_pos
    have h_bound :
        |f.leadingCoeff + μ * g.coeff f.natDegree| ≤
          μ * (g.leadingCoeff * (f.natDegree + 1) *
            (‖z‖ + ‖(Polynomial.aeval (R := ℝ) z) g‖ /
              (g.leadingCoeff * |z.im| ^ f.natDegree))) := by
      convert key_family_ineq hfamily hf_pos hg_pos hsucc hz_im hzf hμ_pos using 1
    cases abs_cases (g.coeff f.natDegree) <;> nlinarith [abs_le.mp h_bound]
  exact false_of_forall_pos_mul_le hf_pos h_bound

end RealRooted
