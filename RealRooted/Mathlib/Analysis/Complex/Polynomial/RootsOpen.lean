module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Vieta

import Mathlib.Tactic

public section

/-!
# Openness of strict upper-half-plane root location

This file proves that having all roots in the open upper half-plane is open
among complex polynomials of bounded degree. The proof was found by Aristotle
(Harmonic).
-/

namespace Polynomial

/-- For `r` in the open upper half-plane and `z` in the closed lower
half-plane, `‖z - r‖` grows at least linearly in `1 + ‖z‖`. -/
private lemma factor_bound {r z : ℂ} (hr : 0 < r.im) (hz : z.im ≤ 0) :
    r.im / (2 * (1 + ‖r‖)) * (1 + ‖z‖) ≤ ‖z - r‖ := by
  have h1 : r.im ≤ ‖z - r‖ := by
    have h := Complex.abs_im_le_norm (z - r)
    rw [Complex.sub_im, abs_sub_comm] at h
    exact le_trans (by rw [abs_of_pos (by linarith)]; linarith) h
  have h2 : ‖z‖ - ‖r‖ ≤ ‖z - r‖ := norm_sub_norm_le z r
  have h3 : r.im ≤ ‖r‖ :=
    le_trans (le_abs_self _) (Complex.abs_im_le_norm r)
  have hp : 0 < 2 * (1 + ‖r‖) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  have := norm_nonneg z
  rcases le_total ‖z‖ (2 * ‖r‖ + 1) with h | h
  · nlinarith
  · nlinarith

/-- Product version of `factor_bound` over upper-half-plane points. -/
private lemma prod_bound (z : ℂ) (hz : z.im ≤ 0) (s : Multiset ℂ)
    (hs : ∀ r ∈ s, 0 < r.im) :
    (s.map fun r => r.im / (2 * (1 + ‖r‖))).prod *
        (1 + ‖z‖) ^ Multiset.card s ≤
      (s.map fun r => ‖z - r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons,
      Multiset.card_cons, pow_succ]
    have ha := hs a (Multiset.mem_cons_self _ _)
    have ih' := ih (fun r hr => hs r (Multiset.mem_cons_of_mem hr))
    have hfa := factor_bound ha hz
    have h0 :
        0 ≤ (s.map fun r => r.im / (2 * (1 + ‖r‖))).prod *
          (1 + ‖z‖) ^ Multiset.card s := by
      apply mul_nonneg _ (by positivity)
      apply Multiset.prod_nonneg
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      have := hs r (Multiset.mem_cons_of_mem hr)
      positivity
    calc
      a.im / (2 * (1 + ‖a‖)) *
            (s.map fun r => r.im / (2 * (1 + ‖r‖))).prod *
          ((1 + ‖z‖) ^ Multiset.card s * (1 + ‖z‖)) =
          (a.im / (2 * (1 + ‖a‖)) * (1 + ‖z‖)) *
            ((s.map fun r => r.im / (2 * (1 + ‖r‖))).prod *
              (1 + ‖z‖) ^ Multiset.card s) := by ring
      _ ≤ ‖z - a‖ * (s.map fun r => ‖z - r‖).prod :=
        mul_le_mul hfa ih' h0 (norm_nonneg _)

/-- Polynomials of bounded degree sufficiently close coefficientwise to a
nonzero polynomial whose roots have positive imaginary part have the same
strict root location. -/
theorem roots_im_pos_of_coeff_near {f : ℂ[X]} (hf : f ≠ 0)
    (hroots : ∀ z ∈ f.roots, 0 < z.im) :
    ∃ δ > 0, ∀ g : ℂ[X], g.natDegree ≤ f.natDegree →
      (∀ j ≤ f.natDegree, ‖g.coeff j - f.coeff j‖ < δ) →
      ∀ z ∈ g.roots, 0 < z.im := by
  set q := f.natDegree
  set K := (f.roots.map fun r => r.im / (2 * (1 + ‖r‖))).prod
  have hK : 0 < K := by
    apply Multiset.prod_pos
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have := hroots r hr
    positivity
  have ha : 0 < ‖f.leadingCoeff‖ :=
    norm_pos_iff.2 (leadingCoeff_ne_zero.2 hf)
  refine ⟨‖f.leadingCoeff‖ * K / (q + 1), by positivity, ?_⟩
  intro g hg hc z hz
  by_contra hneg
  push Not at hneg
  have hroot : g.eval z = 0 := (mem_roots'.1 hz).2
  have hcard := IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := f)
  have hfz : ‖f.leadingCoeff‖ * K * (1 + ‖z‖) ^ q ≤ ‖f.eval z‖ := by
    have hn : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map norm).prod :=
      fun s => map_multiset_prod normHom s
    conv_rhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [eval_mul, eval_C, eval_multiset_prod, norm_mul, Multiset.map_map,
      hn, Multiset.map_map, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h := prod_bound z hneg f.roots hroots
    rw [hcard] at h
    convert h using 3
    simp
  have hd : (g - f).natDegree < q + 1 :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (by lia)
  have hgf : ‖(g - f).eval z‖ <
      ‖f.leadingCoeff‖ * K * (1 + ‖z‖) ^ q := by
    rw [eval_eq_sum_range' hd]
    calc
      ‖∑ i ∈ Finset.range (q + 1), (g - f).coeff i * z ^ i‖ ≤
          ∑ i ∈ Finset.range (q + 1), ‖(g - f).coeff i * z ^ i‖ :=
        norm_sum_le _ _
      _ < ∑ i ∈ Finset.range (q + 1),
          ‖f.leadingCoeff‖ * K / (q + 1) * (1 + ‖z‖) ^ q := by
        apply Finset.sum_lt_sum_of_nonempty (by simp)
        intro i hi
        rw [Finset.mem_range] at hi
        rw [norm_mul, norm_pow, coeff_sub]
        have h1 := hc i (by lia)
        have h2 : ‖z‖ ^ i ≤ (1 + ‖z‖) ^ q :=
          le_trans (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i)
            (pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by lia))
        have h3 : 0 < (1 + ‖z‖) ^ q := by positivity
        calc
          ‖g.coeff i - f.coeff i‖ * ‖z‖ ^ i ≤
              ‖g.coeff i - f.coeff i‖ * (1 + ‖z‖) ^ q :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ < _ := mul_lt_mul_of_pos_right h1 h3
      _ = ‖f.leadingCoeff‖ * K * (1 + ‖z‖) ^ q := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp
  rw [eval_sub, hroot, zero_sub, norm_neg] at hgf
  linarith

end Polynomial
