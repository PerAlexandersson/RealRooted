import Mathlib.Analysis.MeanInequalities
import RealRooted.DerivativeRecurrence.RootWindow

/-!
# The outer selected-height bound

This file proves the uniform height bound at a critical point lying strictly
to the left of every root of a normalized polynomial with negative roots: if
`f(0) = 1`, `f` has degree `d > 0` and only negative roots, `s` lies left of every root and
`2(2d+1) f(s) + (1 - 4s) f'(s) = 0`, then `(-1)^d f(s) > (2d)^d`.  This settles the outer
selected slots of the A101280 orbit (issue #1342); the interior slots need an
orbit-specific invariant, since the generic closures `f + 1 ≼ X Δ` and `Tail ≼ Δ` are false.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

private theorem fin_prod_le_avg_pow {d : ℕ} (hd : d ≠ 0) (e : Fin d → ℝ)
    (he : ∀ i, 0 ≤ e i) :
    ∏ i, e i ≤ ((∑ i, e i) / (d : ℝ)) ^ d := by
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) e (fun _ _ => by positivity)
      (by simpa using Nat.pos_of_ne_zero hd) (fun i _ => he i)
  have h' : (∏ i, e i) ^ ((d : ℝ)⁻¹) ≤ (∑ i, e i) / (d : ℝ) := by
    simpa only [Real.rpow_one, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      one_mul, Finset.sum_const, mul_one] using h
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg (Finset.prod_nonneg fun i _ => he i) _) h' d
  rwa [Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => he i) hd] at hpow

private theorem eval_derivative_finset_prod_div_eval
    {ι : Type*} (u : Finset ι) (g : ι → ℝ[X]) (x : ℝ)
    (h : ∀ i ∈ u, (g i).eval x ≠ 0) :
    (derivative (∏ i ∈ u, g i)).eval x / (∏ i ∈ u, g i).eval x =
      ∑ i ∈ u, (derivative (g i)).eval x / (g i).eval x := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
      have hprod : (∏ j ∈ u, g j).eval x ≠ 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_ne_zero_iff.mpr fun j hj =>
          h j (Finset.mem_insert_of_mem hj)
      have hgi : (g i).eval x ≠ 0 := h i (Finset.mem_insert_self i u)
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Polynomial.derivative_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul]
      rw [← ih fun j hj => h j (Finset.mem_insert_of_mem hj)]
      field_simp

/-- Suppose `f` is the product of `d ≠ 0` normalized linear factors with roots
`-a i < 0`. If `s` lies strictly to the left of every root and satisfies the
displayed critical-point equation, then its signed height is strictly larger
than `(2 * d) ^ d`.

The factorization encodes both `f(0) = 1` and that all roots of `f` are
negative, counted with multiplicity. -/
theorem two_mul_degree_pow_lt_signed_eval_of_outer_critical
    {f : ℝ[X]} {d : ℕ} (hd : d ≠ 0) (a : Fin d → ℝ)
    (ha : ∀ i, 0 < a i)
    (hfactor : f = Finset.univ.prod
      (fun i : Fin d => (1 : ℝ[X]) + C ((a i)⁻¹) * X))
    {s : ℝ} (hs : ∀ i, s < -a i)
    (hcritical : 2 * (2 * (d : ℝ) + 1) * f.eval s +
      (1 - 4 * s) * f.derivative.eval s = 0) :
    (2 * (d : ℝ)) ^ d < (-1) ^ d * f.eval s := by
  classical
  let g : Fin d → ℝ[X] := fun i => (1 : ℝ[X]) + C ((a i)⁻¹) * X
  let b : Fin d → ℝ := fun i => (-s - a i) / a i
  let c : Fin d → ℝ := fun i => 1 / (-s - a i)
  let e : Fin d → ℝ := fun i => a i / (-s - a i)
  let i₀ : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  have hsneg : s < 0 := lt_trans (hs i₀) (neg_neg_of_pos (ha i₀))
  have hb : ∀ i, 0 < b i := fun i => div_pos (by linarith [hs i]) (ha i)
  have he : ∀ i, 0 < e i := fun i => div_pos (ha i) (by linarith [hs i])
  have hgeval : ∀ i, (g i).eval s = -b i := by
    intro i
    dsimp [g, b]
    simp only [eval_add, eval_one, eval_mul, eval_C, eval_X]
    field_simp [(ha i).ne']
    ring
  have hfeval : f.eval s = ∏ i, -b i := by
    rw [hfactor, eval_prod]
    exact Finset.prod_congr rfl fun i _ => hgeval i
  have hfs : f.eval s ≠ 0 := by
    rw [hfeval]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (hb i).ne'
  have hlog : f.derivative.eval s / f.eval s = -∑ i, c i := by
    rw [hfactor]
    have h := eval_derivative_finset_prod_div_eval Finset.univ g s
      (fun i _ => (hgeval i).trans_ne (neg_ne_zero.mpr (hb i).ne'))
    simp only [g, derivative_add, derivative_one, derivative_mul, derivative_C,
      derivative_X, zero_add, zero_mul, mul_one, eval_C] at h
    rw [h, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hgeval]
    dsimp [b, c]
    field_simp [(ha i).ne', (by linarith [hs i] : -s - a i ≠ 0)]
  have hsum_c : ∑ i, c i = 2 * (2 * (d : ℝ) + 1) / (1 - 4 * s) := by
    have hden : 1 - 4 * s ≠ 0 := by linarith
    have hderiv : f.derivative.eval s = (-∑ i, c i) * f.eval s :=
      (div_eq_iff hfs).mp hlog
    have hcrit : 2 * (2 * (d : ℝ) + 1) -
        (1 - 4 * s) * (∑ i, c i) = 0 := by
      rw [hderiv] at hcritical
      have hzero : f.eval s * (2 * (2 * (d : ℝ) + 1) -
          (1 - 4 * s) * (∑ i, c i)) = 0 := by
        nlinarith
      exact (mul_eq_zero.mp hzero).resolve_left hfs
    rw [eq_div_iff hden]
    linarith
  have hsum_e : ∑ i, e i = (-2 * s - d) / (1 - 4 * s) := by
    calc
      ∑ i, e i = ∑ i, ((-s) * c i - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [e, c]
        field_simp [(by linarith [hs i] : -s - a i ≠ 0)]
        ring
      _ = (-s) * (∑ i, c i) - d := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [Finset.mul_sum]
      _ = (-2 * s - d) / (1 - 4 * s) := by
        rw [hsum_c]
        have hden : 1 - 4 * s ≠ 0 := by linarith
        have hden' : 1 - s * 4 ≠ 0 := by linarith
        rw [eq_div_iff hden]
        field_simp [hden, hden']; ring
  have hsum_e_lt : ∑ i, e i < 1 / 2 := by
    rw [hsum_e]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    rw [div_lt_iff₀ (by linarith : 0 < 1 - 4 * s)]
    linarith
  have hprod_e_le := fin_prod_le_avg_pow hd e (fun i => (he i).le)
  have havg_lt : (∑ i, e i) / (d : ℝ) < 1 / (2 * d) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    rw [div_lt_div_iff₀ hdpos (by positivity)]
    nlinarith [hsum_e_lt]
  have hprod_e_lt : ∏ i, e i < (1 / (2 * (d : ℝ))) ^ d :=
    hprod_e_le.trans_lt (pow_lt_pow_left₀ havg_lt
      (div_nonneg (Finset.sum_nonneg fun i _ => (he i).le) (by positivity)) hd)
  have heb : ∀ i, e i = (b i)⁻¹ := by
    intro i
    dsimp [e, b]
    field_simp [(ha i).ne', (by linarith [hs i] : -s - a i ≠ 0)]
  have hprod_b : (2 * (d : ℝ)) ^ d < ∏ i, b i := by
    have heprod_pos : 0 < ∏ i, e i := Finset.prod_pos fun i _ => he i
    rw [show (∏ i, b i) = (∏ i, e i)⁻¹ by
      simp only [heb, Finset.prod_inv_distrib, inv_inv]]
    rw [one_div, inv_pow] at hprod_e_lt
    exact lt_inv_of_lt_inv₀ heprod_pos hprod_e_lt
  rw [hfeval, show (∏ i, -b i) = (-1 : ℝ) ^ d * ∏ i, b i by
    simpa using (Finset.prod_neg (s := Finset.univ) b)]
  convert hprod_b using 1
  rw [← mul_assoc, ← pow_two, ← pow_mul]
  norm_num

end RealRooted
