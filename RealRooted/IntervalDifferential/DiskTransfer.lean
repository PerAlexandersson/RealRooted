/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.EndpointWeight
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Tactic

/-!
# Functional calculus for the structural interval transfer

We choose moment-controlled factors until degree six, then use the centered disk
bound. This is Lemma 1 of the unpublished structural long-cycle descent notes.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- Apply `Q` to half the interval differential operator, acting on `F`. -/
def intervalSpectralApply (c : ℝ) (Q F : ℝ[X]) : ℝ[X] :=
  aeval ((1 / 2 : ℝ) • intervalOperator c) Q F

private def intervalSimple (F : ℝ[X]) : Prop :=
  F ≠ 0 ∧ F.Splits ∧ F.roots.Nodup ∧ ∀ r ∈ F.roots, -1 < r ∧ r < 1

private theorem intervalSimple_C_mul {F : ℝ[X]} (h : intervalSimple F)
    {a : ℝ} (ha : a ≠ 0) : intervalSimple (C a * F) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr ha) h.1, h.2.1.C_mul a, ?_⟩
  simpa only [roots_C_mul F ha] using h.2.2

private theorem intervalSpectralApply_C (c a : ℝ) (F : ℝ[X]) :
    intervalSpectralApply c (C a) F = C a * F := by
  simp [intervalSpectralApply, Module.algebraMap_end_apply, smul_eq_C_mul]

private theorem intervalSpectralApply_mul (c : ℝ) (A B F : ℝ[X]) :
    intervalSpectralApply c (A * B) F =
      intervalSpectralApply c A (intervalSpectralApply c B F) := by
  simp only [intervalSpectralApply, map_mul, mul_apply_eq_comp]

private theorem intervalSpectralApply_linear (c a : ℝ) (F : ℝ[X]) :
    intervalSpectralApply c (X - C a) F = C (1 / 2) * intervalLinearFactor c (2 * a) F := by
  simp only [intervalSpectralApply, map_sub, aeval_X, aeval_C,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.algebraMap_end_apply,
    intervalLinearFactor, ← smul_eq_C_mul]
  module

private theorem intervalSpectralApply_pair (c a b : ℝ) (F : ℝ[X]) :
    intervalSpectralApply c ((X - C a) ^ 2 + C (b ^ 2)) F =
      C (1 / 4) * intervalQuadraticFactor c (2 * a) (2 * b) F := by
  have he := intervalSpectralApply_mul c (X - C a) (X - C a) F
  simp only [pow_two] at *
  simp only [intervalSpectralApply, map_add, LinearMap.add_apply, aeval_C,
    Module.algebraMap_end_apply, smul_eq_C_mul]
  change intervalSpectralApply c ((X - C a) * (X - C a)) F + C (b * b) * F = _
  rw [he, intervalSpectralApply_linear, intervalSpectralApply_linear]
  simp only [intervalQuadraticFactor, intervalLinearFactor, ← smul_eq_C_mul,
    map_sub, map_smul, smul_sub, smul_smul]
  module

/-- The real second power sum, including root multiplicities. -/
private def rootSquareSum (Q : ℝ[X]) : ℝ :=
  (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum

private theorem rootSquareSum_mul {A B : ℝ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    rootSquareSum (A * B) = rootSquareSum A + rootSquareSum B := by
  unfold rootSquareSum
  rw [Polynomial.map_mul, roots_mul (mul_ne_zero (Polynomial.map_ne_zero hA)
    (Polynomial.map_ne_zero hB)), Multiset.map_add, Multiset.sum_add]

private theorem rootSquareSum_le (Q : ℝ[X])
    (hdisk : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval z = 0 →
      Complex.normSq z ≤ 25 / 16) : rootSquareSum Q ≤ (25 / 16 : ℝ) * Q.natDegree := by
  by_cases hQ : Q = 0
  · simp [hQ, rootSquareSum]
  · have hh := Multiset.sum_le_card_nsmul
      (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re) (25 / 16 : ℝ) (by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
        have he := hdisk z ((mem_roots (Polynomial.map_ne_zero hQ)).mp hz)
        simp only [Complex.normSq_apply, pow_two, Complex.mul_re] at he ⊢
        nlinarith [sq_nonneg z.im])
    simpa only [rootSquareSum, Multiset.card_map, nsmul_eq_mul,
      ← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map, mul_comm] using hh

private def rootPair (z : ℂ) : ℝ[X] :=
  X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)

private theorem rootPair_shape (z : ℂ) :
    rootPair z = (X - C z.re) ^ 2 + C (z.im ^ 2) := by
  simp only [rootPair, map_mul, C_ofNat, Complex.sq_norm, Complex.normSq_apply, map_add, map_pow]
  ring

private theorem rootPair_monic (z : ℂ) : (rootPair z).Monic := by
  convert monic_X_pow_add (n := 2) (p := -C (2 * z.re) * X + C (‖z‖ ^ 2))
    (by compute_degree; norm_num) using 1; simp [rootPair, sub_eq_add_neg, add_assoc]

private theorem rootPair_natDegree (z : ℂ) : (rootPair z).natDegree = 2 := by
  rw [rootPair]
  compute_degree <;> norm_num

private theorem rootPair_map (z : ℂ) :
    (rootPair z).map (algebraMap ℝ ℂ) =
      (X - C (starRingEnd ℂ z)) * (X - C z) := by
  simp only [rootPair, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
  change X ^ 2 - C ((2 * z.re : ℝ) : ℂ) * X + C ((‖z‖ ^ 2 : ℝ) : ℂ) = _
  have hs : ((2 * z.re : ℝ) : ℂ) = z + (starRingEnd ℂ) z :=
    (Complex.add_conj z).symm
  have hn : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    push_cast
    exact (Complex.mul_conj' z).symm
  rw [hs, hn, map_add, map_mul]
  ring

private theorem intervalSpectralApply_linear_roots (a : ℝ) (F : ℝ[X])
    (hF : intervalSimple F) (ha : a ^ 2 ≤ 25 / 16) :
    intervalSimple (intervalSpectralApply 4 (X - C a) F) ∧
      (intervalSpectralApply 4 (X - C a) F).natDegree = F.natDegree + 1 := by
  have hb : -(4 : ℝ) < 2 * a ∧ 2 * a < 4 := by constructor <;> nlinarith
  have hn := intervalLinearFactor_ne_zero 4 (2 * a) F (by norm_num) hF.1
  have hr := intervalLinearFactor_roots 4 (2 * a) F (by norm_num)
    hF.2.1 hF.1 hF.2.2.1 hF.2.2.2 hb
  rw [intervalSpectralApply_linear]
  refine ⟨intervalSimple_C_mul ⟨hn, hr⟩ (by norm_num), ?_⟩
  rw [natDegree_C_mul (by norm_num : (1 / 2 : ℝ) ≠ 0),
    intervalLinearFactor_natDegree 4 (2 * a) F (by norm_num) hF.1]

private theorem intervalSpectralApply_pair_roots (z : ℂ) (F : ℝ[X])
    (hF : intervalSimple F) (hz : Complex.normSq z ≤ 25 / 16) (hb : z.im ≠ 0)
    (hstart : F.natDegree < 6 →
      -(2 + (25 / 16 : ℝ) * F.natDegree) / (15 - F.natDegree) ≤ (z ^ 2).re) :
    intervalSimple (intervalSpectralApply 4 (rootPair z) F) ∧
      (intervalSpectralApply 4 (rootPair z) F).natDegree = F.natDegree + 2 := by
  have hdisk : (2 * z.re) ^ 2 + (2 * z.im) ^ 2 ≤ 25 / 4 := by
    simp only [Complex.normSq_apply] at hz
    nlinarith
  obtain ⟨u, hu, hpair⟩ : ∃ u : ℝ, |u| < 4 ∧
      (2 * z.re - u) ^ 2 + (2 * z.im) ^ 2 <
        intervalInsertionThreshold 4 F.natDegree u := by
    by_cases hd : 6 ≤ F.natDegree
    · refine ⟨0, by norm_num, ?_⟩
      simpa only [sub_zero] using hdisk.trans_lt (intervalInsertionThreshold_six hd)
    · apply intervalInsertionThreshold_small (by lia) _ _ hdisk
      have hm := hstart (by lia)
      simp only [pow_two, Complex.mul_re] at hm
      nlinarith
  have hr := intervalQuadraticFactor_shift_roots 4 (2 * z.re) (2 * z.im) u F
    (by norm_num) hF.2.1 hF.1 hF.2.2.1 hF.2.2.2 hu (mul_ne_zero (by norm_num) hb) hpair
  have hd := intervalQuadraticFactor_natDegree 4 (2 * z.re) (2 * z.im) F
    (by norm_num) hF.1
  have hn : intervalQuadraticFactor 4 (2 * z.re) (2 * z.im) F ≠ 0 := by
    intro hh
    rw [hh, natDegree_zero] at hd
    lia
  rw [rootPair_shape, intervalSpectralApply_pair]
  refine ⟨intervalSimple_C_mul ⟨hn, hr⟩ (by norm_num), ?_⟩
  rw [natDegree_C_mul (by norm_num : (1 / 4 : ℝ) ≠ 0), hd]

/-- The remaining power sum supplies the next starting root. -/
private theorem exists_insertion_root (Q F : ℝ[X]) (hQ : 0 < Q.natDegree)
    (hdegree : 15 ≤ Q.natDegree + F.natDegree)
    (hmoment : -2 - (25 / 16 : ℝ) * F.natDegree ≤ rootSquareSum Q) :
    ∃ z ∈ (Q.map (algebraMap ℝ ℂ)).roots, F.natDegree < 6 →
      -(2 + (25 / 16 : ℝ) * F.natDegree) / (15 - F.natDegree) ≤ (z ^ 2).re := by
  classical
  have hcard : (Q.map (algebraMap ℝ ℂ)).roots.card = Q.natDegree := by
    rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]
  have hne : (Q.map (algebraMap ℝ ℂ)).roots ≠ 0 := by
    exact Multiset.card_pos.mp (hcard ▸ hQ)
  by_cases hd : 6 ≤ F.natDegree
  · obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨z, hz, fun h => (by lia : False).elim⟩
  · let t : ℝ := -(2 + (25 / 16 : ℝ) * F.natDegree) / (15 - F.natDegree)
    have hf : (F.natDegree : ℝ) < 15 := by exact_mod_cast (by lia : F.natDegree < 15)
    have hp : 0 < (15 : ℝ) - F.natDegree := by linarith
    have ht : t ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hp.le
      have hh : 0 ≤ (F.natDegree : ℝ) := Nat.cast_nonneg _
      linarith
    have he : t * (15 - F.natDegree) = -(2 + (25 / 16 : ℝ) * F.natDegree) :=
      div_mul_cancel₀ _ hp.ne'
    have hc : (15 : ℝ) - F.natDegree ≤ Q.natDegree := by
      have hh : (15 : ℝ) ≤ (Q.natDegree : ℝ) + F.natDegree := by exact_mod_cast hdegree
      linarith
    by_contra hn
    have hall : ∀ z ∈ (Q.map (algebraMap ℝ ℂ)).roots, (z ^ 2).re < t := by
      intro z hz
      by_contra h
      exact hn ⟨z, hz, fun _ => le_of_not_gt h⟩
    have hs := Multiset.sum_lt_sum_of_nonempty (f := fun z : ℂ => (z ^ 2).re)
      (g := fun _ => t) hne hall
    simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hcard] at hs
    have hm := mul_le_mul_of_nonpos_right hc ht
    unfold rootSquareSum at hmoment
    nlinarith

/-- Remove one real or conjugate spectral factor while preserving interval roots. -/
private theorem insertion_factor (Q F : ℝ[X]) (hQ : Q ≠ 0) (hF : intervalSimple F)
    (z : ℂ) (hz : aeval z Q = 0) (hdisk : Complex.normSq z ≤ 25 / 16)
    (hgood : F.natDegree < 6 →
      -(2 + (25 / 16 : ℝ) * F.natDegree) / (15 - F.natDegree) ≤ (z ^ 2).re) :
    ∃ A U : ℝ[X], Q = A * U ∧ A ≠ 0 ∧ U ≠ 0 ∧ 0 < A.natDegree ∧
      intervalSimple (intervalSpectralApply 4 A F) ∧
      (intervalSpectralApply 4 A F).natDegree = F.natDegree + A.natDegree := by
  by_cases hz0 : z.im = 0
  · have hzeq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    have hr : Q.IsRoot z.re := by
      rw [hzeq] at hz
      exact isRoot_of_aeval_algebraMap_eq_zero hz
    obtain ⟨U, hfac⟩ := dvd_iff_isRoot.mpr hr
    have hU : U ≠ 0 := by intro h; apply hQ; rw [hfac, h, mul_zero]
    have hb : z.re ^ 2 ≤ 25 / 16 := by
      simpa only [Complex.normSq_apply, hz0, mul_zero, add_zero, pow_two] using hdisk
    obtain ⟨hs, hd⟩ := intervalSpectralApply_linear_roots z.re F hF hb
    exact ⟨X - C z.re, U, hfac, X_sub_C_ne_zero _, hU, by simp, hs,
      by simpa only [natDegree_X_sub_C] using hd⟩
  · obtain ⟨U, hfac⟩ := Q.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hz0
    change Q = rootPair z * U at hfac
    have hU : U ≠ 0 := by intro h; apply hQ; rw [hfac, h, mul_zero]
    obtain ⟨hs, hd⟩ := intervalSpectralApply_pair_roots z F hF hdisk hz0 hgood
    exact ⟨rootPair z, U, hfac, (rootPair_monic z).ne_zero, hU,
      by rw [rootPair_natDegree]; norm_num, hs,
      by simpa only [rootPair_natDegree] using hd⟩

/-- The power-sum invariant controls the order of all remaining factors. -/
private theorem intervalSpectralApply_roots_of_moment (Q F : ℝ[X])
    (hQ : Q ≠ 0) (hF : intervalSimple F)
    (hdisk : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval z = 0 → Complex.normSq z ≤ 25 / 16)
    (hdegree : 15 ≤ Q.natDegree + F.natDegree)
    (hmoment : -2 - (25 / 16 : ℝ) * F.natDegree ≤ rootSquareSum Q) :
    intervalSimple (intervalSpectralApply 4 Q F) ∧
      (intervalSpectralApply 4 Q F).natDegree = Q.natDegree + F.natDegree := by
  generalize hn : Q.natDegree = n
  induction n using Nat.strong_induction_on generalizing Q F with
  | ind n ih =>
    by_cases hz : n = 0
    · have hconst := eq_C_of_natDegree_eq_zero (hn.trans hz)
      have hcoef : Q.coeff 0 ≠ 0 := by
        intro hh
        apply hQ
        rw [hconst, hh, map_zero]
      rw [hconst, intervalSpectralApply_C]
      refine ⟨intervalSimple_C_mul hF hcoef, ?_⟩
      simp only [natDegree_C_mul hcoef, hz, zero_add]
    · obtain ⟨z, hzmem, hgood⟩ := exists_insertion_root Q F (by lia) hdegree hmoment
      have hzeval := (mem_roots (Polynomial.map_ne_zero hQ)).mp hzmem
      have hzaeval : aeval z Q = 0 := by
        simpa only [IsRoot.def, eval_map_algebraMap] using hzeval
      obtain ⟨A, U, hfac, hA, hU, hAdeg, hG, hGdeg⟩ :=
        insertion_factor Q F hQ hF z hzaeval (hdisk z hzeval) hgood
      have hdeg := natDegree_mul hA hU
      rw [← hfac, hn] at hdeg
      have hUdeg : U.natDegree < n := by lia
      have hAdisk (w : ℂ) (hw : (A.map (algebraMap ℝ ℂ)).eval w = 0) :
          Complex.normSq w ≤ 25 / 16 := by
        apply hdisk w
        rw [hfac, Polynomial.map_mul, eval_mul, hw, zero_mul]
      have hUdisk (w : ℂ) (hw : (U.map (algebraMap ℝ ℂ)).eval w = 0) :
          Complex.normSq w ≤ 25 / 16 := by
        apply hdisk w
        rw [hfac, Polynomial.map_mul, eval_mul, hw, mul_zero]
      have hbound := rootSquareSum_le A hAdisk
      have hsum := rootSquareSum_mul hA hU
      rw [← hfac] at hsum
      have hnext := ih U.natDegree hUdeg U (intervalSpectralApply 4 A F) hU hG hUdisk
        (by lia) (by rw [hGdeg]; push_cast; nlinarith [hmoment, hsum, hbound]) rfl
      rw [hfac, mul_comm A U, intervalSpectralApply_mul]
      refine ⟨hnext.1, ?_⟩
      rw [hnext.2, hGdeg]
      lia

/-- The iterated half-operator forms a degree-triangular polynomial basis. -/
private theorem intervalOperator_iterates (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ((((1 / 2 : ℝ) • intervalOperator c) ^ n) 1).natDegree = n ∧
      (((1 / 2 : ℝ) • intervalOperator c) ^ n) 1 ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, LinearMap.smul_apply, smul_eq_C_mul]
    have hd := intervalLinearFactor_natDegree c 0
      ((((1 / 2 : ℝ) • intervalOperator c) ^ n) 1) hc ih.2
    simp only [intervalLinearFactor, map_zero, zero_mul, sub_zero] at hd
    have hn : intervalOperator c ((((1 / 2 : ℝ) • intervalOperator c) ^ n) 1) ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at hd
      lia
    refine ⟨?_, mul_ne_zero (C_ne_zero.mpr (by norm_num)) hn⟩
    rw [natDegree_C_mul (by norm_num : (1 / 2 : ℝ) ≠ 0), hd, ih.1]

/-- Positive endpoint weights make the spectral transform preserve degree. -/
theorem intervalSpectralApply_one_natDegree (c : ℝ) (hc : 0 < c) (Q : ℝ[X]) :
    (intervalSpectralApply c Q 1).natDegree = Q.natDegree := by
  by_cases hQ : Q = 0
  · simp [hQ, intervalSpectralApply]
  · rw [intervalSpectralApply, ← basisTransform_iterate_eq_aeval_apply]
    exact basisTransform_natDegree_eq (fun n => (intervalOperator_iterates c hc n).1)
      (fun n => (intervalOperator_iterates c hc n).2) hQ

/-- The structural interval transfer for any disk with squared radius at most
`25/16`. Degree fifteen and second power sum at least `-2` suffice. -/
theorem intervalSpectralApply_one_roots (Q : ℝ[X]) (hm : 15 ≤ Q.natDegree)
    {radiusSq : ℝ} (hradius : radiusSq ≤ 25 / 16)
    (hdisk : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval z = 0 → Complex.normSq z ≤ radiusSq)
    (hpower : -2 ≤ (((Q.map (algebraMap ℝ ℂ)).roots).map fun z => (z ^ 2).re).sum) :
    intervalSpectralApply 4 Q 1 ≠ 0 ∧
      (intervalSpectralApply 4 Q 1).natDegree = Q.natDegree ∧
      (intervalSpectralApply 4 Q 1).Splits ∧
      (intervalSpectralApply 4 Q 1).roots.Nodup ∧
      ∀ r ∈ (intervalSpectralApply 4 Q 1).roots, -1 < r ∧ r < 1 := by
  have hQ : Q ≠ 0 := ne_zero_of_natDegree_gt (show 0 < Q.natDegree by lia)
  have ht := intervalSpectralApply_roots_of_moment Q 1 hQ
    ⟨one_ne_zero, Splits.one, by simp, by simp⟩
    (fun z hz => (hdisk z hz).trans hradius) (by simpa using hm)
    (by simpa [rootSquareSum] using hpower)
  exact ⟨ht.1.1, by simpa using ht.2, ht.1.2⟩

end RealRooted.IntervalDifferential
