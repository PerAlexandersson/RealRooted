/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Transforms.BrandenE.Basic
import RealRooted.Transforms.BrandenE.Inverse
public import RealRooted.IntervalDifferential.DiskTransfer
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic

/-!
# The unit-disk spectral criterion for Brändén's transform

After removing `q(q²-1)`, every remaining root in the closed unit disk is admissible.
We first insert real factors and conjugate pairs for the open disk, starting from the constant
polynomial. Radial contraction and bounded-degree closure handle the boundary, including the
double root at length five. This is the prime-power application of the unpublished
structural long-cycle notes, without finite polynomial certificates.
-/

public section

noncomputable section

open Polynomial Finset Filter Topology

namespace RealRooted.IntervalDifferential

/-- Functional calculus distributes over products of spectral polynomials. -/
theorem intervalSpectralApply_mul (c : ℝ) (A B F : ℝ[X]) :
    intervalSpectralApply c (A * B) F =
      intervalSpectralApply c A (intervalSpectralApply c B F) := by
  simp only [intervalSpectralApply, map_mul, mul_apply_eq_comp]

/-- A constant spectral polynomial acts by scalar multiplication. -/
theorem intervalSpectralApply_C (c a : ℝ) (F : ℝ[X]) :
    intervalSpectralApply c (C a) F = C a * F := by
  simp [intervalSpectralApply, Module.algebraMap_end_apply, smul_eq_C_mul]

/-- A real spectral root gives the corresponding half-scaled interval insertion. -/
theorem intervalSpectralApply_X_sub_C (c a : ℝ) (F : ℝ[X]) :
    intervalSpectralApply c (X - C a) F = C (1 / 2) * intervalLinearFactor c (2 * a) F := by
  simp only [intervalSpectralApply, map_sub, aeval_X, aeval_C,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.algebraMap_end_apply,
    intervalLinearFactor, ← smul_eq_C_mul]
  module

/-- A spectral conjugate pair gives the corresponding quarter-scaled quadratic insertion. -/
theorem intervalSpectralApply_pair (c a b : ℝ) (F : ℝ[X]) :
    intervalSpectralApply c ((X - C a) ^ 2 + C (b ^ 2)) F =
      C (1 / 4) * intervalQuadraticFactor c (2 * a) (2 * b) F := by
  have he := intervalSpectralApply_mul c (X - C a) (X - C a) F
  simp only [pow_two] at *
  simp only [intervalSpectralApply, map_add, LinearMap.add_apply, aeval_C,
    Module.algebraMap_end_apply, smul_eq_C_mul]
  change intervalSpectralApply c ((X - C a) * (X - C a)) F + C (b * b) * F = _
  rw [he, intervalSpectralApply_X_sub_C, intervalSpectralApply_X_sub_C]
  simp only [intervalQuadraticFactor, intervalLinearFactor, ← smul_eq_C_mul,
    map_sub, map_smul, smul_sub, smul_smul]
  module

private def InteriorSimple (F : ℝ[X]) : Prop :=
  F ≠ 0 ∧ F.Splits ∧ F.roots.Nodup ∧ ∀ r ∈ F.roots, -1 < r ∧ r < 1

private theorem interiorSimple_C_mul {F : ℝ[X]} (h : InteriorSimple F) {a : ℝ}
    (ha : a ≠ 0) : InteriorSimple (C a * F) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr ha) h.1, h.2.1.C_mul a, ?_⟩
  simpa only [roots_C_mul F ha] using h.2.2

private theorem linear_interior (a : ℝ) (F : ℝ[X]) (hF : InteriorSimple F)
    (ha : a ^ 2 < 1) : InteriorSimple (intervalSpectralApply 4 (X - C a) F) := by
  have hs := intervalLinearFactor_roots 4 (2 * a) F (by norm_num)
    hF.2.1 hF.1 hF.2.2.1 hF.2.2.2 (by constructor <;> nlinarith)
  rw [intervalSpectralApply_X_sub_C]
  exact interiorSimple_C_mul
    ⟨intervalLinearFactor_ne_zero 4 (2 * a) F (by norm_num) hF.1, hs⟩ (by norm_num)

private theorem pair_interior (a b : ℝ) (F : ℝ[X]) (hF : InteriorSimple F)
    (hab : a ^ 2 + b ^ 2 < 1) :
    InteriorSimple (intervalSpectralApply 4 ((X - C a) ^ 2 + C (b ^ 2)) F) := by
  have hs := intervalQuadraticFactor_roots 4 (2 * a) (2 * b) F (by norm_num)
    hF.2.1 hF.1 hF.2.2.1 hF.2.2.2 (by nlinarith [sq_nonneg a])
  have hn : intervalQuadraticFactor 4 (2 * a) (2 * b) F ≠ 0 := by
    intro hz
    have hd := intervalQuadraticFactor_natDegree 4 (2 * a) (2 * b) F (by norm_num) hF.1
    rw [hz, natDegree_zero] at hd
    lia
  rw [intervalSpectralApply_pair]
  exact interiorSimple_C_mul ⟨hn, hs⟩ (by norm_num)

private theorem spectral_interior (Q F : ℝ[X]) (hQ : Q ≠ 0) (hF : InteriorSimple F)
    (hroot : ∀ z : ℂ, aeval z Q = 0 → Complex.normSq z < 1) :
    InteriorSimple (intervalSpectralApply 4 Q F) := by
  generalize hn : Q.natDegree = n
  induction n using Nat.strong_induction_on generalizing Q F with
  | ind n ih =>
    by_cases hz : n = 0
    · have he := eq_C_of_natDegree_eq_zero (hn.trans hz)
      have hc : Q.coeff 0 ≠ 0 := by
        intro hc
        apply hQ
        rw [he, hc, C_0]
      rw [he, intervalSpectralApply_C]
      exact interiorSimple_C_mul hF hc
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ Q (by
        intro hd
        have hzero : Q.natDegree = 0 := natDegree_eq_of_degree_eq_some (n := 0) hd
        exact hz (hn.symm.trans hzero))
      obtain ⟨A, B, hfac, hA, hB, hdeg, hins⟩ :
          ∃ A B : ℝ[X], Q = A * B ∧ A ≠ 0 ∧ B ≠ 0 ∧ 0 < A.natDegree ∧
            InteriorSimple (intervalSpectralApply 4 A F) := by
        by_cases hi : z.im = 0
        · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
          have hr : Q.IsRoot z.re := by
            rw [he] at hz
            exact isRoot_of_aeval_algebraMap_eq_zero hz
          obtain ⟨B, hfac⟩ := dvd_iff_isRoot.mpr hr
          refine ⟨X - C z.re, B, hfac, X_sub_C_ne_zero _, ?_, by simp, ?_⟩
          · exact right_ne_zero_of_mul (hfac ▸ hQ)
          · apply linear_interior _ _ hF
            have hb := hroot z hz
            simpa only [Complex.normSq_apply, hi, mul_zero, add_zero, pow_two] using hb
        · obtain ⟨B, hfac⟩ := Q.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hi
          have he : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) =
              (X - C z.re) ^ 2 + C (z.im ^ 2) := by
            simp only [Complex.sq_norm, Complex.normSq_apply, map_add, map_mul, map_pow, C_ofNat]
            ring
          rw [he] at hfac
          have hd : ((X - C z.re) ^ 2 + C (z.im ^ 2)).natDegree = 2 := by
            compute_degree; norm_num
          refine ⟨_, B, hfac, ne_zero_of_natDegree_gt (p := (X - C z.re) ^ 2 + C (z.im ^ 2))
              (n := 0) (by rw [hd]; norm_num),
            right_ne_zero_of_mul (hfac ▸ hQ), by rw [hd]; norm_num, ?_⟩
          apply pair_interior _ _ _ hF
          simpa only [Complex.normSq_apply, pow_two] using hroot z hz
      have hBd : B.natDegree < n := by
        have he := natDegree_mul hA hB
        rw [← hfac, hn] at he
        lia
      have hBr : ∀ z : ℂ, aeval z B = 0 → Complex.normSq z < 1 := by
        intro z hz
        apply hroot z
        rw [hfac, map_mul, hz, mul_zero]
      rw [hfac, mul_comm A B, intervalSpectralApply_mul]
      exact ih B.natDegree hBd B _ hB hins hBr rfl

/-- Open-unit-disk spectral roots can be inserted from the constant seed at every degree. -/
theorem intervalSpectralApply_one_roots_of_open_unitDisk (Q : ℝ[X]) (hQ : Q ≠ 0)
    (hroot : ∀ z : ℂ, aeval z Q = 0 → Complex.normSq z < 1) :
    (intervalSpectralApply 4 Q 1).Splits := by
  exact (spectral_interior Q 1 hQ (by
    exact ⟨one_ne_zero, Splits.one, by simp, by simp⟩) hroot).2.1

end RealRooted.IntervalDifferential

namespace RealRooted

open IntervalDifferential

private theorem spectral_add (c : ℝ) (A B F : ℝ[X]) :
    intervalSpectralApply c (A + B) F =
      intervalSpectralApply c A F + intervalSpectralApply c B F := by
  simp only [intervalSpectralApply, map_add, LinearMap.add_apply]

private theorem spectral_X_mul (Q F : ℝ[X]) :
    intervalSpectralApply 4 (X * Q) F =
      (1 / 2 : ℝ) • intervalOperator 4 (intervalSpectralApply 4 Q F) := by
  simp only [intervalSpectralApply, map_mul, aeval_X, mul_apply_eq_comp, LinearMap.smul_apply]

private theorem base_alphabet_image :
    brandenE (X * (X ^ 2 - 1) : ℝ[X]) = C 6 * X ^ 2 * (X + 1) := by
  have hp : (X * (X ^ 2 - 1) : ℝ[X]) = X ^ 3 + C (-1) * X := by
    simp only [map_neg, map_one]
    ring
  have hX : brandenE (X : ℝ[X]) = orderedBellPolynomial 1 := by
    simpa only [pow_one] using brandenE_X_pow (R := ℝ) 1
  rw [hp, brandenE_add, brandenE_C_mul, hX, brandenE_X_pow]
  norm_num [orderedBellPolynomial_succ, orderedBellPolynomial_zero]
  simp only [C_ofNat]
  ring

private theorem spectral_conjugation (H : ℝ[X]) :
    let W : ℝ[X] := C 6 * X ^ 2 * (X + 1)
    let U : ℝ[X] := C 2 * X + 1
    X * (W * H.comp U) + X * (1 + X) * (W * H.comp U).derivative =
      W * (((1 / 2 : ℝ) • intervalOperator 4 H).comp U) := by
  dsimp only
  apply mul_left_cancel₀ (C_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0))
  have hs : C 2 * (((1 / 2 : ℝ) • intervalOperator 4 H).comp (C 2 * X + 1)) =
      (intervalOperator 4 H).comp (C 2 * X + 1) := by
    rw [smul_eq_C_mul, mul_comp, C_comp, ← mul_assoc, ← C_mul]
    norm_num
  rw [show C 2 * (C 6 * X ^ 2 * (X + 1) *
      (((1 / 2 : ℝ) • intervalOperator 4 H).comp (C 2 * X + 1))) =
      C 6 * X ^ 2 * (X + 1) *
        (C 2 * (((1 / 2 : ℝ) • intervalOperator 4 H).comp (C 2 * X + 1))) by ring, hs]
  simp only [intervalOperator_apply, derivative_mul, derivative_comp,
    derivative_X_pow_succ, derivative_X, derivative_C, derivative_one,
    Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.pow_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.one_comp, map_add, map_one, Nat.cast_one,
    pow_one, zero_mul, zero_add, mul_one, add_zero]
  norm_num only [C_ofNat]
  ring

/-- The three alphabet factors conjugate Brändén's operator to the weight-four interval operator. -/
theorem brandenE_alphabetFactor (Q : ℝ[X]) :
    brandenE (X * (X ^ 2 - 1) * Q) =
      C 6 * X ^ 2 * (X + 1) * (intervalSpectralApply 4 Q 1).comp (C 2 * X + 1) := by
  induction Q using Polynomial.induction_on with
  | C a =>
    rw [mul_comm (X * (X ^ 2 - 1)), brandenE_C_mul, base_alphabet_image,
      intervalSpectralApply_C, mul_one, C_comp]
    ring
  | add A B hA hB =>
    rw [mul_add, brandenE_add, spectral_add, add_comp, mul_add, hA, hB]
  | monomial n a ih =>
    rw [show X * (X ^ 2 - 1) * (C a * X ^ (n + 1)) =
        X * (X * (X ^ 2 - 1) * (C a * X ^ n)) by ring,
      brandenE_X_mul, ih,
      show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring, spectral_X_mul]
    exact spectral_conjugation _

/-- Open-unit-disk roots of the residual alphabet polynomial give a split `E` image. -/
theorem splits_brandenE_alphabetFactor_of_open_unitDisk {Q : ℝ[X]} (hQ : Q ≠ 0)
    (hroot : ∀ z : ℂ, aeval z Q = 0 → Complex.normSq z < 1) :
    (brandenE (X * (X ^ 2 - 1) * Q)).Splits := by
  rw [brandenE_alphabetFactor]
  apply ((Splits.C _).mul (Splits.X.pow 2) |>.mul (Splits.X_add_C 1)).mul
  exact (intervalSpectralApply_one_roots_of_open_unitDisk Q hQ hroot).comp_of_degree_le_one
    (by compute_degree)

end RealRooted

namespace RealRooted

private theorem brandenE_alphabetFactor_scaleRoots (Q : ℝ[X]) (t : ℝ) :
    brandenE (X * (X ^ 2 - 1) * Q.scaleRoots t) = ∑ i ∈ Q.support,
      C (Q.coeff i * t ^ (Q.natDegree - i)) * brandenE (X * (X ^ 2 - 1) * X ^ i) := by
  rw [scaleRoots, mul_sum, brandenE_finset_sum]
  apply sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial]
  rw [show X * (X ^ 2 - 1) * (C (Q.coeff i * t ^ (Q.natDegree - i)) * X ^ i) =
      C (Q.coeff i * t ^ (Q.natDegree - i)) * (X * (X ^ 2 - 1) * X ^ i) by ring,
    brandenE_C_mul]

private theorem scaleRoots_open_unitDisk {Q : ℝ[X]} (hQ : Q ≠ 0)
    (hroot : ∀ z : ℂ, aeval z Q = 0 → Complex.normSq z ≤ 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ z : ℂ, aeval z (Q.scaleRoots t) = 0 → Complex.normSq z < 1 := by
  intro z hz
  have hmap : (Q.scaleRoots t).map Complex.ofRealHom =
      (Q.map Complex.ofRealHom).scaleRoots (t : ℂ) :=
    map_scaleRoots Q t Complex.ofRealHom
      ((map_ne_zero_iff Complex.ofRealHom Complex.ofRealHom.injective).mpr
        (leadingCoeff_ne_zero.mpr hQ))
  have hm : ((Q.map Complex.ofRealHom).scaleRoots (t : ℂ)) ≠ 0 :=
    scaleRoots_ne_zero (Polynomial.map_ne_zero hQ) _
  have hzmem : z ∈ ((Q.map Complex.ofRealHom).scaleRoots (t : ℂ)).roots := by
    apply (mem_roots hm).mpr
    rw [← hmap]
    rw [IsRoot.def, eval_map]
    rw [aeval_def] at hz
    convert hz using 1
  rw [roots_scaleRoots _ (isUnit_iff_ne_zero.mpr (by exact_mod_cast ht.ne')),
    Multiset.mem_map] at hzmem
  obtain ⟨w, hw, rfl⟩ := hzmem
  have hw0 : aeval w Q = 0 := by
    have he := (mem_roots (Polynomial.map_ne_zero hQ)).mp hw
    rw [IsRoot.def, eval_map] at he
    rw [aeval_def]
    convert he using 1
  have hbound := hroot w hw0
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - Complex.normSq w by linarith)]

/-- Closed-unit-disk residual roots give a real-rooted `E` image. Radial contraction handles
boundary pairs and repeated transformed roots, using bounded-degree closure. -/
theorem splits_brandenE_alphabetFactor_of_closed_unitDisk {Q : ℝ[X]} (hQ : Q ≠ 0)
    (hroot : ∀ z : ℂ, aeval z Q = 0 → Complex.normSq z ≤ 1) :
    (brandenE (X * (X ^ 2 - 1) * Q)).Splits := by
  let t (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)
  have ht (n : ℕ) : 0 < t n ∧ t n < 1 := by
    dsimp only [t]
    have hn : (1 : ℝ) < n + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hlt : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr hn
    constructor <;> linarith
  have htlim : Tendsto t atTop (𝓝 1) := by
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    simpa only [sub_zero] using tendsto_const_nhds.sub hzero
  let P (s : ℝ) := brandenE (X * (X ^ 2 - 1) * Q.scaleRoots s)
  have hdegree (n : ℕ) : (P (t n)).natDegree ≤ Q.natDegree + 3 := by
    change (brandenE (X * (X ^ 2 - 1) * Q.scaleRoots (t n))).natDegree ≤ _
    apply (basisTransform_natDegree_le_of_natDegree_le
      (fun i => (orderedBellPolynomial_natDegree (R := ℝ) i).le) _).trans
    have hb : (X * (X ^ 2 - 1) : ℝ[X]).natDegree ≤ 3 := by
      calc
        _ ≤ (X : ℝ[X]).natDegree + (X ^ 2 - 1 : ℝ[X]).natDegree := natDegree_mul_le
        _ ≤ 1 + 2 := add_le_add (by simp)
          ((natDegree_sub_le _ _).trans (by simp))
        _ = 3 := rfl
    have hh := natDegree_mul_le (p := (X * (X ^ 2 - 1) : ℝ[X])) (q := Q.scaleRoots (t n))
    rw [natDegree_scaleRoots] at hh
    lia
  have hsplits (n : ℕ) : P (t n) = 0 ∨ (P (t n)).Splits := by
    right
    exact splits_brandenE_alphabetFactor_of_open_unitDisk (scaleRoots_ne_zero hQ _)
      (scaleRoots_open_unitDisk hQ hroot (ht n).1 (ht n).2)
  have heval (z : ℂ) : Continuous (fun s : ℝ => ((P s).map Complex.ofRealHom).eval z) := by
    simp only [P, brandenE_alphabetFactor_scaleRoots, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, eval_finsetSum, eval_mul, eval_C]
    change Continuous (fun s : ℝ => ∑ i ∈ Q.support,
      ((Q.coeff i * s ^ (Q.natDegree - i) : ℝ) : ℂ) *
        ((brandenE (X * (X ^ 2 - 1) * X ^ i)).map Complex.ofRealHom).eval z)
    fun_prop
  have hlim := Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le hdegree hsplits
    (fun z => (heval z).continuousAt.tendsto.comp htlim)
  have hP : P 1 = brandenE (X * (X ^ 2 - 1) * Q) := by simp only [P, scaleRoots_one]
  rw [hP] at hlim
  apply hlim.resolve_left
  intro hz
  have hb : (X * (X ^ 2 - 1) : ℝ[X]) ≠ 0 :=
    mul_ne_zero X_ne_zero (by
      have hd : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by compute_degree; norm_num
      exact ne_zero_of_natDegree_gt (p := (X ^ 2 - 1 : ℝ[X]))
        (n := 0) (by rw [hd]; norm_num))
  exact mul_ne_zero hb hQ (brandenE_injective (by simpa only [brandenE_zero] using hz))

end RealRooted
