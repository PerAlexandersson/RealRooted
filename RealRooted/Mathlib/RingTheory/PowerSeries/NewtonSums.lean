/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Log
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmPositive
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmMul
import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
import RealRooted.Mathlib.RingTheory.PowerSeries.PiTopology
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.ElementarySymmetric
import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Data.Multiset.Fintype
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Newton sums from elementary symmetric coefficients

We evaluate Newton's identities on a multiset and use the resulting recursion
for coefficientwise limits. The multiset evaluation is adapted from Tau Ceti
`RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open Finset Filter Topology

namespace Multiset

/-- Newton's power-sum identity evaluated on a multiset.
Adapted from Tau Ceti `RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`
(Apache-2.0). -/
theorem sum_map_pow_eq_esymm_sub_sum {R : Type*} [CommRing R]
    (s : Multiset R) {k : ℕ} (hk : 0 < k) :
    (s.map (· ^ k)).sum = (-1) ^ (k + 1) * k * s.esymm k -
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval fun x : s.ToType => (x : R))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s.ToType R k hk)
  have hpsum (j : ℕ) : MvPolynomial.aeval (fun x : s.ToType => (x : R))
      (MvPolynomial.psum s.ToType R j) = (s.map (· ^ j)).sum := by
    rw [← Multiset.map_univ_comp_coe, Finset.sum_map_val]
    simp [MvPolynomial.psum]
  simpa only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, hpsum] using h

end Multiset

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The Newton power sums associated with elementary symmetric coefficients.
The value at zero is set to zero; only positive indices encode power sums. -/
def newtonSum (a : PowerSeries R) (k : ℕ) : R :=
  if k = 0 then 0 else
    (-1) ^ (k + 1) * k * coeff k a -
      ∑ q ∈ ({q ∈ Finset.HasAntidiagonal.antidiagonal k | q.1 ∈ Set.Ioo 0 k} :
          Finset (ℕ × ℕ)).attach,
        (-1) ^ q.1.1 * coeff q.1.1 a * newtonSum a q.1.2
termination_by k
decreasing_by
  have hq := (mem_filter.mp q.2)
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq.1
  have hpos := hq.2.1
  lia

/-- The zero index of the Newton-sum recursion is unused. -/
@[simp] theorem newtonSum_zero (a : PowerSeries R) : newtonSum a 0 = 0 := by
  simp [newtonSum]

/-- Newton's recursion, with the finite dependent sum removed. -/
theorem newtonSum_of_pos (a : PowerSeries R) {k : ℕ} (hk : 0 < k) :
    newtonSum a k = (-1) ^ (k + 1) * k * coeff k a -
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal k with q.1 ∈ Set.Ioo 0 k,
        (-1) ^ q.1 * coeff q.1 a * newtonSum a q.2 := by
  rw [newtonSum, ite_eq_right (by lia),
    sum_attach _ (fun q : ℕ × ℕ => (-1 : R) ^ q.1 * coeff q.1 a * newtonSum a q.2)]

/-- Newton sums of the elementary symmetric coefficients of a multiset
are its positive power sums. -/
theorem newtonSum_mk_esymm (s : Multiset R) {k : ℕ} (hk : 0 < k) :
    newtonSum (mk s.esymm) k = (s.map (· ^ k)).sum := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [newtonSum_of_pos _ hk, s.sum_map_pow_eq_esymm_sub_sum hk, coeff_mk]
    congr 1
    apply sum_congr rfl
    intro q hq
    have hq' := mem_filter.mp hq
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq'.1
    rw [coeff_mk, ih q.2 (by have := hq'.2.1; lia) (by have := hq'.2.2; lia)]

/-- Each Newton sum is continuous under coefficientwise convergence. -/
theorem tendsto_newtonSum_of_coeff_tendsto
    [TopologicalSpace R] [IsTopologicalRing R]
    {ι : Type*} {l : Filter ι} {a : ι → PowerSeries R} {b : PowerSeries R}
    (h : ∀ j, Tendsto (fun i => coeff j (a i)) l (𝓝 (coeff j b))) (k : ℕ) :
    Tendsto (fun i => newtonSum (a i) k) l (𝓝 (newtonSum b k)) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [newtonSum_zero]
      exact tendsto_const_nhds
    · simp_rw [newtonSum_of_pos _ hk]
      apply Tendsto.sub (tendsto_const_nhds.mul (h k))
      apply tendsto_finsetSum
      intro q hq
      have hq' := mem_filter.mp hq
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq'.1
      exact (tendsto_const_nhds.mul (h q.1)).mul (ih q.2 (by have := hq'.2.1; lia))

/-- The elementary symmetric series after adjoining one variable. -/
theorem mk_esymm_cons (x : R) (s : Multiset R) :
    mk (x ::ₘ s).esymm = (1 + C x * X) * mk s.esymm := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp [add_mul, mul_assoc, coeff_C_mul, coeff_succ_X_mul, Multiset.esymm_cons]

/-- A positive power sum equals the corresponding signed logarithmic
coefficient of the elementary symmetric series. -/
theorem signed_coeff_logOf_mk_esymm (s : Multiset ℝ) {k : ℕ} (hk : 0 < k) :
    (-1 : ℝ) ^ (k + 1) * k * coeff k (logOf (mk s.esymm)) =
      (s.map (· ^ k)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    have he : mk (0 : Multiset ℝ).esymm = (1 : PowerSeries ℝ) := by
      ext n
      simp only [coeff_mk, coeff_one]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [Multiset.esymm_of_card_lt (by simpa using Nat.pos_of_ne_zero hn),
          ite_eq_right hn]
    rw [he]
    simp [logOf_eq]
  | cons x s ih =>
    rw [mk_esymm_cons, logOf_mul _ _ (by simp) (by simp), map_add,
      mul_add, ih, Multiset.map_cons, Multiset.sum_cons]
    congr 1
    have h := coeff_neg_logOf_one_sub_C_mul_X (-x) hk.ne'
    have harg : (1 - C (-x) * X : PowerSeries ℝ) = 1 + C x * X := by
      simp [map_neg, sub_neg_eq_add]
    rw [harg, map_neg] at h
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hsign : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    rw [neg_pow] at h
    have h := (eq_div_iff hkR).mp h
    rw [pow_succ]
    calc
      _ = (-1 : ℝ) ^ k * (-(coeff k (logOf (1 + C x * X))) * k) := by ring
      _ = (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * x ^ k) := by rw [h]
      _ = x ^ k := by rw [← mul_assoc, hsign, one_mul]

/-- Formal logarithms are continuous coefficientwise on normalized series. -/
theorem tendsto_coeff_logOf_of_coeff_tendsto
    {ι : Type*} {l : Filter ι} {a : ι → PowerSeries ℝ} {b : PowerSeries ℝ}
    (ha : ∀ i, constantCoeff (a i) = 1) (hb : constantCoeff b = 1)
    (h : ∀ j, Tendsto (fun i => coeff j (a i)) l (𝓝 (coeff j b))) (k : ℕ) :
    Tendsto (fun i => coeff k (logOf (a i))) l (𝓝 (coeff k (logOf b))) := by
  have hfa (i : ι) := coeff_subst_eq_sum_range (a i - 1) (log ℝ)
    (by simp [ha i]) k
  have hfb := coeff_subst_eq_sum_range (b - 1) (log ℝ) (by simp [hb]) k
  simp only [logOf_eq]
  simp_rw [hfa]
  rw [hfb]
  apply tendsto_finsetSum
  intro j hj
  apply Tendsto.const_mul
  apply WithPiTopology.tendsto_coeff_pow_of_coeff_tendsto
  intro n
  simpa only [map_sub] using (h n).sub tendsto_const_nhds

end PowerSeries
