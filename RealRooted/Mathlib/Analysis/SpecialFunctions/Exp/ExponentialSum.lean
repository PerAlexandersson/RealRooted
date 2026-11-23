/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumBounds
public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.CompletelyMonotone.Limits
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Ring

/-!
# Heat traces of positive summable spectra

The trace `sum exp (-rate * time)` and all its natural spectral moments
are completely monotone on the open positive half-line. Derivatives and
the two asymptotic estimates in Zhang, arXiv:1506.07012v13, Lemma 2,
follow under an explicit inverse-moment summability hypothesis.

The exponential decay estimate allows a rate equal to the spectral lower
bound. Strict positivity needs a nonempty spectrum; no value at time zero
is asserted for infinite spectra.
-/

public section

open Filter Topology

namespace Real

/-- The natural spectral moment of an exponential sum. Its heat trace is
the case `k = 0`. Analytic assertions below are restricted to positive time. -/
@[expose] noncomputable def exponentialMomentSum {ι : Type*}
    (r : ι → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑' i, r i ^ k * exp (-r i * t)

/-- All spectral moments are nonnegative for positive rates. -/
theorem exponentialMomentSum_nonneg {ι : Type*} {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (k : ℕ) (t : ℝ) :
    0 ≤ exponentialMomentSum r k t :=
  tsum_nonneg fun i ↦ mul_nonneg (pow_nonneg (hr i).le _) (exp_nonneg _)

/-- A nonempty positive spectrum gives strictly positive spectral moments
whenever an inverse moment is summable. -/
theorem exponentialMomentSum_pos {ι : Type*} [Nonempty ι] {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) {t : ℝ} (ht : 0 < t) : 0 < exponentialMomentSum r k t := by
  let i : ι := Classical.arbitrary ι
  exact (summable_pow_mul_exp_neg_mul hr ha hs k ht).tsum_pos
    (fun j ↦ mul_nonneg (pow_nonneg (hr j).le _) (exp_nonneg _)) i
    (mul_pos (pow_pos (hr i) _) (exp_pos _))

/-- Each natural spectral moment is completely monotone on positive time.
Finite partial sums converge pointwise; complete monotonicity is closed
under these limits without a separate smoothness assumption. -/
theorem isCompletelyMonotoneOnIoi_exponentialMomentSum
    {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) : TauCeti.IsCompletelyMonotoneOnIoi (exponentialMomentSum r k) := by
  classical
  apply TauCeti.isCompletelyMonotoneOnIoi_of_tendsto
    (L := atTop) (F := fun s : Finset ι ↦ fun t ↦ ∑ i ∈ s, r i ^ k * exp (-r i * t))
  · exact Filter.Eventually.of_forall fun s ↦
      (TauCeti.IsCompletelyMonotone.sum (s := s) fun i _ ↦ by
        exact ((TauCeti.isCompletelyMonotone_exp_neg_mul (hr i).le).smul
          (pow_nonneg (hr i).le k)).congr fun t _ ↦ by
            simp only [Pi.smul_apply, smul_eq_mul]).isCompletelyMonotoneOnIoi
  · intro t ht
    exact (summable_pow_mul_exp_neg_mul hr ha hs k ht).hasSum

/-- Local uniform summability of one further spectral moment justifies
termwise differentiation of the exponential sum. -/
theorem hasDerivAt_exponentialMomentSum {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (exponentialMomentSum r k) (-exponentialMomentSum r (k + 1) t) t := by
  have hterm (i : ι) (y : ℝ) (_hy : y ∈ Set.Ioi (t / 2)) :
      HasDerivAt (fun z : ℝ ↦ r i ^ k * exp (-r i * z))
        (-(r i ^ (k + 1) * exp (-r i * y))) y := by
    convert (((hasDerivAt_id y).const_mul (-r i)).exp).const_mul (r i ^ k) using 1
    · simp only [id_eq]
    · simp only [id_eq, mul_one, pow_succ]
      ring
  have hbound (i : ι) (y : ℝ) (hy : y ∈ Set.Ioi (t / 2)) :
      ‖-(r i ^ (k + 1) * exp (-r i * y))‖ ≤
        r i ^ (k + 1) * exp (-r i * (t / 2)) := by
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (hr i).le _) (exp_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (hr i).le _)
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hy.le (neg_nonpos.mpr (hr i).le)
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_pow_mul_exp_neg_mul hr ha hs (k + 1) (half_pos ht))
    isOpen_Ioi isPreconnected_Ioi hterm hbound
    (show t ∈ Set.Ioi (t / 2) from half_lt_self ht)
    (summable_pow_mul_exp_neg_mul hr ha hs k ht)
    (show t ∈ Set.Ioi (t / 2) from half_lt_self ht)
  convert h using 1
  · rfl
  · rw [tsum_neg]
    rfl

/-- All derivatives of the heat trace are signed spectral moments. -/
theorem iteratedDeriv_exponentialMomentSum_zero {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (exponentialMomentSum r 0) t =
      (-1 : ℝ) ^ k * exponentialMomentSum r k t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
      have heq : iteratedDeriv k (exponentialMomentSum r 0) =ᶠ[𝓝 t]
          (fun y ↦ (-1 : ℝ) ^ k * exponentialMomentSum r k y) :=
        Filter.Eventually.mono (isOpen_Ioi.mem_nhds ht) fun y hy ↦ ih hy
      have hd := (hasDerivAt_exponentialMomentSum hr ha hs k ht).const_mul ((-1 : ℝ) ^ k)
      rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv, pow_succ]
      ring

/-- Zhang's small-time estimate, valid for any nonnegative summable inverse
spectral exponent and every derivative. -/
theorem isBigO_iteratedDeriv_exponentialMomentSum_zero_nhdsWithin
    {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) :
    (iteratedDeriv k (exponentialMomentSum r 0)) =O[𝓝[>] (0 : ℝ)]
      (fun t ↦ t ^ (-(a + (k : ℝ)))) := by
  obtain ⟨C, _, hC⟩ := exists_tsum_pow_mul_exp_neg_mul_le hr ha hs k
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [iteratedDeriv_exponentialMomentSum_zero hr ha hs k ht, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (exponentialMomentSum_nonneg hr k t),
    abs_of_pos (rpow_pos_of_pos ht _)]
  exact hC t ht

/-- Any lower spectral bound controls exponential decay, including when
the decay rate equals the smallest eigenvalue. -/
theorem exponentialMomentSum_le_exp_mul {ι : Type*} {r : ι → ℝ} {a b t : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (hb : ∀ i, b ≤ r i) (k : ℕ) (ht : 1 ≤ t) :
    exponentialMomentSum r k t ≤
      (exp b * exponentialMomentSum r k 1) * exp (-b * t) := by
  have hterm (i : ι) : r i ^ k * exp (-r i * t) ≤
      (exp b * exp (-b * t)) * (r i ^ k * exp (-r i * 1)) := by
    have harg : -r i * t ≤ b + (-b * t) + (-r i * 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hb i)) (sub_nonneg.mpr ht)]
    calc _ ≤ r i ^ k * exp (b + (-b * t) + (-r i * 1)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) (pow_nonneg (hr i).le _)
      _ = _ := by rw [exp_add, exp_add]; ring
  calc exponentialMomentSum r k t
      ≤ ∑' i, (exp b * exp (-b * t)) * (r i ^ k * exp (-r i * 1)) :=
        Summable.tsum_le_tsum hterm
          (summable_pow_mul_exp_neg_mul hr ha hs k (zero_lt_one.trans_le ht))
          ((summable_pow_mul_exp_neg_mul hr ha hs k zero_lt_one).mul_left _)
    _ = _ := by rw [tsum_mul_left]; unfold exponentialMomentSum; ring

/-- Zhang's large-time estimate, with the stronger admissible endpoint
`b ≤ r i` for every spectral rate. A positive `b` gives actual decay. -/
theorem isBigO_iteratedDeriv_exponentialMomentSum_zero_atTop
    {ι : Type*} {r : ι → ℝ} {a b : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (hb : ∀ i, b ≤ r i) (k : ℕ) :
    (iteratedDeriv k (exponentialMomentSum r 0)) =O[atTop]
      (fun t ↦ exp (-b * t)) := by
  apply Asymptotics.IsBigO.of_bound (exp b * exponentialMomentSum r k 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [iteratedDeriv_exponentialMomentSum_zero hr ha hs k (zero_lt_one.trans_le ht),
    norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (exponentialMomentSum_nonneg hr k t), abs_of_pos (exp_pos _)]
  exact exponentialMomentSum_le_exp_mul hr ha hs hb k ht

end Real
