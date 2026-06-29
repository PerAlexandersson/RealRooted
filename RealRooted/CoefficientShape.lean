import RealRooted.Basic
import RealRooted.AissenSchoenbergWhitney
import Mathlib.Order.Preorder.Finite

/-!
# Coefficient shape consequences of real-rootedness

This file collects finite coefficient-sequence predicates used for the
classical implication chain

```text
nonnegative coefficients + real-rooted
  => ultra-log-concave coefficients
  => log-concave coefficients
  => unimodal coefficients.
```

The Newton-inequality and no-internal-zero polynomial steps are recorded as
theorem stubs.  The elementary sequence implications and the Pólya-frequency
route to log-concavity are formalized here.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-! ## Finite coefficient-sequence predicates -/

/-- A finite real sequence is nonnegative through index `d`. -/
def CoeffNonnegUpTo (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ k, k ≤ d → 0 ≤ a k

/-- A finite real sequence is log-concave through index `d`. -/
def CoeffLogConcaveUpTo (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ k, 0 < k → k < d → a (k - 1) * a (k + 1) ≤ a k ^ 2

/-- Binomial-normalized ultra-log-concavity through index `d`, without division.

Equivalently, the normalized sequence `a k / Nat.choose d k` is log-concave on
`0, ..., d`.  The division-free form is

```text
a_k^2 k (d-k) >= a_{k-1} a_{k+1} (k+1) (d-k+1).
```
-/
def CoeffUltraLogConcaveUpTo (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ k, 0 < k → k < d →
    a (k - 1) * a (k + 1) * ((k + 1 : ℝ) * ((d - k + 1 : ℕ) : ℝ)) ≤
      a k ^ 2 * ((k : ℝ) * ((d - k : ℕ) : ℝ))

/-- A finite sequence has no internal zeros through index `d`. -/
def CoeffNoInternalZerosUpTo (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ i j k, i < j → j < k → k ≤ d → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- A finite sequence is weakly unimodal through index `d`.

The index `m` is a peak: the sequence is nondecreasing up to `m` and
nonincreasing from `m` to `d`. -/
def CoeffUnimodalUpTo (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∃ m, m ≤ d ∧
    (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧
      ∀ i j, m ≤ i → i ≤ j → j ≤ d → a j ≤ a i

theorem CoeffUltraLogConcaveUpTo.logConcave {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hulc : CoeffUltraLogConcaveUpTo d a) :
    CoeffLogConcaveUpTo d a := by
  intro k hk0 hkd
  have hk_pred_le : k - 1 ≤ d := by
    lia
  have hk_succ_le : k + 1 ≤ d := by
    lia
  have hprod_nonneg : 0 ≤ a (k - 1) * a (k + 1) := by
    exact mul_nonneg (hnonneg (k - 1) hk_pred_le) (hnonneg (k + 1) hk_succ_le)
  have hk_pos_real : (0 : ℝ) < k := by
    exact_mod_cast hk0
  have hdk_pos_nat : 0 < d - k :=
    Nat.sub_pos_of_lt hkd
  have hdk_pos_real : (0 : ℝ) < ((d - k : ℕ) : ℝ) := by
    exact_mod_cast hdk_pos_nat
  have hfactor_pos : 0 < (k : ℝ) * ((d - k : ℕ) : ℝ) :=
    mul_pos hk_pos_real hdk_pos_real
  have hfactor_le :
      (k : ℝ) * ((d - k : ℕ) : ℝ) ≤
        (k + 1 : ℝ) * ((d - k + 1 : ℕ) : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k :=
      le_of_lt hk_pos_real
    have hdk_nonneg : (0 : ℝ) ≤ ((d - k : ℕ) : ℝ) :=
      le_of_lt hdk_pos_real
    norm_num at hdk_nonneg ⊢
    nlinarith
  have hmul_le := mul_le_mul_of_nonneg_left hfactor_le hprod_nonneg
  have hulc_k := hulc k hk0 hkd
  have hcombined :
      a (k - 1) * a (k + 1) * ((k : ℝ) * ((d - k : ℕ) : ℝ)) ≤
        a k ^ 2 * ((k : ℝ) * ((d - k : ℕ) : ℝ)) := by
    exact le_trans hmul_le hulc_k
  nlinarith [hcombined, hfactor_pos]

/-- If a nonnegative log-concave sequence strictly decreases at `k`, then it
strictly decreases at the next adjacent pair, provided the middle term is
nonzero. -/
lemma CoeffLogConcaveUpTo.strict_decrease_next {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hlc : CoeffLogConcaveUpTo d a)
    {k : ℕ} (hk : k + 2 ≤ d) (hdrop : a (k + 1) < a k)
    (hpos_next : a (k + 1) ≠ 0) :
    a (k + 2) < a (k + 1) := by
  have hk1_pos : 0 < k + 1 := by
    lia
  have hk1_lt : k + 1 < d := by
    lia
  have hlc_k := hlc (k + 1) hk1_pos hk1_lt
  have hprev : (k + 1) - 1 = k := by
    lia
  have hnext : (k + 1) + 1 = k + 2 := by
    lia
  rw [hprev, hnext] at hlc_k
  have hmid_nonneg : 0 ≤ a (k + 1) :=
    hnonneg (k + 1) (by lia)
  have hmid_pos : 0 < a (k + 1) :=
    lt_of_le_of_ne hmid_nonneg (Ne.symm hpos_next)
  have hnext_nonneg : 0 ≤ a (k + 2) :=
    hnonneg (k + 2) hk
  by_contra hnot
  push Not at hnot
  have hsq_le : a (k + 1) ^ 2 ≤ a (k + 1) * a (k + 2) := by
    nlinarith
  have hmul_lt : a (k + 1) * a (k + 2) < a k * a (k + 2) := by
    exact mul_lt_mul_of_pos_right hdrop (lt_of_lt_of_le hmid_pos hnot)
  nlinarith

/-- If a nonnegative log-concave sequence strictly increases at `k`, then it
strictly increases at the previous adjacent pair, provided the middle term is
nonzero. -/
lemma CoeffLogConcaveUpTo.strict_increase_prev {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hlc : CoeffLogConcaveUpTo d a)
    {k : ℕ} (hk0 : 0 < k) (hk : k + 1 ≤ d) (hrise : a k < a (k + 1))
    (hpos_k : a k ≠ 0) :
    a (k - 1) < a k := by
  have hk_lt : k < d := by
    lia
  have hlc_k := hlc k hk0 hk_lt
  have hk_nonneg : 0 ≤ a k :=
    hnonneg k (by lia)
  have hk_pos : 0 < a k :=
    lt_of_le_of_ne hk_nonneg (Ne.symm hpos_k)
  have hprev_nonneg : 0 ≤ a (k - 1) :=
    hnonneg (k - 1) (by lia)
  by_contra hnot
  push Not at hnot
  have hsq_le : a k ^ 2 ≤ a (k - 1) * a k := by
    nlinarith
  have hmul_lt : a (k - 1) * a k < a (k - 1) * a (k + 1) := by
    exact mul_lt_mul_of_pos_left hrise (lt_of_lt_of_le hk_pos hnot)
  nlinarith

/-- No strict decrease can occur before a maximal coefficient of a nonnegative
log-concave sequence with no internal zeros. -/
lemma CoeffLogConcaveUpTo.no_strict_decrease_before_max {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hnozero : CoeffNoInternalZerosUpTo d a)
    (hlc : CoeffLogConcaveUpTo d a) {m : ℕ}
    (hm_le : m ≤ d) (hmax : ∀ k, k ≤ d → a k ≤ a m) :
    ∀ i, i < m → ¬ a (i + 1) < a i := by
  intro i him hdrop
  have hsucc_nonneg : 0 ≤ a (i + 1) :=
    hnonneg (i + 1) (by lia)
  have hi_pos : 0 < a i :=
    lt_of_le_of_lt hsucc_nonneg hdrop
  have hi_ne : a i ≠ 0 :=
    ne_of_gt hi_pos
  have hm_pos : 0 < a m :=
    lt_of_lt_of_le hi_pos (hmax i (by lia))
  have hm_ne : a m ≠ 0 :=
    ne_of_gt hm_pos
  have hprop : ∀ t, i ≤ t → t < m → a (t + 1) < a t := by
    intro t hit htm
    induction t, hit using Nat.le_induction with
    | base => exact hdrop
    | succ t hit ih =>
        have ht_lt_m : t < m := by
          lia
        have hcurr : a (t + 1) < a t :=
          ih ht_lt_m
        have ht_pos : 0 < a t :=
          lt_of_le_of_lt (hnonneg (t + 1) (by lia)) hcurr
        have ht_ne : a t ≠ 0 :=
          ne_of_gt ht_pos
        have hmid_ne : a (t + 1) ≠ 0 := by
          exact hnozero t (t + 1) m (by lia) (by lia) hm_le ht_ne hm_ne
        exact hlc.strict_decrease_next hnonneg (by lia) hcurr hmid_ne
  have hlast := hprop (m - 1) (by lia) (by lia)
  have hlast_eq : (m - 1) + 1 = m := by
    lia
  rw [hlast_eq] at hlast
  have hmax_last : a (m - 1) ≤ a m :=
    hmax (m - 1) (by lia)
  linarith

/-- No strict increase can occur after a maximal coefficient of a nonnegative
log-concave sequence with no internal zeros. -/
lemma CoeffLogConcaveUpTo.no_strict_increase_after_max {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hnozero : CoeffNoInternalZerosUpTo d a)
    (hlc : CoeffLogConcaveUpTo d a) {m : ℕ}
    (hm_le : m ≤ d) (hmax : ∀ k, k ≤ d → a k ≤ a m) :
    ∀ i, m ≤ i → i < d → ¬ a i < a (i + 1) := by
  intro i hmi hid hrise
  have hi_nonneg : 0 ≤ a i :=
    hnonneg i (by lia)
  have hi_succ_pos : 0 < a (i + 1) :=
    lt_of_le_of_lt hi_nonneg hrise
  have hm_pos : 0 < a m :=
    lt_of_lt_of_le hi_succ_pos (hmax (i + 1) (by lia))
  have hm_ne : a m ≠ 0 :=
    ne_of_gt hm_pos
  have hprop : ∀ t, m < t → t ≤ i + 1 → a (t - 1) < a t := by
    intro t hmt hti
    refine Nat.decreasingInduction' (m := t) (n := i + 1)
      (P := fun u => m < u → u ≤ i + 1 → a (u - 1) < a u) ?step hti
      ?base hmt hti
    · intro k hk_lt htk ih hmk hki
      have hcurr : a ((k + 1) - 1) < a (k + 1) :=
        ih (by lia) (by lia)
      have hkeq : (k + 1) - 1 = k := by
        lia
      rw [hkeq] at hcurr
      have hk_succ_pos : 0 < a (k + 1) :=
        lt_of_le_of_lt (hnonneg k (by lia)) hcurr
      have hk_succ_ne : a (k + 1) ≠ 0 :=
        ne_of_gt hk_succ_pos
      have hk_ne : a k ≠ 0 := by
        exact hnozero m k (k + 1) (by lia) (by lia) (by lia) hm_ne hk_succ_ne
      simpa [show k - 1 + 1 = k by lia] using
        hlc.strict_increase_prev hnonneg (by lia) (by lia) hcurr hk_ne
    · intro _ _
      simpa [Nat.add_sub_cancel] using hrise
  have hfirst := hprop (m + 1) (by lia) (by lia)
  have hfirst_eq : (m + 1) - 1 = m := by
    lia
  rw [hfirst_eq] at hfirst
  have hmax_first : a (m + 1) ≤ a m :=
    hmax (m + 1) (by lia)
  linarith

/-- Classical finite-sequence lemma: a nonnegative log-concave finite sequence
with no internal zeros is unimodal. -/
theorem CoeffLogConcaveUpTo.unimodal {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hnozero : CoeffNoInternalZerosUpTo d a)
    (hlc : CoeffLogConcaveUpTo d a) :
    CoeffUnimodalUpTo d a := by
  obtain ⟨m, hmmax⟩ :=
    Finset.exists_maximalFor (fun k => a k) (Finset.range (d + 1)) ⟨0, by simp⟩
  have hm_mem : m ∈ Finset.range (d + 1) :=
    hmmax.prop
  have hm_le : m ≤ d :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hm_mem)
  have hmax : ∀ k, k ≤ d → a k ≤ a m := by
    intro k hk
    exact hmmax.le (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hleft_adj : ∀ k, k < m → a k ≤ a (k + 1) := by
    intro k hk
    exact le_of_not_gt (hlc.no_strict_decrease_before_max hnonneg hnozero hm_le hmax k hk)
  have hright_adj : ∀ k, m ≤ k → k < d → a (k + 1) ≤ a k := by
    intro k hmk hkd
    exact le_of_not_gt (hlc.no_strict_increase_after_max hnonneg hnozero hm_le hmax k hmk hkd)
  refine ⟨m, hm_le, ?_, ?_⟩
  · intro i j hij hjm
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
        have hj_le_m : j ≤ m := by
          lia
        exact le_trans (ih hj_le_m) (hleft_adj j (by lia))
  · intro i j hmi hij hjd
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
        have hj_le_d : j ≤ d := by
          lia
        have hstep : a (j + 1) ≤ a j :=
          hright_adj j (by lia) (by lia)
        exact le_trans hstep (ih hj_le_d)

theorem CoeffUltraLogConcaveUpTo.unimodal {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hnozero : CoeffNoInternalZerosUpTo d a)
    (hulc : CoeffUltraLogConcaveUpTo d a) :
    CoeffUnimodalUpTo d a :=
  (hulc.logConcave hnonneg).unimodal hnonneg hnozero

/-! ## Polya-frequency consequences -/

/-- The `2 × 2` Toeplitz minors of a Pólya-frequency sequence are exactly
log-concavity of the sequence. -/
theorem IsPolyaFreqSeq.logConcaveUpTo {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    (d : ℕ) :
    CoeffLogConcaveUpTo d a := by
  intro k hk0 hkd
  have hdet : 0 ≤ ((toeplitz a).submatrix ![k, k + 1] ![0, 1]).det := by
    exact hpf (by simp [StrictMono]) (by decide)
  have h1k : 1 ≤ k :=
    hk0
  simpa [toeplitz, Matrix.det_fin_two, h1k, pow_two] using hdet

/-! ## Polynomial coefficient wrappers -/

/-- Polynomial coefficients are log-concave up to the natural degree. -/
def HasLogConcaveCoeffs (p : ℝ[X]) : Prop :=
  CoeffLogConcaveUpTo p.natDegree fun k => p.coeff k

/-- Polynomial coefficients are ultra-log-concave up to the natural degree. -/
def HasUltraLogConcaveCoeffs (p : ℝ[X]) : Prop :=
  CoeffUltraLogConcaveUpTo p.natDegree fun k => p.coeff k

/-- Polynomial coefficients have no internal zeros up to the natural degree. -/
def HasNoInternalCoeffZeros (p : ℝ[X]) : Prop :=
  CoeffNoInternalZerosUpTo p.natDegree fun k => p.coeff k

/-- Polynomial coefficients are unimodal up to the natural degree. -/
def HasUnimodalCoeffs (p : ℝ[X]) : Prop :=
  CoeffUnimodalUpTo p.natDegree fun k => p.coeff k

theorem coeffNonnegUpTo_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    CoeffNonnegUpTo p.natDegree fun k => p.coeff k :=
  fun k _ => hp k

theorem HasUltraLogConcaveCoeffs.logConcave {p : ℝ[X]} (hpnn : HasNonnegCoeffs p)
    (hulc : HasUltraLogConcaveCoeffs p) :
    HasLogConcaveCoeffs p :=
  CoeffUltraLogConcaveUpTo.logConcave
    (coeffNonnegUpTo_of_hasNonnegCoeffs hpnn) hulc

theorem HasLogConcaveCoeffs.unimodal {p : ℝ[X]} (hpnn : HasNonnegCoeffs p)
    (hnozero : HasNoInternalCoeffZeros p) (hlc : HasLogConcaveCoeffs p) :
    HasUnimodalCoeffs p :=
  CoeffLogConcaveUpTo.unimodal
    (coeffNonnegUpTo_of_hasNonnegCoeffs hpnn) hnozero hlc

theorem HasUltraLogConcaveCoeffs.unimodal {p : ℝ[X]} (hpnn : HasNonnegCoeffs p)
    (hnozero : HasNoInternalCoeffZeros p) (hulc : HasUltraLogConcaveCoeffs p) :
    HasUnimodalCoeffs p :=
  (hulc.logConcave hpnn).unimodal hpnn hnozero

theorem hasLogConcaveCoeffs_of_isPolyaFreqSeq_coeff {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq fun n => p.coeff n) :
    HasLogConcaveCoeffs p :=
  hpf.logConcaveUpTo p.natDegree

/-- Newton inequalities for nonnegative real-rooted polynomials, stated as
ultra-log-concavity of the coefficient sequence. -/
theorem hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasUltraLogConcaveCoeffs p := by
  sorry

/-- Nonnegative real-rooted polynomials have no internal coefficient zeros. -/
theorem hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasNoInternalCoeffZeros p := by
  sorry

theorem hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasLogConcaveCoeffs p := by
  apply hasLogConcaveCoeffs_of_isPolyaFreqSeq_coeff
  rcases hrr with rfl | hsplits
  · simpa using IsPolyaFreqSeq_zero
  · exact aissenSchoenbergWhitney_reverse hpnn hsplits
      (roots_nonpos_of_nonneg_coeffs hsplits hpnn)

theorem hasUnimodalCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasUnimodalCoeffs p :=
  (hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn hrr).unimodal hpnn
    (hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn hrr)

end RealRooted
