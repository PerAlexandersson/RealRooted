import RealRooted.Basic
import RealRooted.AissenSchoenbergWhitney
import RealRooted.NewtonAux
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Polynomial.Vieta

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
  have hprod_nonneg : 0 ≤ a (k - 1) * a (k + 1) :=
    mul_nonneg (hnonneg (k - 1) (by lia)) (hnonneg (k + 1) (by lia))
  have hk_pos_real : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdk_pos_real : (0 : ℝ) < ((d - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hkd
  have hfactor_pos : 0 < (k : ℝ) * ((d - k : ℕ) : ℝ) :=
    mul_pos hk_pos_real hdk_pos_real
  have hfactor_le :
      (k : ℝ) * ((d - k : ℕ) : ℝ) ≤
        (k + 1 : ℝ) * ((d - k + 1 : ℕ) : ℝ) := by
    have hdk_nonneg : (0 : ℝ) ≤ ((d - k : ℕ) : ℝ) :=
      le_of_lt hdk_pos_real
    norm_num at hdk_nonneg ⊢
    nlinarith
  have hmul_le := mul_le_mul_of_nonneg_left hfactor_le hprod_nonneg
  have hulc_k := hulc k hk0 hkd
  have hcombined :
      a (k - 1) * a (k + 1) * ((k : ℝ) * ((d - k : ℕ) : ℝ)) ≤
        a k ^ 2 * ((k : ℝ) * ((d - k : ℕ) : ℝ)) :=
    le_trans hmul_le hulc_k
  nlinarith [hcombined, hfactor_pos]

/-- If a nonnegative log-concave sequence strictly decreases at `k`, then it
strictly decreases at the next adjacent pair, provided the middle term is
nonzero. -/
lemma CoeffLogConcaveUpTo.strict_decrease_next {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hlc : CoeffLogConcaveUpTo d a)
    {k : ℕ} (hk : k + 2 ≤ d) (hdrop : a (k + 1) < a k)
    (hpos_next : a (k + 1) ≠ 0) :
    a (k + 2) < a (k + 1) := by
  have hlc_k := hlc (k + 1) (by lia) (by lia)
  rw [show (k + 1) - 1 = k by lia,
    show (k + 1) + 1 = k + 2 by lia] at hlc_k
  have hmid_nonneg : 0 ≤ a (k + 1) :=
    hnonneg (k + 1) (by lia)
  have hmid_pos : 0 < a (k + 1) :=
    lt_of_le_of_ne hmid_nonneg (Ne.symm hpos_next)
  by_contra hnot
  push Not at hnot
  nlinarith [hlc_k, hdrop, hmid_pos, hnot]

/-- If a nonnegative log-concave sequence strictly increases at `k`, then it
strictly increases at the previous adjacent pair, provided the middle term is
nonzero. -/
lemma CoeffLogConcaveUpTo.strict_increase_prev {d : ℕ} {a : ℕ → ℝ}
    (hnonneg : CoeffNonnegUpTo d a) (hlc : CoeffLogConcaveUpTo d a)
    {k : ℕ} (hk0 : 0 < k) (hk : k + 1 ≤ d) (hrise : a k < a (k + 1))
    (hpos_k : a k ≠ 0) :
    a (k - 1) < a k := by
  have hlc_k := hlc k hk0 (by lia)
  have hk_nonneg : 0 ≤ a k :=
    hnonneg k (by lia)
  have hk_pos : 0 < a k :=
    lt_of_le_of_ne hk_nonneg (Ne.symm hpos_k)
  by_contra hnot
  push Not at hnot
  nlinarith [hlc_k, hrise, hk_pos, hnot]

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
        have hmid_ne : a (t + 1) ≠ 0 :=
          hnozero t (t + 1) m (by lia) (by lia) hm_le ht_ne hm_ne
        exact hlc.strict_decrease_next hnonneg (by lia) hcurr hmid_ne
  have hlast : a m < a (m - 1) := by
    simpa [show (m - 1) + 1 = m by lia] using hprop (m - 1) (by lia) (by lia)
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
      have hcurr : a k < a (k + 1) := by
        simpa [show (k + 1) - 1 = k by lia] using ih (by lia) (by lia)
      have hk_succ_pos : 0 < a (k + 1) :=
        lt_of_le_of_lt (hnonneg k (by lia)) hcurr
      have hk_succ_ne : a (k + 1) ≠ 0 :=
        ne_of_gt hk_succ_pos
      have hk_ne : a k ≠ 0 :=
        hnozero m k (k + 1) (by lia) (by lia) (by lia) hm_ne hk_succ_ne
      simpa [show k - 1 + 1 = k by lia] using
        hlc.strict_increase_prev hnonneg (by lia) (by lia) hcurr hk_ne
    · intro _ _
      simpa [Nat.add_sub_cancel] using hrise
  have hfirst : a m < a (m + 1) := by simpa using hprop (m + 1) (by lia) (by lia)
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
  have hmax : ∀ k, k ≤ d → a k ≤ a m :=
    fun k hk => hmmax.le (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hleft_adj : ∀ k, k < m → a k ≤ a (k + 1) :=
    fun k hk =>
      le_of_not_gt (hlc.no_strict_decrease_before_max hnonneg hnozero hm_le hmax k hk)
  have hright_adj : ∀ k, m ≤ k → k < d → a (k + 1) ≤ a k :=
    fun k hmk hkd =>
      le_of_not_gt (hlc.no_strict_increase_after_max hnonneg hnozero hm_le hmax k hmk hkd)
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
  simpa [toeplitz, Matrix.det_fin_two, show 1 ≤ k from hk0, pow_two] using
    (hpf (by simp [StrictMono]) (by decide) :
      0 ≤ ((toeplitz a).submatrix ![k, k + 1] ![0, 1]).det)

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

/-- Elementary symmetric functions of a nonnegative multiset are nonnegative. -/
lemma esymm_nonneg_of_forall_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    0 ≤ s.esymm n := by
  rw [Multiset.esymm]
  apply Multiset.sum_nonneg
  intro y hy
  rw [Multiset.mem_map] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [Multiset.mem_powersetCard] at ht
  exact Multiset.prod_nonneg (fun x hx => hs x (Multiset.mem_of_le ht.1 hx))

/-- For a nonnegative multiset, positivity of `esymm a` propagates downwards. -/
lemma esymm_pos_mono_of_forall_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x)
    {a b : ℕ} (hb : b ≤ a) (ha : 0 < s.esymm a) :
    0 < s.esymm b := by
  rw [Multiset.esymm] at ha
  obtain ⟨P, hP_mem, hP_pos⟩ : ∃ P ∈ s.powersetCard a, 0 < P.prod := by
    by_contra hcon
    push Not at hcon
    have hzero : ((s.powersetCard a).map Multiset.prod).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro y hy
      rw [Multiset.mem_map] at hy
      obtain ⟨P, hPmem, rfl⟩ := hy
      have hge : 0 ≤ P.prod := by
        rw [Multiset.mem_powersetCard] at hPmem
        exact Multiset.prod_nonneg (fun x hx => hs x (Multiset.mem_of_le hPmem.1 hx))
      have hle := hcon P hPmem
      linarith
    rw [hzero] at ha
    exact lt_irrefl 0 ha
  rw [Multiset.mem_powersetCard] at hP_mem
  obtain ⟨hPle, hPcard⟩ := hP_mem
  have hP_all_pos : ∀ x ∈ P, 0 < x := by
    intro x hx
    refine lt_of_le_of_ne (hs x (Multiset.mem_of_le hPle hx)) ?_
    intro h
    rw [← h] at hx
    exact (ne_of_gt hP_pos) (Multiset.prod_eq_zero hx)
  have hne : P.powersetCard b ≠ 0 := by
    rw [← Multiset.card_pos, Multiset.card_powersetCard, hPcard]
    exact Nat.choose_pos hb
  obtain ⟨Q, hQ_mem⟩ := Multiset.exists_mem_of_ne_zero hne
  rw [Multiset.mem_powersetCard] at hQ_mem
  obtain ⟨hQle, hQcard⟩ := hQ_mem
  have hQ_le_s : Q ≤ s := le_trans hQle hPle
  have hQ_pos : 0 < Q.prod :=
    Multiset.prod_pos (fun x hx => hP_all_pos x (Multiset.mem_of_le hQle hx))
  rw [Multiset.esymm]
  calc
    0 < Q.prod := hQ_pos
    _ ≤ ((s.powersetCard b).map Multiset.prod).sum := by
      apply Multiset.single_le_sum
      · intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨R, hR, rfl⟩ := hy
        rw [Multiset.mem_powersetCard] at hR
        exact Multiset.prod_nonneg (fun x hx => hs x (Multiset.mem_of_le hR.1 hx))
      · rw [Multiset.mem_map]
        exact ⟨Q, Multiset.mem_powersetCard.mpr ⟨hQ_le_s, hQcard⟩, rfl⟩

/-- Vieta-type formula rewriting a coefficient of a split polynomial in terms of
the elementary symmetric function of the negated roots. -/
lemma coeff_eq_leadingCoeff_mul_esymm_neg_roots {p : ℝ[X]} (hp : p.Splits) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (p.roots.map Neg.neg).esymm (p.natDegree - k) := by
  rw [Polynomial.coeff_eq_esymm_roots_of_splits hp hk, Multiset.esymm_neg]
  ring

/-- Newton inequalities for nonnegative real-rooted polynomials, stated as
ultra-log-concavity of the coefficient sequence. -/
theorem hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasUltraLogConcaveCoeffs p := by
  rcases hrr with rfl | hsplits
  · intro k hk0 hkd
    simp only [natDegree_zero] at hkd
    lia
  · intro k hk0 hkd
    set t := p.roots.map Neg.neg with ht_def
    have htcard : Multiset.card t = p.natDegree := by
      rw [ht_def, Multiset.card_map, card_roots_of_splits hsplits]
    have hc1 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hsplits (k := k - 1) (by lia)
    have hck := coeff_eq_leadingCoeff_mul_esymm_neg_roots hsplits (k := k) (by lia)
    have hc2 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hsplits (k := k + 1) (by lia)
    rw [← ht_def] at hc1 hck hc2
    have idx1 : p.natDegree - (k - 1) = p.natDegree - k + 1 := by
      lia
    have idx2 : p.natDegree - (k + 1) = p.natDegree - k - 1 := by
      lia
    rw [idx1] at hc1
    rw [idx2] at hc2
    have hnewton := NewtonAux.newton_esymm_ineq t (n := p.natDegree)
      (m := p.natDegree - k) htcard (by lia) (by lia)
    have hnm1 : p.natDegree - (p.natDegree - k) = k := by
      lia
    rw [hnm1] at hnewton
    change p.coeff (k - 1) * p.coeff (k + 1) *
        ((k + 1 : ℝ) * ((p.natDegree - k + 1 : ℕ) : ℝ)) ≤
      p.coeff k ^ 2 * ((k : ℝ) * ((p.natDegree - k : ℕ) : ℝ))
    rw [hc1, hck, hc2]
    have hscaled := mul_le_mul_of_nonneg_left hnewton (sq_nonneg p.leadingCoeff)
    have hcast1 :
        ((p.natDegree - k + 1 : ℕ) : ℝ) = ((p.natDegree - k : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    have hcast2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast1]
    rw [hcast2] at hnewton hscaled
    nlinarith [hscaled, sq_nonneg p.leadingCoeff]

/-- Nonnegative real-rooted polynomials have no internal coefficient zeros. -/
theorem hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasNoInternalCoeffZeros p := by
  rcases hrr with rfl | hsplits
  · intro i j k _ _ _ hai _
    simp at hai
  · intro i j k hij hjk hkd hai _
    have hp0 : p ≠ 0 := by rintro rfl; simp at hai
    have hlc : 0 < p.leadingCoeff := hpnn.pos_leadingCoeff hp0
    have hroots_nonpos := roots_nonpos_of_nonneg_coeffs hsplits hpnn
    have ht : ∀ x ∈ p.roots.map Neg.neg, 0 ≤ x := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      simpa using neg_nonneg.mpr (hroots_nonpos r hr)
    have hid : i ≤ p.natDegree := by
      by_contra h
      exact hai (Polynomial.coeff_eq_zero_of_natDegree_lt (by lia))
    have hjd : j ≤ p.natDegree := le_of_lt (lt_of_lt_of_le hjk hkd)
    have hcoeff_i := coeff_eq_leadingCoeff_mul_esymm_neg_roots hsplits hid
    have hei : 0 < (p.roots.map Neg.neg).esymm (p.natDegree - i) := by
      rcases lt_or_eq_of_le
          (esymm_nonneg_of_forall_nonneg ht (p.natDegree - i)) with h | h
      · exact h
      · exact absurd (show p.coeff i = 0 by rw [hcoeff_i, ← h]; ring) hai
    have hb : p.natDegree - j ≤ p.natDegree - i := by
      lia
    have hej : 0 < (p.roots.map Neg.neg).esymm (p.natDegree - j) :=
      esymm_pos_mono_of_forall_nonneg ht hb hei
    have hcoeff_j := coeff_eq_leadingCoeff_mul_esymm_neg_roots hsplits hjd
    change p.coeff j ≠ 0
    rw [hcoeff_j]
    exact ne_of_gt (mul_pos hlc hej)

theorem hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasLogConcaveCoeffs p := by
  rcases hrr with rfl | hsplits
  · exact hasLogConcaveCoeffs_of_isPolyaFreqSeq_coeff (by simpa using IsPolyaFreqSeq_zero)
  · exact hasLogConcaveCoeffs_of_isPolyaFreqSeq_coeff <|
      aissenSchoenbergWhitney_reverse hpnn hsplits
      (roots_nonpos_of_nonneg_coeffs hsplits hpnn)

theorem hasUnimodalCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hrr : p = 0 ∨ p.Splits) :
    HasUnimodalCoeffs p :=
  (hasLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn hrr).unimodal hpnn
    (hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits hpnn hrr)

end RealRooted
