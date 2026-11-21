module

public import RealRooted.Toeplitz.TrinomialRows
public import RealRooted.Toeplitz.TrinomialRoots
public import RealRooted.Basic.Coefficients
import RealRooted.Interlacing.VariableDelay
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-degree localization for a fixed-lag recurrence

The universal rows of `1 / (1 - t - y t^k)` split by the variable-delay theorem.
A positive-ratio invariant excludes the closed interval from the first negative root
through zero, including its critical endpoint. The argument is Section 3 of the
unpublished manuscript *Ndikubwayo's thesis and exact finite-degree curve containment*
(2026-10-28), tracked in RealRooted issue #2153. The published containing-curve result is
Bøgvad--Ndikubwayo--Shapiro, *Generalizing Tran's Conjecture*, arXiv:2001.09248v2,
Theorem 1.2; the strict finite-degree bound below is proved directly.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Trinomial

/-- The universal fixed-lag row `F_n(y) = [t^n] (1 - t - y t^k)⁻¹`. -/
def delayPolynomial (k n : ℕ) : ℝ[X] := row 1 k (-X) (-1) n

/-- The universal row starts at one. -/
@[simp] theorem delayPolynomial_zero (k : ℕ) : delayPolynomial k 0 = 1 := by
  simp [delayPolynomial]

/-- The universal fixed-lag recurrence, including the zero negative-index rows. -/
theorem delayPolynomial_succ {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    delayPolynomial k (n + 1) = delayPolynomial k n +
      X * if k ≤ n + 1 then delayPolynomial k (n + 1 - k) else 0 := by
  unfold delayPolynomial
  rw [row_succ (by decide : 1 ≠ 0) hk]
  simp only [show 1 ≤ n + 1 by lia, ite_true, Nat.add_sub_cancel, one_mul, neg_neg,
    neg_mul, sub_neg_eq_add]

/-- The first `k` universal rows are constant. -/
theorem delayPolynomial_of_lt {k n : ℕ} (h : n < k) : delayPolynomial k n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [delayPolynomial_succ (by lia), ite_eq_right (by lia), mul_zero, add_zero, ih (by lia)]

private theorem delayPolynomial_recurrence {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    delayPolynomial k (n + 1) = delayPolynomial k n +
      C (if k ≤ n + 1 then (1 : ℝ) else 0) * X * delayPolynomial k (n + 1 - k) := by
  rw [delayPolynomial_succ hk]
  split_ifs <;> simp

/-- Every universal fixed-lag row splits over the reals. Zero initial weights allow a direct
application of the variable-delay theorem without shifting the row indices. -/
theorem delayPolynomial_splits {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    (delayPolynomial k n).Splits := by
  exact splits_of_variableDelay_recurrence (delayPolynomial k) (fun m ↦ m - k)
    (fun m ↦ if k ≤ m then 1 else 0)
    (fun {_ _} _ hij ↦ Nat.sub_le_sub_right hij k) (fun m hm ↦ by lia)
    (fun m ↦ by split_ifs <;> norm_num) (delayPolynomial_zero k)
    (delayPolynomial_recurrence hk) n

/-- Every universal fixed-lag row has nonnegative coefficients. -/
theorem delayPolynomial_hasNonnegCoeffs {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    HasNonnegCoeffs (delayPolynomial k n) := by
  exact hasNonnegCoeffs_of_variableDelay_recurrence (delayPolynomial k) (fun m ↦ m - k)
    (fun m ↦ if k ≤ m then 1 else 0)
    (fun {_ _} _ hij ↦ Nat.sub_le_sub_right hij k) (fun m hm ↦ by lia)
    (fun m ↦ by split_ifs <;> norm_num) (delayPolynomial_zero k)
    (delayPolynomial_recurrence hk) n

/-- Every universal fixed-lag row has constant coefficient one. -/
@[simp] theorem coeff_zero_delayPolynomial {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    (delayPolynomial k n).coeff 0 = 1 := by
  exact coeff_zero_of_variableDelay_recurrence (delayPolynomial k) (fun m ↦ m - k)
    (fun m ↦ if k ≤ m then 1 else 0)
    (fun {_ _} _ hij ↦ Nat.sub_le_sub_right hij k) (fun m hm ↦ by lia)
    (fun m ↦ by split_ifs <;> norm_num) (delayPolynomial_zero k)
    (delayPolynomial_recurrence hk) n

/-- Universal fixed-lag rows never vanish identically. -/
theorem delayPolynomial_ne_zero {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    delayPolynomial k n ≠ 0 := by
  intro h
  have hc := coeff_zero_delayPolynomial hk n
  simp [h] at hc

/-- A uniform geometric lower bound for the real delay recurrence. The bound on `q` includes
its critical endpoint, so every row is strictly positive there. -/
theorem pos_and_pow_mul_le_of_delay_recurrence {k : ℕ} (hk : k ≠ 0)
    (p : ℕ → ℝ) (lam q : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hq : q ≤ lam ^ (k - 1) * (1 - lam))
    (hinit : ∀ n, n < k → p n = 1)
    (hrec : ∀ n, k ≤ n + 1 → p (n + 1) = p n - q * p (n + 1 - k)) :
    ∀ n, 0 < p n ∧ ∀ m, m ≤ n → lam ^ (n - m) * p m ≤ p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [hinit 0 (by lia)]
      refine ⟨zero_lt_one, ?_⟩
      intro m hm
      have hm0 : m = 0 := by lia
      subst m
      simp [hinit 0 (by lia)]
    | succ n =>
      have hn := ih n (by lia)
      have hstep : lam * p n ≤ p (n + 1) := by
        by_cases hkn : k ≤ n + 1
        · have hlag := ih (n + 1 - k) (by lia)
          have hdist : n - (n + 1 - k) = k - 1 := by lia
          have hchain := hn.2 (n + 1 - k) (by lia)
          rw [hdist] at hchain
          have h₁ := mul_le_mul_of_nonneg_right hq hlag.1.le
          have h₂ := mul_le_mul_of_nonneg_right hchain (sub_nonneg.mpr hlam1)
          rw [hrec n hkn]
          nlinarith
        · rw [hinit (n + 1) (by lia), hinit n (by lia), mul_one]
          exact hlam1
      refine ⟨lt_of_lt_of_le (mul_pos hlam hn.1) hstep, ?_⟩
      intro m hm
      rcases eq_or_lt_of_le hm with rfl | hm
      · simp
      · have hmn : m ≤ n := by lia
        have hchain := mul_le_mul_of_nonneg_left (hn.2 m hmn) hlam.le
        have hpow : n + 1 - m = (n - m) + 1 := by lia
        rw [hpow, pow_succ]
        nlinarith

/-- The real critical parameter of the fixed-lag recurrence. -/
def delayThreshold (k : ℕ) : ℝ := ((k - 1 : ℕ) / (k : ℝ)) ^ (k - 1) / k

/-- Universal fixed-lag rows are positive throughout the closed critical interval. -/
theorem eval_delayPolynomial_neg_pos {k : ℕ} (hk : 2 ≤ k) {q : ℝ}
    (hq : q ≤ delayThreshold k) (n : ℕ) :
    0 < (delayPolynomial k n).eval (-q) := by
  let lam : ℝ := (k - 1 : ℕ) / (k : ℝ)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by lia)
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]
  have hlam : 0 < lam := by
    exact div_pos (by exact_mod_cast (show 0 < k - 1 by lia)) hkpos
  have hlam1 : lam ≤ 1 := by dsimp [lam]; rw [div_le_one hkpos, hkcast]; linarith
  have hbound : q ≤ lam ^ (k - 1) * (1 - lam) := by
    have heq : 1 - lam = 1 / (k : ℝ) := by dsimp [lam]; rw [hkcast]; field_simp; ring
    rw [heq]
    simpa [delayThreshold, lam, div_eq_mul_inv] using hq
  exact (pos_and_pow_mul_le_of_delay_recurrence (by lia)
    (fun m ↦ (delayPolynomial k m).eval (-q)) lam q hlam hlam1 hbound
    (fun m hm ↦ by simp [delayPolynomial_of_lt hm])
    (fun m hm ↦ by simp [delayPolynomial_succ (by lia : k ≠ 0), hm, sub_eq_add_neg]) n).1

/-- Every real zero lies strictly beyond the critical endpoint. -/
theorem isRoot_delayPolynomial_lt {k : ℕ} (hk : 2 ≤ k) {n : ℕ} {y : ℝ}
    (hy : (delayPolynomial k n).IsRoot y) : y < -delayThreshold k := by
  by_contra h
  have hpos := eval_delayPolynomial_neg_pos hk (q := -y) (by linarith) n
  simp only [neg_neg] at hpos
  exact hpos.ne' hy

/-- The critical parameter is strictly positive for every lag at least two. -/
theorem delayThreshold_pos {k : ℕ} (hk : 2 ≤ k) : 0 < delayThreshold k := by
  unfold delayThreshold
  have hnum : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by lia)
  have hden : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by lia)
  positivity

/-- The reciprocal critical parameter is Tran's finite-degree upper bound. -/
theorem inv_delayThreshold {k : ℕ} (hk : 2 ≤ k) :
    (delayThreshold k)⁻¹ = (k : ℝ) ^ k / (k - 1 : ℕ) ^ (k - 1) := by
  have hden : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by lia)
  have hnum : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by lia)
  have hpow : (k : ℝ) ^ k = (k : ℝ) ^ (k - 1) * k := by
    rw [← pow_succ, Nat.sub_add_cancel (by lia : 1 ≤ k)]
  simp only [delayThreshold, div_pow, inv_div]
  rw [hpow]
  field_simp

/-- Evaluation transports the universal polynomial to scalar numerator-one rows. -/
theorem eval₂_delayPolynomial {S : Type*} [CommRing S] (f : ℝ →+* S)
    {k : ℕ} (hk : k ≠ 0) (y : S) (n : ℕ) :
    (delayPolynomial k n).eval₂ f y = row 1 k (-y) (-1) n := by
  simpa [delayPolynomial] using map_row (eval₂RingHom f y) (by decide : 1 ≠ 0) hk
    (-X : ℝ[X]) (-1) n

/-- Scaling out the linear coefficient gives the universal fixed-lag polynomial. -/
theorem row_eq_pow_mul_eval₂ {k : ℕ} (hk : k ≠ 0) (a b : ℂ) (hb : b ≠ 0) (n : ℕ) :
    row 1 k a b n = (-b) ^ n *
      (delayPolynomial k n).eval₂ Complex.ofRealHom (-a / (-b) ^ k) := by
  rw [eval₂_delayPolynomial Complex.ofRealHom hk]
  have hscale := row_rescale (by decide : 1 ≠ 0) hk
    (-(-a / (-b) ^ k)) (-1 : ℂ) (-b) n
  have ha : -(-a / (-b) ^ k) * (-b) ^ k = a := by field_simp [pow_ne_zero k (neg_ne_zero.mpr hb)]
  simpa [ha] using hscale

/-- A complex zero of a universal fixed-lag row is a real zero strictly past the endpoint. -/
theorem eval₂_delayPolynomial_eq_zero {k : ℕ} (hk : 2 ≤ k) {n : ℕ} {z : ℂ}
    (hz : (delayPolynomial k n).eval₂ Complex.ofRealHom z = 0) :
    ∃ y : ℝ, y < -delayThreshold k ∧ (y : ℂ) = z := by
  obtain ⟨y, hy⟩ : z ∈ Complex.ofRealHom.range :=
    (delayPolynomial_splits (by lia : k ≠ 0) n).mem_range_of_isRoot
      (delayPolynomial_ne_zero (by lia) n) (by simpa [IsRoot.def, eval_map] using hz)
  refine ⟨y, isRoot_delayPolynomial_lt hk (n := n) ?_, hy⟩
  have h := hz
  rw [← hy, eval₂_at_apply] at h
  exact Complex.ofRealHom.injective (by simpa using h)

/-- **Exact finite-degree Tran localization.** Every scalar row zero away from `a = 0`
has invariant in the half-open critical interval. The upper endpoint is strictly excluded
at every degree, without an eventual-degree hypothesis. -/
theorem row_zero_invariant_mem_Ico {k : ℕ} (hk : 2 ≤ k) {a b : ℂ}
    (ha : a ≠ 0) {n : ℕ} (hz : row 1 k a b n = 0) :
    ∃ w : ℝ, 0 ≤ w ∧ w < (k : ℝ) ^ k / (k - 1 : ℕ) ^ (k - 1) ∧
      (-1 : ℂ) ^ k * b ^ k / a = (w : ℂ) := by
  have hs : 0 < delayThreshold k := delayThreshold_pos hk
  by_cases hb : b = 0
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · rw [← inv_delayThreshold hk]
      exact inv_pos.mpr hs
    · simp [hb, zero_pow (by lia : k ≠ 0)]
  · rw [row_eq_pow_mul_eval₂ (by lia) a b hb n] at hz
    have hF := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero n (neg_ne_zero.mpr hb))
    obtain ⟨y, hy, heq⟩ := eval₂_delayPolynomial_eq_zero hk hF
    have hyneg : y < 0 := by linarith
    refine ⟨1 / (-y), (div_pos zero_lt_one (neg_pos.mpr hyneg)).le, ?_, ?_⟩
    · rw [← inv_delayThreshold hk, ← one_div]
      exact one_div_lt_one_div_of_lt hs (by linarith)
    · have hynz : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyneg.ne
      have hrel : (y : ℂ) * ((-1 : ℂ) ^ k * b ^ k) = -a := by
        have h := (eq_div_iff (pow_ne_zero k (neg_ne_zero.mpr hb))).mp heq
        have hc : (-b) ^ k = (-1 : ℂ) ^ k * b ^ k := by
          rw [← mul_pow, neg_one_mul]
        rw [hc] at h
        exact h
      push_cast
      field_simp
      linear_combination hrel

/-- Real polynomial rows are real-rooted when the critical inverse image is real and
common zeros of the row and `A` are real. The nonzero-row hypothesis is explicit. -/
theorem row_isRealRooted {k : ℕ} (hk : 2 ≤ k) (A B : ℝ[X]) (n : ℕ)
    (hne : row 1 k A B n ≠ 0)
    (hcurve : ∀ (z : ℂ) (w : ℝ), 0 ≤ w →
      w < (k : ℝ) ^ k / (k - 1 : ℕ) ^ (k - 1) →
      A.eval₂ Complex.ofRealHom z ≠ 0 →
      (-1 : ℂ) ^ k * (B.eval₂ Complex.ofRealHom z) ^ k /
        A.eval₂ Complex.ofRealHom z = (w : ℂ) → z.im = 0)
    (hexception : ∀ z : ℂ, A.eval₂ Complex.ofRealHom z = 0 →
      (row 1 k A B n).eval₂ Complex.ofRealHom z = 0 → z.im = 0) :
    row 1 k A B n ≠ 0 ∧ (row 1 k A B n).Splits := by
  refine ⟨hne, Polynomial.splits_of_all_roots_real ?_⟩
  intro z hz
  have hzeval : (row 1 k A B n).eval₂ Complex.ofRealHom z = 0 := by
    simpa [eval_map] using hz
  by_cases ha : A.eval₂ Complex.ofRealHom z = 0
  · exact hexception z ha hzeval
  · have hscalar : row 1 k (A.eval₂ Complex.ofRealHom z)
        (B.eval₂ Complex.ofRealHom z) n = 0 := by
      have hm := map_row (eval₂RingHom Complex.ofRealHom z) (by decide : 1 ≠ 0)
        (by lia : k ≠ 0) A B n
      exact hm.symm.trans hzeval
    obtain ⟨w, hw0, hw1, hw⟩ := row_zero_invariant_mem_Ico hk ha hscalar
    exact hcurve z w hw0 hw1 ha hw

/-- At a finite row zero away from `a = 0`, the lag-one denominator has no multiple
root: multiple roots would force the strictly excluded critical endpoint. -/
theorem not_isRoot_derivative_of_row_zero {k : ℕ} (hk : 2 ≤ k) {a b : ℂ}
    (ha : a ≠ 0) {n : ℕ} (hrow : row 1 k a b n = 0) {r : ℂ}
    (hr : (trinomial 0 1 k 1 b a).IsRoot r) :
    ¬ (trinomial 0 1 k 1 b a).derivative.IsRoot r := by
  intro hd
  obtain ⟨w, _, hlt, heq⟩ := row_zero_invariant_mem_Ico hk ha hrow
  have hcrit := invariant_eq_of_isRoot_derivative hk hr hd
  have hw : w = (k : ℝ) ^ k / (k - 1 : ℕ) ^ (k - 1) := by
    apply Complex.ofReal_injective
    push_cast
    exact heq.symm.trans hcrit
  exact hlt.ne hw

end RealRooted.Trinomial
