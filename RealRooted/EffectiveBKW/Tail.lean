module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Effective BKW majorant tails

The cofactor degree is `e`. Its inverse coefficients are majorized by the coefficients of
`(1 - X)⁻ᵉ`. We use a shifted infinite sum for each tail, so natural subtraction also covers
numerator terms whose index exceeds the cutoff. The zero-degree case is the delta sequence.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open scoped BigOperators

/-- The natural coefficient of `(1 - X)⁻ᵉ`, including the constant series at `e = 0`. -/
def majorantCoeff : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | e + 1, k => (k + e).choose e

/-- The majorant agrees with Mathlib's inverse-power series. -/
theorem coeff_invOneSubPow (e k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOneSubPow ℝ e).val = (majorantCoeff e k : ℝ) := by
  cases e with
  | zero => simp [majorantCoeff, PowerSeries.invOneSubPow_zero, PowerSeries.coeff_one]
  | succ e => simp [majorantCoeff, PowerSeries.invOneSubPow, Nat.add_comm]

/-- The full majorant series has sum `(1 - q)⁻ᵉ`. -/
theorem hasSum_majorantCoeff {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (e : ℕ) :
    HasSum (fun k ↦ (majorantCoeff e k : ℝ) * q ^ k) (1 / (1 - q) ^ e) := by
  cases e with
  | zero =>
      have h : (fun k ↦ (majorantCoeff 0 k : ℝ) * q ^ k) =
          (fun k : ℕ ↦ if k = 0 then (1 : ℝ) else 0) := by
        funext k
        by_cases hk : k = 0 <;> simp [majorantCoeff, hk]
      simpa [h] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  | succ e =>
      simpa [majorantCoeff] using
        hasSum_choose_mul_geometric_of_norm_lt_one e
          (r := q) (by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1)

/-- The part of the majorant series starting at coefficient `M`. -/
noncomputable def majorantTail (q : ℝ) (e M : ℕ) : ℝ :=
  ∑' k, (majorantCoeff e (k + M) : ℝ) * q ^ (k + M)

/-- The shifted tail equals the threshold-indicator form of the series. -/
theorem majorantTail_eq_tsum_ite (q : ℝ) (e M : ℕ) :
    majorantTail q e M =
      ∑' k, if M ≤ k then (majorantCoeff e k : ℝ) * q ^ k else 0 := by
  have hr : Function.support (fun k ↦
      if M ≤ k then (majorantCoeff e k : ℝ) * q ^ k else 0) ⊆
      Set.range (fun k : ℕ ↦ k + M) := by
    intro k hk
    have hMk : M ≤ k := by
      by_contra h
      simp [h] at hk
    exact ⟨k - M, Nat.sub_add_cancel hMk⟩
  have h := (add_left_injective M).tsum_eq hr
  simpa only [majorantTail, Nat.le_add_left, ite_true] using h

/-- An infinite majorant tail is the full sum minus its finite prefix. -/
theorem majorantTail_eq_sub {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (e M : ℕ) :
    majorantTail q e M =
      1 / (1 - q) ^ e - ∑ k ∈ Finset.range M, (majorantCoeff e k : ℝ) * q ^ k := by
  have h := (hasSum_majorantCoeff hq hq1 e).summable.sum_add_tsum_nat_add M
  rw [(hasSum_majorantCoeff hq hq1 e).tsum_eq] at h
  exact eq_sub_of_add_eq' h

/-- The weighted tail controlling the BKW remainder at row `n`. -/
noncomputable def tail (q : ℝ) (β : List ℝ) (e n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range β.length, β.getD j 0 * majorantTail q e (n + 2 - j)

/-- The tail has the threshold form used in the BKW remainder estimate. -/
theorem tail_eq_tsum (q : ℝ) (β : List ℝ) (e n : ℕ) :
    tail q β e n = ∑ j ∈ Finset.range β.length, β.getD j 0 *
      ∑' k, if n + 2 ≤ j + k then (majorantCoeff e k : ℝ) * q ^ k else 0 := by
  unfold tail
  apply Finset.sum_congr rfl
  intro j _
  rw [majorantTail_eq_tsum_ite]
  apply congrArg (fun x : ℝ ↦ β.getD j 0 * x)
  apply tsum_congr
  intro k
  simp only [show n + 2 - j ≤ k ↔ n + 2 ≤ j + k by lia]

/-- The effective BKW tail is an explicitly evaluable finite expression. -/
theorem tail_eq_closedForm {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (β : List ℝ) (e n : ℕ) :
    tail q β e n = ∑ j ∈ Finset.range β.length, β.getD j 0 *
      (1 / (1 - q) ^ e -
        ∑ k ∈ Finset.range (n + 2 - j), (majorantCoeff e k : ℝ) * q ^ k) := by
  simp only [tail, majorantTail_eq_sub hq hq1]

/-- Every majorant tail is nonnegative at a nonnegative argument. -/
theorem majorantTail_nonneg {q : ℝ} (hq : 0 ≤ q) (e M : ℕ) :
    0 ≤ majorantTail q e M := by
  exact tsum_nonneg fun k ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)

/-- Increasing the starting index decreases a majorant tail. -/
theorem majorantTail_antitone {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (e : ℕ) :
    Antitone (majorantTail q e) := by
  intro M L hML
  rw [majorantTail_eq_sub hq hq1, majorantTail_eq_sub hq hq1]
  exact sub_le_sub_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hML)
    (fun k _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))) _

/-- Nonnegative numerator weights make the BKW tail nonnegative. -/
theorem tail_nonneg {q : ℝ} (hq : 0 ≤ q) (β : List ℝ)
    (hβ : ∀ j, 0 ≤ β.getD j 0) (e n : ℕ) : 0 ≤ tail q β e n := by
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hβ j) (majorantTail_nonneg hq e _)

/-- The uniform tail bound propagates from one cutoff to every later row. -/
theorem tail_antitone {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (β : List ℝ)
    (hβ : ∀ j, 0 ≤ β.getD j 0) (e : ℕ) : Antitone (tail q β e) := by
  intro n m hnm
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
    (majorantTail_antitone hq hq1 e (Nat.sub_le_sub_right (Nat.add_le_add_right hnm 2) j))
    (hβ j)

/-- The degree-two majorant coefficient is `k + 1`. -/
theorem majorantCoeff_two (k : ℕ) : majorantCoeff 2 k = k + 1 := by
  simp [majorantCoeff]

/-- A finite arithmetic-geometric sum, with its denominator cleared in the proof. -/
private theorem sum_range_succ_mul_pow {q : ℝ} (hq : q ≠ 1) (M : ℕ) :
    ∑ k ∈ Finset.range M, ((k : ℝ) + 1) * q ^ k =
      (1 - q ^ M * ((M : ℝ) + 1 - M * q)) / (1 - q) ^ 2 := by
  have h : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [pow_succ]
      field_simp
      ring

/-- The pilot's arithmetic-geometric closed form, valid also at `M = 0`. -/
theorem majorantTail_two {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    majorantTail q 2 M = q ^ M * ((M : ℝ) + 1 - M * q) / (1 - q) ^ 2 := by
  rw [majorantTail_eq_sub hq hq1]
  simp only [majorantCoeff_two, Nat.cast_add, Nat.cast_one]
  rw [sum_range_succ_mul_pow (ne_of_lt hq1)]
  ring

/-- A polynomial factor times a geometric power explicitly bounds the quadratic tail. -/
theorem majorantTail_two_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    majorantTail q 2 M ≤ q ^ M * ((M : ℝ) + 1) / (1 - q) ^ 2 := by
  rw [majorantTail_two hq hq1]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
  linarith [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) hq]

/-- The exact degree-two bound used to select the pilot cutoff. -/
theorem tail_two_eq {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (β : List ℝ) (n : ℕ) :
    tail q β 2 n = ∑ j ∈ Finset.range β.length, β.getD j 0 *
      (q ^ (n + 2 - j) * ((n + 2 - j : ℕ) + 1 - (n + 2 - j : ℕ) * q) /
        (1 - q) ^ 2) := by
  simp only [tail, majorantTail_two hq hq1]

/-- A weighted polynomial-geometric bound for quadratic cofactors. -/
theorem tail_two_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (β : List ℝ)
    (hβ : ∀ j, 0 ≤ β.getD j 0) (n : ℕ) :
    tail q β 2 n ≤ ∑ j ∈ Finset.range β.length, β.getD j 0 *
      (q ^ (n + 2 - j) * ((n + 2 - j : ℕ) + 1) / (1 - q) ^ 2) := by
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (majorantTail_two_le hq hq1 _) (hβ j)

/-- A verified cutoff remains valid at every larger row. -/
theorem tail_lt_of_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (β : List ℝ)
    (hβ : ∀ j, 0 ≤ β.getD j 0) (e : ℕ) {N n : ℕ} {m : ℝ}
    (hN : tail q β e N < m) (hn : N ≤ n) : tail q β e n < m := by
  exact (tail_antitone hq hq1 β hβ e hn).trans_lt hN

end RealRooted.EffectiveBKW
