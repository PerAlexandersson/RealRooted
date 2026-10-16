module

public import RealRooted.Applications.EulerianCompendium.Definitions
public import RealRooted.Applications.EulerianCompendium.TernaryRecurrence
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Ternary words and increasing runs

We identify the recurrence polynomial in `RealRooted` with the enumerator of
actual words in the ordered alphabet `0 < 1 < 2`.  The statistic counts
maximal consecutive strictly increasing factors, including the empty word's
zero factors.  This is the combinatorial identification cited in the proof
of Paper `thm:ternaryRuns`.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

namespace RealRooted.EulerianCompendium

/-- Read a word at a natural-number position, with a harmless default outside its range. -/
def ternaryWordLetterAt {n : ℕ} (w : Fin n → Fin 3) (i : ℕ) : Fin 3 :=
  if h : i < n then w ⟨i, h⟩ else 0

/-- The strictly increasing adjacent positions of a ternary word. -/
def ternaryWordAscents {n : ℕ} (w : Fin n → Fin 3) : Finset ℕ :=
  (Finset.range (n - 1)).filter fun i =>
    ternaryWordLetterAt w i < ternaryWordLetterAt w (i + 1)

/-- The number of maximal strictly increasing runs in a ternary word.

Each strict ascent joins two adjacent letters into the same run; every other
adjacent pair starts a new run.  Thus a word of length `n` has `n` runs minus
its number of strict ascents. -/
def ternaryWordRunCount {n : ℕ} (w : Fin n → Fin 3) : ℕ :=
  n - (ternaryWordAscents w).card

/-- The actual increasing-run enumerator of all ternary words of length `n`.
The empty word contributes `1`. -/
def ternaryWordRunEnumerator (n : ℕ) : ℝ[X] :=
  ∑ w : Fin n → Fin 3, X ^ ternaryWordRunCount w

@[simp] theorem ternaryWordRunEnumerator_zero :
    ternaryWordRunEnumerator 0 = 1 := by
  simp [ternaryWordRunEnumerator, ternaryWordRunCount, ternaryWordAscents]

/-- Append one letter to the end of a finite word. -/
def ternaryWordSnoc {n : ℕ} (w : Fin n → Fin 3) (a : Fin 3) : Fin (n + 1) → Fin 3 :=
  Fin.snoc w a

/-- The contribution from words of length `n + 1` with a specified final letter. -/
def ternaryWordEndingEnumerator (n : ℕ) (a : Fin 3) : ℝ[X] :=
  ∑ w : Fin n → Fin 3, X ^ ternaryWordRunCount (ternaryWordSnoc w a)

/-- Every nonempty word is uniquely a prefix followed by its final letter. -/
def ternaryWordSnocEquiv (n : ℕ) :
    (Fin n → Fin 3) × Fin 3 ≃ (Fin (n + 1) → Fin 3) where
  toFun p := ternaryWordSnoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last n))
  left_inv p := by simp [ternaryWordSnoc]
  right_inv w := Fin.snoc_init_self w

/-- Reindex the actual word enumerator by prefix and final letter. -/
theorem ternaryWordRunEnumerator_succ_eq_snoc_sum (n : ℕ) :
    ternaryWordRunEnumerator (n + 1) =
      ∑ w : Fin n → Fin 3, ∑ a : Fin 3,
        X ^ ternaryWordRunCount (ternaryWordSnoc w a) := by
  calc
    _ = ∑ p : (Fin n → Fin 3) × Fin 3,
        X ^ ternaryWordRunCount (ternaryWordSnoc p.1 p.2) := by
      unfold ternaryWordRunEnumerator
      exact Fintype.sum_equiv (ternaryWordSnocEquiv n).symm
        (fun w => X ^ ternaryWordRunCount w)
        (fun p => X ^ ternaryWordRunCount (ternaryWordSnoc p.1 p.2))
        (by intro w; simp [ternaryWordSnocEquiv, ternaryWordSnoc])
    _ = _ := by rw [Fintype.sum_prod_type]

/-- Splitting nonempty words by their last letter. -/
theorem ternaryWordRunEnumerator_succ_eq_ending (n : ℕ) :
    ternaryWordRunEnumerator (n + 1) =
      ∑ a : Fin 3, ternaryWordEndingEnumerator n a := by
  rw [ternaryWordRunEnumerator_succ_eq_snoc_sum]
  exact Finset.sum_comm

@[simp] theorem ternaryWordLetterAt_snoc_prefix {n : ℕ} (w : Fin n → Fin 3) (a : Fin 3)
    {i : ℕ} (hi : i < n) :
    ternaryWordLetterAt (ternaryWordSnoc w a) i = ternaryWordLetterAt w i := by
  have hidx : (⟨i, by lia⟩ : Fin (n + 1)) = (⟨i, hi⟩ : Fin n).castSucc := by
    ext
    rfl
  change (if h : i < n + 1 then
      ((Fin.snoc w a : Fin (n + 1) → Fin 3) ⟨i, h⟩) else 0) =
    if h : i < n then w ⟨i, h⟩ else 0
  rw [dite_eq_left (show i < n + 1 by lia), dite_eq_left hi]
  change (ternaryWordSnoc w a) ⟨i, show i < n + 1 by lia⟩ = w ⟨i, hi⟩
  calc
    (ternaryWordSnoc w a) ⟨i, show i < n + 1 by lia⟩ =
        (ternaryWordSnoc w a) ((⟨i, hi⟩ : Fin n).castSucc) :=
      congrArg (ternaryWordSnoc w a) hidx
    _ = w ⟨i, hi⟩ := by
      simpa only [ternaryWordSnoc] using
        (@Fin.snoc_castSucc n (fun _ : Fin (n + 1) => Fin 3) a w ⟨i, hi⟩)

@[simp] theorem ternaryWordLetterAt_snoc_last {n : ℕ} (w : Fin n → Fin 3) (a : Fin 3) :
    ternaryWordLetterAt (ternaryWordSnoc w a) n = a := by
  have hidx : (⟨n, by lia⟩ : Fin (n + 1)) = Fin.last n := by
    ext
    simp
  change (if h : n < n + 1 then
      ((Fin.snoc w a : Fin (n + 1) → Fin 3) ⟨n, h⟩) else 0) = a
  rw [dite_eq_left (show n < n + 1 by lia)]
  change (ternaryWordSnoc w a) ⟨n, show n < n + 1 by lia⟩ = a
  calc
    (ternaryWordSnoc w a) ⟨n, show n < n + 1 by lia⟩ =
        (ternaryWordSnoc w a) (Fin.last n) := congrArg (ternaryWordSnoc w a) hidx
    _ = a := by
      simpa only [ternaryWordSnoc] using
        (@Fin.snoc_last n (fun _ : Fin (n + 1) => Fin 3) a w)

theorem ternaryWordAscents_snoc {n : ℕ} (w : Fin n → Fin 3) (a : Fin 3) :
    ternaryWordAscents (ternaryWordSnoc w a) =
      if n = 0 then ∅ else
        if ternaryWordLetterAt w (n - 1) < a then
          insert (n - 1) (ternaryWordAscents w)
        else ternaryWordAscents w := by
  cases n with
  | zero => simp [ternaryWordAscents]
  | succ n =>
      have hprefix :
          (Finset.range n).filter (fun i =>
            ternaryWordLetterAt (ternaryWordSnoc w a) i <
              ternaryWordLetterAt (ternaryWordSnoc w a) (i + 1)) =
            ternaryWordAscents w := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, ternaryWordAscents]
        constructor
        · rintro ⟨hi, hlt⟩
          rw [ternaryWordLetterAt_snoc_prefix w a (by lia)] at hlt
          rw [ternaryWordLetterAt_snoc_prefix w a (by lia)] at hlt
          exact ⟨hi, hlt⟩
        · rintro ⟨hi, hlt⟩
          refine ⟨hi, ?_⟩
          rw [ternaryWordLetterAt_snoc_prefix w a (by lia)]
          rw [ternaryWordLetterAt_snoc_prefix w a (by lia)]
          exact hlt
      have hfinal :
          (ternaryWordLetterAt (ternaryWordSnoc w a) n <
            ternaryWordLetterAt (ternaryWordSnoc w a) (n + 1)) ↔
            ternaryWordLetterAt w n < a := by
        simp only [ternaryWordLetterAt_snoc_prefix (w := w) (a := a) (i := n) (by lia),
          ternaryWordLetterAt_snoc_last]
      simp only [ternaryWordAscents]
      change (Finset.range (n + 1)).filter _ = _
      rw [Finset.range_add_one, Finset.filter_insert]
      simp [hprefix, ternaryWordAscents]

theorem ternaryWordRunCount_snoc {n : ℕ} (w : Fin n → Fin 3) (a : Fin 3) :
    ternaryWordRunCount (ternaryWordSnoc w a) =
      ternaryWordRunCount w +
        if n = 0 then 1 else
          if ternaryWordLetterAt w (n - 1) < a then 0 else 1 := by
  by_cases hn : n = 0
  · subst n
    simp [ternaryWordRunCount, ternaryWordAscents]
  · have hcard : (ternaryWordAscents w).card ≤ n - 1 := by
      change ((Finset.range (n - 1)).filter _).card ≤ n - 1
      calc
        _ ≤ (Finset.range (n - 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = n - 1 := by simp
    rw [ternaryWordRunCount, ternaryWordRunCount, ternaryWordAscents_snoc]
    by_cases hasc : ternaryWordLetterAt w (n - 1) < a
    · have hnot : n - 1 ∉ ternaryWordAscents w := by
        simp [ternaryWordAscents, Finset.mem_filter, Finset.mem_range]
      simp [hn, hasc, hnot]
    · have hnot : n - 1 ∉ ternaryWordAscents w := by
        simp [ternaryWordAscents, Finset.mem_filter, Finset.mem_range]
      simp [hn, hasc]
      lia

/-- Transition of the three last-letter enumerators when one letter is appended. -/
theorem ternaryWordEndingEnumerator_succ (n : ℕ) (b : Fin 3) :
    ternaryWordEndingEnumerator (n + 1) b =
      ∑ c : Fin 3,
        if c < b then ternaryWordEndingEnumerator n c
        else ternaryWordEndingEnumerator n c * X := by
  unfold ternaryWordEndingEnumerator
  calc
    _ = ∑ p : (Fin n → Fin 3) × Fin 3,
        X ^ ternaryWordRunCount
          (ternaryWordSnoc (ternaryWordSnoc p.1 p.2) b) := by
      exact Fintype.sum_equiv (ternaryWordSnocEquiv n).symm
        (fun w : Fin (n + 1) → Fin 3 =>
          (X : ℝ[X]) ^ ternaryWordRunCount (ternaryWordSnoc w b))
        (fun p : (Fin n → Fin 3) × Fin 3 => (X : ℝ[X]) ^ ternaryWordRunCount
          (ternaryWordSnoc (ternaryWordSnoc p.1 p.2) b))
        (by intro w; simp [ternaryWordSnocEquiv, ternaryWordSnoc])
    _ = ∑ c : Fin 3, ∑ w : Fin n → Fin 3,
        X ^ ternaryWordRunCount
          (ternaryWordSnoc (ternaryWordSnoc w c) b) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      have hrun (w : Fin n → Fin 3) :
          ternaryWordRunCount (ternaryWordSnoc (ternaryWordSnoc w c) b) =
            ternaryWordRunCount (ternaryWordSnoc w c) +
              if c < b then 0 else 1 := by
        rw [ternaryWordRunCount_snoc]
        simp
      calc
        _ = ∑ w : Fin n → Fin 3,
            if c < b then
              X ^ ternaryWordRunCount (ternaryWordSnoc w c)
            else X ^ ternaryWordRunCount (ternaryWordSnoc w c) * X := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [hrun w]
          by_cases hc : c < b <;> simp [hc, pow_succ]
        _ = if c < b then ternaryWordEndingEnumerator n c
            else ternaryWordEndingEnumerator n c * X := by
          by_cases hc : c < b
          · simp [hc, ternaryWordEndingEnumerator]
          · simp [hc, ternaryWordEndingEnumerator, Finset.sum_mul]

theorem ternaryWordEndingEnumerator_succ_zero (n : ℕ) :
    ternaryWordEndingEnumerator (n + 1) 0 =
      ternaryWordEndingEnumerator n 0 * X +
        ternaryWordEndingEnumerator n 1 * X +
        ternaryWordEndingEnumerator n 2 * X := by
  rw [ternaryWordEndingEnumerator_succ, Fin.sum_univ_three]
  norm_num [Polynomial.C_ofNat]

theorem ternaryWordEndingEnumerator_succ_one (n : ℕ) :
    ternaryWordEndingEnumerator (n + 1) 1 =
      ternaryWordEndingEnumerator n 0 +
        ternaryWordEndingEnumerator n 1 * X +
        ternaryWordEndingEnumerator n 2 * X := by
  rw [ternaryWordEndingEnumerator_succ, Fin.sum_univ_three]
  norm_num

theorem ternaryWordEndingEnumerator_succ_two (n : ℕ) :
    ternaryWordEndingEnumerator (n + 1) 2 =
      ternaryWordEndingEnumerator n 0 +
        ternaryWordEndingEnumerator n 1 +
        ternaryWordEndingEnumerator n 2 * X := by
  rw [ternaryWordEndingEnumerator_succ, Fin.sum_univ_three]
  norm_num

@[simp] theorem ternaryWordEndingEnumerator_zero (a : Fin 3) :
    ternaryWordEndingEnumerator 0 a = X := by
  simp [ternaryWordEndingEnumerator, ternaryWordRunCount,
    ternaryWordAscents, ternaryWordSnoc, ternaryWordLetterAt]

theorem ternaryWordEndingEnumerator_one_zero :
    ternaryWordEndingEnumerator 1 0 = 3 * X ^ 2 := by
  rw [ternaryWordEndingEnumerator_succ_zero 0]
  simp
  ring

theorem ternaryWordEndingEnumerator_one_one :
    ternaryWordEndingEnumerator 1 1 = X + 2 * X ^ 2 := by
  rw [ternaryWordEndingEnumerator_succ_one 0]
  simp
  ring

theorem ternaryWordEndingEnumerator_one_two :
    ternaryWordEndingEnumerator 1 2 = 2 * X + X ^ 2 := by
  rw [ternaryWordEndingEnumerator_succ_two 0]
  simp
  ring

theorem ternaryWordEndingEnumerator_two_zero :
    ternaryWordEndingEnumerator 2 0 = 3 * X ^ 2 + 6 * X ^ 3 := by
  change ternaryWordEndingEnumerator (1 + 1) 0 = _
  rw [ternaryWordEndingEnumerator_succ_zero 1,
    ternaryWordEndingEnumerator_one_zero,
    ternaryWordEndingEnumerator_one_one,
    ternaryWordEndingEnumerator_one_two]
  ring

theorem ternaryWordEndingEnumerator_two_one :
    ternaryWordEndingEnumerator 2 1 = 6 * X ^ 2 + 3 * X ^ 3 := by
  change ternaryWordEndingEnumerator (1 + 1) 1 = _
  rw [ternaryWordEndingEnumerator_succ_one 1,
    ternaryWordEndingEnumerator_one_zero,
    ternaryWordEndingEnumerator_one_one,
    ternaryWordEndingEnumerator_one_two]
  ring

theorem ternaryWordEndingEnumerator_two_two :
    ternaryWordEndingEnumerator 2 2 = X + 7 * X ^ 2 + X ^ 3 := by
  change ternaryWordEndingEnumerator (1 + 1) 2 = _
  rw [ternaryWordEndingEnumerator_succ_two 1,
    ternaryWordEndingEnumerator_one_zero,
    ternaryWordEndingEnumerator_one_one,
    ternaryWordEndingEnumerator_one_two]
  ring

theorem ternaryWordRunEnumerator_two :
    ternaryWordRunEnumerator 2 = 3 * X + 6 * X ^ 2 := by
  rw [ternaryWordRunEnumerator_succ_eq_ending, Fin.sum_univ_three,
    ternaryWordEndingEnumerator_one_zero,
    ternaryWordEndingEnumerator_one_one,
    ternaryWordEndingEnumerator_one_two]
  ring

theorem ternaryWordRunEnumerator_three :
    ternaryWordRunEnumerator 3 =
      3 * X * (3 * X + 6 * X ^ 2) +
        3 * X * (1 - X) * (3 * X) + X * (1 - X) ^ 2 := by
  rw [ternaryWordRunEnumerator_succ_eq_ending, Fin.sum_univ_three,
    ternaryWordEndingEnumerator_two_zero,
    ternaryWordEndingEnumerator_two_one,
    ternaryWordEndingEnumerator_two_two]
  ring

/-- The word enumerators satisfy the cubic recurrence obtained by eliminating
the three possible final letters. -/
theorem ternaryWordRunEnumerator_succ_three_step (n : ℕ) :
    ternaryWordRunEnumerator (n + 4) =
      3 * X * ternaryWordRunEnumerator (n + 3) +
        3 * X * (1 - X) * ternaryWordRunEnumerator (n + 2) +
        X * (1 - X) ^ 2 * ternaryWordRunEnumerator (n + 1) := by
  simp only [ternaryWordRunEnumerator_succ_eq_ending, Fin.sum_univ_three,
    ternaryWordEndingEnumerator_succ_zero,
    ternaryWordEndingEnumerator_succ_one,
    ternaryWordEndingEnumerator_succ_two]
  ring

/-- Appending each of the three letters gives the literal transition sum. -/
theorem ternaryWordRunEnumerator_succ_append_formula (n : ℕ) :
    ternaryWordRunEnumerator (n + 1) =
      ∑ w : Fin n → Fin 3, ∑ a : Fin 3,
        X ^ (ternaryWordRunCount w +
          if n = 0 then 1 else
            if ternaryWordLetterAt w (n - 1) < a then 0 else 1) := by
  rw [ternaryWordRunEnumerator_succ_eq_snoc_sum]
  simp_rw [ternaryWordRunCount_snoc]

theorem ternaryWordRunEnumerator_one :
    ternaryWordRunEnumerator 1 = C 3 * X := by
  rw [ternaryWordRunEnumerator_succ_append_formula]
  simp only [ternaryWordRunCount, ternaryWordAscents, Nat.zero_sub,
    Finset.range_zero, Finset.filter_empty, Finset.card_empty, zero_add,
    pow_one, Finset.univ_unique,
    ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Finset.card_singleton, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one, one_mul,
    Polynomial.C_ofNat]

/-- The actual finite-word enumerator agrees with the constant-coefficient model. -/
theorem ternaryWordRunEnumerator_eq_threeStep (n : ℕ) :
    ternaryWordRunEnumerator n = ternaryRunThreeStep n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · rw [ternaryWordRunEnumerator_zero]
      rfl
    · rw [ternaryWordRunEnumerator_one]
      simp only [ternaryRunThreeStep, Polynomial.C_ofNat]
    · rw [ternaryWordRunEnumerator_two]
      simp only [ternaryRunThreeStep]
    · rw [ternaryWordRunEnumerator_three]
      change _ = ternaryRunThreeStep (0 + 3)
      rw [ternaryRunThreeStep_succ_three 0]
      simp only [ternaryRunThreeStep, mul_one]
    · have h3 := ih (n + 3) (by lia)
      have h2 := ih (n + 2) (by lia)
      have h1 := ih (n + 1) (by lia)
      calc
        ternaryWordRunEnumerator (n + 4) =
            3 * X * ternaryWordRunEnumerator (n + 3) +
              3 * X * (1 - X) * ternaryWordRunEnumerator (n + 2) +
              X * (1 - X) ^ 2 * ternaryWordRunEnumerator (n + 1) :=
          ternaryWordRunEnumerator_succ_three_step n
        _ = 3 * X * ternaryRunThreeStep (n + 3) +
              3 * X * (1 - X) * ternaryRunThreeStep (n + 2) +
              X * (1 - X) ^ 2 * ternaryRunThreeStep (n + 1) := by
          rw [h3, h2, h1]
        _ = ternaryRunThreeStep (n + 4) := by
          rw [show n + 4 = (n + 1) + 3 by lia,
            ternaryRunThreeStep_succ_three (n + 1)]

/-- The paper's ternary-run polynomial enumerates actual ternary words. -/
theorem ternaryWordRunEnumerator_eq_ternaryRunPolynomial (n : ℕ) :
    ternaryWordRunEnumerator n = ternaryRunPolynomial n := by
  rw [ternaryWordRunEnumerator_eq_threeStep, ternaryRunThreeStep_eq]

end RealRooted.EulerianCompendium
