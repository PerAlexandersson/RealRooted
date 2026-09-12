import RealRooted.Mathlib.Algebra.Polynomial.Expand.Splits
import RealRooted.MultiplierSequence.Infinite

/-!
# Sign classification of multiplier sequences

This file proves the zero-safe parity sign constraint for an arbitrary
multiplier sequence and derives the classical four-way PF normalization.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Expanding a diagonal transform along `X ↦ X ^ d` selects the subsequence
whose indices are multiples of `d`. -/
theorem expand_diagonalOperator_mul (gamma : ℕ → ℝ) {d : ℕ} (hd : 0 < d)
    (p : ℝ[X]) :
    expand ℝ d (diagonalOperator (fun j => gamma (d * j)) p) =
      diagonalOperator gamma (expand ℝ d p) := by
  ext n
  conv_rhs => rw [coeff_diagonalOperator]
  rw [coeff_expand hd, coeff_diagonalOperator, coeff_expand hd]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    simp [Nat.mul_div_cancel_left j hd]
  · simp

/-- Any two entries of a multiplier sequence whose indices have the same
parity have compatible signs. The arbitrary gap is essential when intervening
entries vanish. -/
theorem IsMultiplierSequence.parity_mul_nonneg
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma) (k m : ℕ) :
    0 ≤ gamma k * gamma (k + 2 * m) := by
  by_cases hk : gamma k = 0
  · simp [hk]
  by_cases hkm : gamma (k + 2 * m) = 0
  · simp [hkm]
  let delta := fun j => gamma (j + k)
  let even := fun j => delta (2 * j)
  let q := diagonalOperator even ((X - 1) ^ m)
  have hdelta : IsMultiplierSequence delta := by
    simpa [delta] using hgamma.shift k
  have hinput : ((X ^ 2 - 1 : ℝ[X]) ^ m) =
      expand ℝ 2 ((X - 1) ^ m) := by
    rw [map_pow]
    congr 1
    simp [expand_eq_comp_X_pow]
  have hexpand : expand ℝ 2 q =
      diagonalOperator delta ((X ^ 2 - 1) ^ m) := by
    rw [hinput]
    exact expand_diagonalOperator_mul delta (by norm_num) ((X - 1) ^ m)
  have hp : (((X ^ 2 - 1 : ℝ[X])) ^ m).Splits := by
    have hminus : ((X - 1 : ℝ[X])).Splits := by
      simpa using Polynomial.Splits.X_sub_C (1 : ℝ)
    have hplus : ((X + 1 : ℝ[X])).Splits := by
      simpa using Polynomial.Splits.X_sub_C (-1 : ℝ)
    rw [show (X ^ 2 - 1 : ℝ[X]) = (X - 1) * (X + 1) by ring]
    exact (hminus.mul hplus).pow m
  rcases hdelta.diagonalOperator_eq_zero_or_splits hp with hzero | hsplits
  · have hqzero : q = 0 := by
      apply Polynomial.expand_injective (R := ℝ) (by norm_num : 0 < 2)
      rw [hexpand, hzero, map_zero]
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hqzero
    have hbase0 : ((X - 1 : ℝ[X]) ^ m).coeff 0 = (-1 : ℝ) ^ m := by
      rw [coeff_zero_eq_eval_zero]
      simp
    have hqcoeff0 : q.coeff 0 = gamma k * (-1 : ℝ) ^ m := by
      simp [q, even, delta, coeff_diagonalOperator, hbase0]
    rw [hqcoeff0] at hcoeff
    simp only [coeff_zero] at hcoeff
    exact (hk ((mul_eq_zero.mp hcoeff).resolve_right
      (pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0)))).elim
  · rw [← hexpand] at hsplits
    obtain ⟨hqsplit, hroots⟩ :=
      Polynomial.splits_and_forall_roots_nonneg_of_splits_expand_two q hsplits
    have hbaseMonic : ((X - 1 : ℝ[X]) ^ m).Monic := by
      simpa only [C_1] using (monic_X_sub_C (1 : ℝ)).pow m
    have hbaseDeg : ((X - 1 : ℝ[X]) ^ m).natDegree = m := by
      have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
        simpa only [C_1] using natDegree_X_sub_C (R := ℝ) (1 : ℝ)
      rw [natDegree_pow, hlin, mul_one]
    have hbaseCoeff : ((X - 1 : ℝ[X]) ^ m).coeff m = 1 := by
      simpa [leadingCoeff, hbaseDeg] using hbaseMonic.leadingCoeff
    have hbase0 : ((X - 1 : ℝ[X]) ^ m).coeff 0 = (-1 : ℝ) ^ m := by
      rw [coeff_zero_eq_eval_zero]
      simp
    have hqdeg_le : q.natDegree ≤ m :=
      (natDegree_diagonalOperator_le even ((X - 1) ^ m)).trans hbaseDeg.le
    have hqcoeffm : q.coeff m = gamma (k + 2 * m) := by
      simp [q, even, delta, coeff_diagonalOperator, hbaseCoeff,
        Nat.add_comm]
    have hqdeg : q.natDegree = m :=
      natDegree_eq_of_le_of_coeff_ne_zero hqdeg_le (hqcoeffm.trans_ne hkm)
    have hqlead : q.leadingCoeff = gamma (k + 2 * m) := by
      rw [leadingCoeff, hqdeg, hqcoeffm]
    have hqcoeff0 : q.coeff 0 = gamma k * (-1 : ℝ) ^ m := by
      simp [q, even, delta, coeff_diagonalOperator, hbase0]
    have hprod : 0 ≤ q.roots.prod := Multiset.prod_nonneg hroots
    have hvieta := hqsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
    rw [hqcoeff0, hqdeg, hqlead] at hvieta
    have hrelmul : (-1 : ℝ) ^ m * gamma k =
        (-1 : ℝ) ^ m * (gamma (k + 2 * m) * q.roots.prod) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hvieta
    have hrel : gamma k = gamma (k + 2 * m) * q.roots.prod :=
      mul_left_cancel₀ (pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0)) hrelmul
    rw [hrel]
    calc
      (gamma (k + 2 * m) * q.roots.prod) * gamma (k + 2 * m) =
          gamma (k + 2 * m) ^ 2 * q.roots.prod := by ring
      _ ≥ 0 := mul_nonneg (sq_nonneg _) hprod

/-- Adjacent entries of the same parity have compatible signs. -/
theorem IsMultiplierSequence.mul_add_two_nonneg
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma) (k : ℕ) :
    0 ≤ gamma k * gamma (k + 2) := by
  simpa using hgamma.parity_mul_nonneg k 1

/-- Even-indexed entries of a multiplier sequence are pairwise
sign-compatible. -/
theorem IsMultiplierSequence.even_mul_nonneg
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma) (a b : ℕ) :
    0 ≤ gamma (2 * a) * gamma (2 * b) := by
  by_cases hab : a ≤ b
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
    simpa [Nat.mul_add] using hgamma.parity_mul_nonneg (2 * a) m
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hba
    simpa [Nat.mul_add, Nat.add_mul, mul_comm] using
      hgamma.parity_mul_nonneg (2 * b) m

/-- Odd-indexed entries of a multiplier sequence are pairwise
sign-compatible. -/
theorem IsMultiplierSequence.odd_mul_nonneg
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma) (a b : ℕ) :
    0 ≤ gamma (2 * a + 1) * gamma (2 * b + 1) := by
  by_cases hab : a ≤ b
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hgamma.parity_mul_nonneg (2 * a + 1) m
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hba
    simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, mul_comm] using
        hgamma.parity_mul_nonneg (2 * b + 1) m

/-- Every multiplier sequence becomes a PF multiplier sequence after one of
the four classical global sign normalizations: identity, global negation,
alternation, or negated alternation. -/
theorem IsMultiplierSequence.exists_pf_sign_normalization
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma) :
    (IsPFMultiplierSequence gamma ∨
        IsPFMultiplierSequence (fun k => -gamma k)) ∨
      (IsPFMultiplierSequence (fun k => (-1 : ℝ) ^ k * gamma k) ∨
        IsPFMultiplierSequence (fun k => -((-1 : ℝ) ^ k * gamma k))) := by
  have signDichotomy (f : ℕ → ℝ) (h : ∀ a b, 0 ≤ f a * f b) :
      (∀ a, 0 ≤ f a) ∨ (∀ a, f a ≤ 0) := by
    by_cases hnonneg : ∀ a, 0 ≤ f a
    · exact Or.inl hnonneg
    · push Not at hnonneg
      obtain ⟨a, ha⟩ := hnonneg
      exact Or.inr fun b => by
        have hab := h a b
        nlinarith
  rcases signDichotomy (fun a => gamma (2 * a)) hgamma.even_mul_nonneg with
      heven | heven <;>
    rcases signDichotomy (fun a => gamma (2 * a + 1)) hgamma.odd_mul_nonneg with
      hodd | hodd
  · left
    left
    exact hgamma.toPF fun k => by
      obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' k
      · exact heven a
      · exact hodd a
  · right
    left
    exact hgamma.alternating.toPF fun k => by
      obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' k
      · simpa [pow_mul] using heven a
      · simpa [pow_succ, pow_mul] using hodd a
  · right
    right
    have hmult : IsMultiplierSequence
        (fun k => -((-1 : ℝ) ^ k * gamma k)) := by
      simpa using hgamma.alternating.const_mul (-1)
    exact hmult.toPF fun k => by
      obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' k
      · simpa [pow_mul] using heven a
      · simpa [pow_succ, pow_mul] using hodd a
  · left
    right
    have hmult : IsMultiplierSequence (fun k => -gamma k) := by
      simpa using hgamma.const_mul (-1)
    exact hmult.toPF fun k => by
      obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' k
      · simpa using heven a
      · simpa using hodd a

end RealRooted
