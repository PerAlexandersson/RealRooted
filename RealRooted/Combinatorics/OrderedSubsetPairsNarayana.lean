import RealRooted.Mathlib.Combinatorics.Enumerative.OrderedSubsetPairs
import RealRooted.NarayanaTransformation

/-!
# Ordered subset-pair Narayana counts

This module connects the ordered subset-pair ballot count to the `m = 1`
Narayana coefficient already developed in `RealRooted.NarayanaTransformation`.
-/

namespace Finset

/-- The ordered `k`-subset pairs of `range n` are counted by the `m = 1`
Narayana coefficient. -/
theorem card_orderedKSubsetPairs_eq_narayanaTransformCoeff_one (n k : ℕ) :
    ((orderedKSubsetPairs n k).card : ℝ) = RealRooted.narayanaTransformCoeff 1 n k := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkn : k ≤ n
    · have hcard := card_orderedKSubsetPairs_eq_choose_sq_sub (n := n) (k := k) hkpos
      have hsum := card_orderedKSubsetPairs_add_card_badPrefixSubsetPairs n k
      rw [card_badPrefixSubsetPairs n k hkpos] at hsum
      have hbad_le : Nat.choose n (k - 1) * Nat.choose n (k + 1) ≤
          Nat.choose n k * Nat.choose n k := by
        rw [← hsum]
        exact Nat.le_add_left _ _
      rw [hcard, Nat.cast_sub hbad_le]
      simpa [pow_two] using
        RealRooted.choose_sq_sub_choose_pred_mul_choose_succ_eq_narayanaTransformCoeff_one
          hkpos hkn
    · have hnk : n < k := Nat.lt_of_not_ge hkn
      rw [card_orderedKSubsetPairs_eq_zero_of_lt hnk,
        RealRooted.narayanaTransformCoeff_eq_zero_of_lt (m := 1) hnk]
      norm_num

/-- Closed-form Nat cardinality for ordered `k`-subset pairs of `range n`. -/
theorem card_orderedKSubsetPairs_eq_choose_mul_choose_succ_div (n k : ℕ) :
    (orderedKSubsetPairs n k).card =
      Nat.choose n k * Nat.choose (n + 1) k / (k + 1) := by
  have hreal := card_orderedKSubsetPairs_eq_narayanaTransformCoeff_one n k
  have hmulR : (((k + 1) * (orderedKSubsetPairs n k).card : ℕ) : ℝ) =
      (Nat.choose n k * Nat.choose (n + 1) k : ℕ) := by
    rw [Nat.cast_mul, hreal]
    unfold RealRooted.narayanaTransformCoeff
    rw [show Nat.choose (1 + k) k = k + 1 by
      simp [Nat.add_comm, Nat.choose_succ_self_right]]
    norm_num [Nat.cast_add]
    field_simp [show (k + 1 : ℝ) ≠ 0 by positivity]
  exact Nat.eq_div_of_mul_eq_right (by simp) (Nat.cast_injective hmulR)

end Finset
