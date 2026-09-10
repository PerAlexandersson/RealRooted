import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Mathlib.Analysis.Polynomial.Asymptotics

/-!
# Eventually polynomial Pólya-frequency sequences

This file records eventual positivity for a Pólya-frequency sequence whose
tail is given by evaluations of a nonzero polynomial.
-/

open Filter Polynomial

namespace RealRooted

/-- The Toeplitz matrix of the causal forward difference is obtained by
subtracting the next column entrywise. This is an entrywise identity, not a
total-nonnegativity preservation result. -/
theorem toeplitz_causalFwdDiff (a : ℕ → ℝ) (i j : ℕ) :
    toeplitz (Function.causalFwdDiff a) i j =
      toeplitz a i j - toeplitz a i (j + 1) := by
  by_cases hji : j ≤ i
  · rw [toeplitz_apply, if_pos hji, toeplitz_apply, if_pos hji]
    by_cases hzero : i - j = 0
    · have hij : i = j := Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hji
      subst i
      simp [toeplitz_apply, Function.causalFwdDiff]
    · have hpos : 0 < i - j := Nat.pos_of_ne_zero hzero
      have hsucc : j + 1 ≤ i := by
        exact Nat.succ_le_iff.mpr (Nat.lt_of_sub_pos hpos)
      rw [toeplitz_apply, if_pos hsucc]
      have hindex : i - j = i - (j + 1) + 1 := by
        lia
      rw [hindex]
      simp [Function.causalFwdDiff]
  · have hsucc : ¬ j + 1 ≤ i := fun h => hji (le_trans (Nat.le_succ _) h)
    simp [toeplitz_apply, hji, hsucc]

/-- A Pólya-frequency sequence which eventually agrees with evaluations of a
nonzero real polynomial is eventually strictly positive. -/
theorem IsPolyaFreqSeq.eventually_pos_of_eventually_polynomial
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) :
    ∀ᶠ n in atTop, 0 < a n :=
  Polynomial.eventually_pos_of_eventually_nonneg_of_eventually_eq_eval_nat hp
    (Eventually.of_forall ha.nonneg) hap

end RealRooted
