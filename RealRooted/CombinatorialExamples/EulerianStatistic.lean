import RealRooted.Mathlib.Combinatorics.Enumerative.EulerianPeak
import RealRooted.Mathlib.Combinatorics.Enumerative.GenPoly
import RealRooted.GeneralizedEulerian

open scoped BigOperators Polynomial
open Polynomial

noncomputable section

namespace RealRooted

private lemma coeff_eulerianNumber (n k : ℕ) :
    (Equiv.Perm.eulerianNumber (n + 1) k : ℝ) =
      (generalizedEulerian 1 n).coeff k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero =>
          rw [Equiv.Perm.eulerianNumber_succ_zero]
          simp [generalizedEulerian, Polynomial.coeff_one]
      | succ k =>
          change (Equiv.Perm.eulerianNumber 1 (k + 1) : ℝ) =
            (generalizedEulerian 1 0).coeff (k + 1)
          rw [Equiv.Perm.eulerianNumber_succ_succ]
          have hzero : Equiv.Perm.eulerianNumber 0 (k + 1) = 0 := by
            simp [Equiv.Perm.eulerianNumber, Equiv.Perm.descentCount,
              Equiv.Perm.descentSet, List.descentSet]
          rw [hzero]
          simp [generalizedEulerian, Polynomial.coeff_one]
  | succ n ih =>
      cases k with
      | zero =>
          rw [Equiv.Perm.eulerianNumber_succ_zero]
          simp [coeff_zero_generalizedEulerian]
      | succ k =>
          rw [Equiv.Perm.eulerianNumber_succ_succ, coeff_generalizedEulerian_succ]
          simp only [Nat.cast_add, Nat.cast_mul]
          rw [ih (k + 1), ih k]
          by_cases hk : k ≤ n
          · rw [Nat.cast_sub (by lia : k ≤ n + 1)]
            push_cast
            ring
          · have hkn : n < k := Nat.lt_of_not_ge hk
            have hzero : (generalizedEulerian 1 n).coeff k = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by
                rw [generalizedEulerian_natDegree]
                exact hkn)
            have hzero' : (generalizedEulerian 1 n).coeff (k + 1) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by
                rw [generalizedEulerian_natDegree]
                lia)
            simp [hzero, hzero']

/-- The descent generating polynomial of permutations is the ordinary Eulerian polynomial.

The coefficient of `X ^ k` counts permutations with `k` descents, and the index `n`
corresponds to permutations of `Fin (n + 1)`. -/
theorem genPoly_univ_descentCount (n : ℕ) :
    (Finset.genPoly (Finset.univ : Finset (Equiv.Perm (Fin (n + 1))))
      Equiv.Perm.descentCount : ℝ[X]) = generalizedEulerian 1 n := by
  apply Polynomial.ext
  intro k
  rw [Finset.coeff_genPoly]
  exact coeff_eulerianNumber n k

/-- The descent generating polynomial of permutations has only real roots. -/
theorem isRealRooted_genPoly_univ_descentCount (n : ℕ) :
    (Finset.genPoly (Finset.univ : Finset (Equiv.Perm (Fin (n + 1))))
      Equiv.Perm.descentCount : ℝ[X]) ≠ 0 ∧
      Polynomial.Splits
        (Finset.genPoly (Finset.univ : Finset (Equiv.Perm (Fin (n + 1))))
          Equiv.Perm.descentCount : ℝ[X]) := by
  rw [genPoly_univ_descentCount]
  exact ⟨(generalizedEulerian_monic 1 n).ne_zero, generalizedEulerian_splits (by norm_num) n⟩

end RealRooted
