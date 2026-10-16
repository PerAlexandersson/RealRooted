import RealRooted.Applications.OEIS.HigherOrderDegreeModels
import RealRooted.SymmetricDecomposition.FPolynomial
import RealRooted.Transforms.BrandenE.EvenBinomial

/-!
# OEIS A262226

The degree-`n` f-transform of the primary type-D Eulerian row is the even
binomial sum of Brändén basis images.  This places it in a common-interleaver
cone and proves real-rootedness after inverting the f-transform.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.HigherOrderDegreeModels.A262226

/-- The even indices in the ambient binomial basis of degree `n`. -/
abbrev evenBinomialIndices := RealRooted.evenBinomialIndices

/-- The even binomial sum of Brändén basis images. -/
abbrev evenBinomialImage := RealRooted.brandenEvenBinomialImage

private theorem typeB_choose_le :
    ∀ n k : ℕ,
      (n.choose k : ℝ) ≤
        (RealRooted.generalizedEulerian 2 n).coeff k := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [show RealRooted.generalizedEulerian 2 0 = 1 by rfl]
      cases k with
      | zero => simp
      | succ k =>
          rw [Nat.choose_eq_zero_of_lt (by lia)]
          simp [coeff_one]
  | succ n ih =>
      intro k
      cases k with
      | zero => simp
      | succ k =>
          rw [RealRooted.coeff_generalizedEulerian_succ,
            Nat.choose_succ_succ]
          by_cases hkn : k ≤ n
          · have h0 := ih k
            have h1 := ih (k + 1)
            have hnn0 :
                0 ≤ (RealRooted.generalizedEulerian 2 n).coeff k :=
              (RealRooted.generalizedEulerian_invariants
                (c := 2) (by norm_num) n).2.1 k
            have hnn1 :
                0 ≤ (RealRooted.generalizedEulerian 2 n).coeff (k + 1) :=
              (RealRooted.generalizedEulerian_invariants
                (c := 2) (by norm_num) n).2.1 (k + 1)
            have hkcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
            push_cast
            nlinarith
          · have hk0 : n.choose k = 0 :=
              Nat.choose_eq_zero_of_lt (by lia)
            have hk1 : n.choose (k + 1) = 0 :=
              Nat.choose_eq_zero_of_lt (by lia)
            have hg0 :
                (RealRooted.generalizedEulerian 2 n).coeff k = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              rw [(RealRooted.generalizedEulerian_invariants
                (c := 2) (by norm_num) n).1]
              lia
            have hg1 :
                (RealRooted.generalizedEulerian 2 n).coeff (k + 1) = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              rw [(RealRooted.generalizedEulerian_invariants
                (c := 2) (by norm_num) n).1]
              lia
            simp_all

private theorem polynomial_nonneg (n : ℕ) :
    HasNonnegCoeffs (polynomial n) := by
  intro k
  rw [polynomial_eq_typeB_average, coeff_C_mul, coeff_add,
    Polynomial.coeff_one_sub_X_pow]
  have hdom := typeB_choose_le n k
  have hchoose : 0 ≤ (n.choose k : ℝ) := by positivity
  rcases Nat.even_or_odd k with heven | hodd
  · rw [heven.neg_one_pow]
    nlinarith
  · simp_all

/-- Every A262226 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  have himage := RealRooted.brandenEvenBinomialImage_ne_zero_and_splits n
  have hdeg : (polynomial n).natDegree ≤ n := by
    rw [polynomial_natDegree]
    lia
  have hfpoly : fPolynomial n (polynomial n) ≠ 0 ∧
      (fPolynomial n (polynomial n)).Splits := by
    rw [polynomial_eq_typeB_average,
      RealRooted.fPolynomial_typeD_average_eq_evenBinomialImage]
    exact himage
  exact (isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs
    hdeg hfpoly.1 hfpoly.2 (polynomial_nonneg n)).2

private theorem polynomial_step (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) (polynomial n) := rfl

/-- Every sequence with the A262226 initial rows and order-two update splits. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1)
    (hrec : ∀ n, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    hzero hone hrec polynomial_step
  rw [heq n]
  exact polynomial_splits n

end RealRooted.Applications.OEIS.HigherOrderDegreeModels.A262226
