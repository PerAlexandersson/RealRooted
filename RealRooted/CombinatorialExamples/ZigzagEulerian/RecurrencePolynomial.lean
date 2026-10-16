/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.Recurrence
public import RealRooted.CombinatorialExamples.ZigzagEulerian.Standardization
public import RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted

/-!
# Zig-zag Eulerian polynomials defined by recurrences

The word numbers are defined recursively in `Recurrence`. We recover the numerator
coefficients by triangular binomial inversion. Thus the polynomial definition does
not enumerate permutations. Standardization identifies it with the swap enumerator,
and transfers the simple negative root theorem to the recurrence-defined family.
-/

@[expose] public noncomputable section

open Polynomial Finset

namespace RealRooted.ZigzagEulerian

/-- The binomial transform from numerator coefficients to word counts. -/
def binomialWordTransform (n k : ℕ) : ℝ[X] →+ ℝ where
  toFun p := p.sum fun d c => c * (Nat.choose (k + n - 1 - d) n : ℝ)
  map_zero' := by simp
  map_add' p q := by
    exact Polynomial.sum_add_index p q _ (by simp) (by intros; ring)

private theorem binomialWordTransform_monomial (n k d : ℕ) (c : ℝ) :
    binomialWordTransform n k (monomial d c) =
      c * (Nat.choose (k + n - 1 - d) n : ℝ) := by
  simp [binomialWordTransform]

/-- The word transform of the actual swap enumerator is the actual word count. -/
theorem binomialWordTransform_zigzagEulerianPolynomial (n k : ℕ) :
    binomialWordTransform n k (zigzagEulerianPolynomial n) =
      (weakUpDownWordCount n k : ℝ) := by
  classical
  rw [weakUpDownWordCount_eq_zigzagBinomialWordCount]
  unfold zigzagEulerianPolynomial zigzagBinomialWordCount
  rw [map_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro π _
  rw [← monomial_one_right_eq_X_pow, binomialWordTransform_monomial, one_mul]

private theorem binomialWordTransform_succ (n j : ℕ) (hn : 0 < n) (p : ℝ[X]) :
    binomialWordTransform n (j + 1) p = p.coeff j +
      ∑ i ∈ range j, p.coeff i * (Nat.choose (n + j - i) n : ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq]
    simp only [coeff_add, add_mul, Finset.sum_add_distrib]
    ring
  | monomial d c =>
    rw [binomialWordTransform_monomial]
    have htop : j + 1 + n - 1 = n + j := by lia
    rw [htop]
    simp only [coeff_monomial, ite_mul, zero_mul]
    by_cases hd : d < j
    · simp [hd, ne_of_lt hd]
    · by_cases he : d = j
      · subst d
        simp
      · have hzero : Nat.choose (n + j - d) n = 0 :=
          Nat.choose_eq_zero_of_lt (by lia)
        simp [hd, he, hzero]

/-- Numerator coefficients recovered from recursively defined word counts.
For a positive row, the binomial transform is triangular with diagonal one. -/
def recursiveCoefficient (n : ℕ) : ℕ → ℝ
  | j => (recursiveWordCount n (j + 1) : ℝ) -
      ∑ i : Fin j, recursiveCoefficient n i.val * (Nat.choose (n + j - i.val) n : ℝ)
termination_by j => j
decreasing_by exact i.isLt

/-- Triangular inversion gives the actual numerator coefficients for every positive row. -/
theorem recursiveCoefficient_eq_coeff (n j : ℕ) (hn : 0 < n) :
    recursiveCoefficient n j = (zigzagEulerianPolynomial n).coeff j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [recursiveCoefficient, recursiveWordCount_eq_weakUpDownWordCount]
    have hsum :
        (∑ i : Fin j, recursiveCoefficient n i.val * (Nat.choose (n + j - i.val) n : ℝ)) =
        ∑ i ∈ range j,
          (zigzagEulerianPolynomial n).coeff i * (Nat.choose (n + j - i) n : ℝ) := by
      calc
        _ = ∑ i : Fin j,
            (zigzagEulerianPolynomial n).coeff i.val *
              (Nat.choose (n + j - i.val) n : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ih i.val i.isLt]
        _ = _ := Fin.sum_univ_eq_sum_range
            (fun i => (zigzagEulerianPolynomial n).coeff i *
              (Nat.choose (n + j - i) n : ℝ)) j
    rw [hsum, ← binomialWordTransform_zigzagEulerianPolynomial,
      binomialWordTransform_succ n j hn]
    ring

/-- The zig-zag Eulerian family defined by the word recurrence and triangular
binomial inversion. The zero row uses the empty-permutation convention. -/
def polynomial (n : ℕ) : ℝ[X] :=
  if n = 0 then 1 else
    ∑ j ∈ range (n + 1), monomial j (recursiveCoefficient n j)

/-- The recurrence-defined polynomial equals the swap enumerator in every positive row. -/
theorem polynomial_eq_zigzagEulerianPolynomial (n : ℕ) (hn : 0 < n) :
    polynomial n = zigzagEulerianPolynomial n := by
  classical
  rw [polynomial, ite_eq_right (by lia)]
  simp_rw [recursiveCoefficient_eq_coeff n _ hn]
  have hdegree : (zigzagEulerianPolynomial n).natDegree ≤ n := by
    by_cases hsmall : n = 1
    · subst n
      simp [zigzagEulerianPolynomial_one]
    · exact (zigzagEulerianPolynomial_natDegree_le_sub_two (by lia)).trans (by lia)
  have hs : (zigzagEulerianPolynomial n).support ⊆ range (n + 1) := by
    intro i hi
    have := le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    simp only [Finset.mem_range]
    lia
  exact (Polynomial.sum_eq_of_subset (fun j c => monomial j c) (by simp) hs).symm.trans
    (Polynomial.sum_monomial_eq _)

/-- The recurrence-defined positive rows have degree `n - 2` and simple negative roots. -/
theorem polynomial_roots (n : ℕ) (hn : 1 ≤ n) :
    (polynomial n).natDegree = n - 2 ∧
      (polynomial n).Splits ∧
      (polynomial n).roots.Nodup ∧
      ∀ r ∈ (polynomial n).roots, r < 0 := by
  rw [polynomial_eq_zigzagEulerianPolynomial n (by lia)]
  exact zigzagEulerianPolynomial_roots n hn

end RealRooted.ZigzagEulerian
