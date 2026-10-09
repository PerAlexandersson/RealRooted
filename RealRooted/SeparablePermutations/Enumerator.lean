import RealRooted.Mathlib.Combinatorics.Enumerative.Pattern
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import RealRooted.SeparablePermutations.Gamma

/-!
# The descent enumerator of the separable permutations

A permutation is *separable* if it avoids the patterns `2413` and `3142`.  We define the
descent enumerator `descentEnumerator n = ∑ x ^ des σ`, summed over the separable permutations
of `n + 1` letters, using the canonical descent set; the shift `n + 1`
matches the indexing of that definition and keeps the empty permutation out of the picture.

The algebraic family `descentPolynomial` of `RealRooted/SeparablePermutations/Gamma.lean` is
defined through Zhang's representation of the gamma-polynomials (SSRN 7510941, Proposition
3.3).  That `descentEnumerator n = descentPolynomial (n + 1)` for all `n` is the combination of
Proposition 2.1 and Corollaries 2.4, 2.6 of Fu--Lin--Zeng with Zhang's Proposition 3.3; it is
**not** proved here.  We verify it by `decide` for permutations of at most four letters, and
state the consequences that follow from it as theorems with the identity as an explicit
hypothesis.

Pattern containment and descents are the canonical `Equiv.Perm.ContainsPattern` and
`Equiv.Perm.descentSet` of the staging modules `RealRooted.Mathlib.Combinatorics.Enumerative`;
the local names are kept for compatibility.
-/

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

/-- Pattern containment for permutations, retained under the historical local name. -/
def ContainsPattern {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) : Prop :=
  Equiv.Perm.ContainsPattern σ τ

instance {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    Decidable (ContainsPattern σ τ) := by
  unfold ContainsPattern
  infer_instance

/-- The permutation `2413` of `Fin 4` (one-line notation, values `1, …, 4`). -/
def pattern2413 : Equiv.Perm (Fin 4) := ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

/-- The permutation `3142` of `Fin 4` (one-line notation, values `1, …, 4`). -/
def pattern3142 : Equiv.Perm (Fin 4) := ⟨![2, 0, 3, 1], ![1, 3, 0, 2], by decide, by decide⟩

/-- A permutation is separable if it avoids `2413` and `3142`. -/
def IsSeparable {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  σ.Avoids pattern2413 ∧ σ.Avoids pattern3142

instance {n : ℕ} : DecidablePred (IsSeparable (n := n)) := fun σ => by
  unfold IsSeparable
  infer_instance

/-- The number of separable permutations of `n + 1` letters with exactly `k` descents. -/
def descentCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
    IsSeparable σ ∧ σ.descentCount = k).card

/-- The descent enumerator of separable permutations of `n + 1` letters. -/
def descentEnumerator (n : ℕ) : ℝ[X] :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => IsSeparable σ),
    X ^ σ.descentCount

/-- The coefficients of the descent enumerator are the descent counts. -/
theorem coeff_descentEnumerator (n k : ℕ) :
    (descentEnumerator n).coeff k = (descentCount n k : ℝ) := by
  classical
  rw [descentEnumerator, finsetSum_coeff, descentCount, Finset.card_filter, Nat.cast_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : IsSeparable σ
  · by_cases hk : σ.descentCount = k
    · simp only [hσ, coeff_X_pow, hk.symm, ite_true, true_and, Nat.cast_one]
    · simp only [hσ, coeff_X_pow, Ne.symm hk, hk, ite_true, ite_false, true_and]
      norm_num
  · simp [hσ]

/-- A permutation of `n + 1` letters has at most `n` descents. -/
theorem descentCount_eq_zero {n k : ℕ} (hk : n < k) : descentCount n k = 0 := by
  rw [descentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro σ - ⟨-, hσ⟩
  have hsubset : σ.descentSet ⊆ Finset.range n := by
    rw [Equiv.Perm.descentSet_eq_list]
    simpa only [List.length_ofFn, Nat.add_sub_cancel]
      using List.descentSet_subset_range (List.ofFn σ)
  have := Finset.card_le_card hsubset
  rw [Finset.card_range] at this
  change σ.descentCount ≤ n at this
  rw [hσ] at this
  lia

/-- The descent enumerator as a sum over the descent counts. -/
theorem descentEnumerator_eq_sum (n : ℕ) :
    descentEnumerator n = ∑ k ∈ Finset.range (n + 1), C (descentCount n k : ℝ) * X ^ k := by
  ext m
  rw [coeff_descentEnumerator, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hm : m < n + 1
  · rw [ite_eq_left (Finset.mem_range.mpr hm)]
  · rw [ite_eq_right (fun h => hm (Finset.mem_range.mp h)), descentCount_eq_zero (by lia)]
    simp

/-! ### Finite checks against `descentPolynomial` -/

theorem descentEnumerator_zero : descentEnumerator 0 = descentPolynomial 1 := by
  have h0 : descentCount 0 0 = 1 := by decide
  rw [descentEnumerator_eq_sum, descentPolynomial_one]
  simp [h0]

theorem descentEnumerator_one : descentEnumerator 1 = descentPolynomial 2 := by
  have h0 : descentCount 1 0 = 1 := by decide
  have h1 : descentCount 1 1 = 1 := by decide
  rw [descentEnumerator_eq_sum, descentPolynomial_two]
  simp [Finset.sum_range_succ, h0, h1]

theorem descentEnumerator_two : descentEnumerator 2 = descentPolynomial 3 := by
  have h0 : descentCount 2 0 = 1 := by decide
  have h1 : descentCount 2 1 = 4 := by decide
  have h2 : descentCount 2 2 = 1 := by decide
  rw [descentEnumerator_eq_sum, descentPolynomial_three]
  simp [Finset.sum_range_succ, h0, h1, h2]

theorem descentEnumerator_three : descentEnumerator 3 = descentPolynomial 4 := by
  have h0 : descentCount 3 0 = 1 := by decide +kernel
  have h1 : descentCount 3 1 = 10 := by decide +kernel
  have h2 : descentCount 3 2 = 10 := by decide +kernel
  have h3 : descentCount 3 3 = 1 := by decide +kernel
  rw [descentEnumerator_eq_sum, descentPolynomial_four]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, Nat.cast_one,
    Nat.cast_ofNat, map_one, map_ofNat C, pow_zero, pow_one]
  ring

/-! ### Conditional transfer -/

/-- Positive descent counts follow from the corresponding descent-polynomial identity. -/
theorem descentCount_pos_of_eq_descentPolynomial
    (h : ∀ n, descentEnumerator n = descentPolynomial (n + 1)) {n k : ℕ} (hk : k ≤ n) :
    0 < descentCount n k := by
  have := coeff_descentPolynomial_pos (n := n + 1) (k := k) (by lia) (by lia)
  rw [← h, coeff_descentEnumerator] at this
  exact_mod_cast this

/-- The descent enumerator has degree `n` under the corresponding descent-polynomial identity. -/
theorem natDegree_descentEnumerator_of_eq_descentPolynomial
    (h : ∀ n, descentEnumerator n = descentPolynomial (n + 1)) (n : ℕ) :
    (descentEnumerator n).natDegree = n := by
  rw [h, natDegree_descentPolynomial (by lia)]
  rfl

end RealRooted.SeparablePermutations
