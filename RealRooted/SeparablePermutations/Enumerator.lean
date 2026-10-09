import RealRooted.SeparablePermutations.Gamma
import RealRooted.HosterStump.Permutation

/-!
# The descent enumerator of the separable permutations

A permutation is *separable* if it avoids the patterns `2413` and `3142`.  We define the
descent enumerator `descentEnumerator n = ∑ x ^ des σ`, summed over the separable permutations
of `n + 1` letters, reusing `RealRooted.HosterStump.desSet` for descents; the shift `n + 1`
matches the indexing of that definition and keeps the empty permutation out of the picture.

The algebraic family `descentPolynomial` of `RealRooted/SeparablePermutations/Gamma.lean` is
defined through Zhang's representation of the gamma-polynomials (SSRN 7510941, Proposition
3.3).  That `descentEnumerator n = descentPolynomial (n + 1)` for all `n` is the combination of
Proposition 2.1 and Corollaries 2.4, 2.6 of Fu--Lin--Zeng with Zhang's Proposition 3.3; it is
**not** proved here.  We verify it by `decide` for permutations of at most four letters, and
state the consequences that follow from it as theorems with the identity as an explicit
hypothesis.
-/

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

/-- Pattern containment: `σ` contains `τ` if there are positions `f 0 < ⋯ < f (k - 1)` at
which the values of `σ` are order-isomorphic to `τ`. -/
def ContainsPattern {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) : Prop :=
  ∃ f : Fin k → Fin n, (∀ i j, i < j → f i < f j) ∧ ∀ i j, σ (f i) < σ (f j) ↔ τ i < τ j

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
  ¬ ContainsPattern σ pattern2413 ∧ ¬ ContainsPattern σ pattern3142

instance {n : ℕ} : DecidablePred (IsSeparable (n := n)) := fun σ => by
  unfold IsSeparable
  infer_instance

/-- The number of separable permutations of `n + 1` letters with exactly `k` descents. -/
def descentCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
    IsSeparable σ ∧ (HosterStump.desSet σ).card = k).card

/-- The descent enumerator `∑ x ^ des σ` of the separable permutations of `n + 1` letters
(descents are counted by `RealRooted.HosterStump.desSet`). -/
def descentEnumerator (n : ℕ) : ℝ[X] :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => IsSeparable σ),
    X ^ (HosterStump.desSet σ).card

/-- The coefficients of the descent enumerator are the descent counts. -/
theorem coeff_descentEnumerator (n k : ℕ) :
    (descentEnumerator n).coeff k = (descentCount n k : ℝ) := by
  classical
  rw [descentEnumerator, finsetSum_coeff, descentCount, Finset.card_filter, Nat.cast_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : IsSeparable σ
  · by_cases hk : (HosterStump.desSet σ).card = k
    · simp [hσ, hk, coeff_X_pow]
    · simp [hσ, hk, coeff_X_pow, Ne.symm hk]
  · simp [hσ]

/-- A permutation of `n + 1` letters has at most `n` descents. -/
theorem descentCount_eq_zero {n k : ℕ} (hk : n < k) : descentCount n k = 0 := by
  rw [descentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro σ - ⟨-, hσ⟩
  have := Finset.card_le_card (HosterStump.desSet_subset_range σ)
  rw [Finset.card_range] at this
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

/-! ### Conditional transfer

The following results take the combinatorial identity
`descentEnumerator n = descentPolynomial (n + 1)` (Fu--Lin--Zeng together with Zhang's
Proposition 3.3) as an explicit hypothesis.  The hypothesis is a documented identity between a
permutation statistic and the algebraically defined family, not a restatement of the
conclusion: the conclusions are derived from the proved properties of `descentPolynomial`. -/

/-- If the descent enumerator of the separable permutations is `descentPolynomial`, then for
every `k ≤ n` there is a separable permutation of `n + 1` letters with exactly `k` descents. -/
theorem descentCount_pos_of_eq_descentPolynomial
    (h : ∀ n, descentEnumerator n = descentPolynomial (n + 1)) {n k : ℕ} (hk : k ≤ n) :
    0 < descentCount n k := by
  have := coeff_descentPolynomial_pos (n := n + 1) (k := k) (by lia) (by lia)
  rw [← h, coeff_descentEnumerator] at this
  exact_mod_cast this

/-- If the descent enumerator of the separable permutations is `descentPolynomial`, then it
has degree `n` on `n + 1` letters. -/
theorem natDegree_descentEnumerator_of_eq_descentPolynomial
    (h : ∀ n, descentEnumerator n = descentPolynomial (n + 1)) (n : ℕ) :
    (descentEnumerator n).natDegree = n := by
  rw [h, natDegree_descentPolynomial (by lia)]
  rfl

end RealRooted.SeparablePermutations
