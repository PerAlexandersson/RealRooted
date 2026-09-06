import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative

/-!
# Peak-value polynomials of permutations

This file defines the multivariate enumerator whose variables record the
values, rather than the positions, of the interior peaks of a permutation.
Values are zero-based: the value called `j` in the combinatorics literature is
represented by the element of `Fin n` with value `j - 1`.
-/

open scoped BigOperators

namespace RealRooted

noncomputable section

/-- A position is an interior peak when it has two adjacent positions and its
value is larger than both adjacent values. -/
def IsPeakPosition {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : Prop :=
  ∃ i k : Fin n,
    i.val + 1 = j.val ∧ j.val + 1 = k.val ∧
      π i < π j ∧ π k < π j

/-- The set of interior peak positions of a permutation. -/
def peakPositions {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsPeakPosition π)

@[simp] theorem mem_peakPositions_iff {n : ℕ} {π : Equiv.Perm (Fin n)}
    {j : Fin n} :
    j ∈ peakPositions π ↔ IsPeakPosition π j := by
  simp [peakPositions]

/-- The set of values occurring at interior peaks of a permutation. -/
def peakValues {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (peakPositions π).image π

theorem mem_peakValues_iff_exists {n : ℕ} {π : Equiv.Perm (Fin n)}
    {v : Fin n} :
    v ∈ peakValues π ↔ ∃ j, IsPeakPosition π j ∧ π j = v := by
  simp [peakValues]

@[simp] theorem mem_peakValues_iff {n : ℕ} {π : Equiv.Perm (Fin n)}
    {v : Fin n} :
    v ∈ peakValues π ↔ IsPeakPosition π (π.symm v) := by
  classical
  constructor
  · rw [peakValues, Finset.mem_image]
    rintro ⟨j, hj, rfl⟩
    simpa using mem_peakPositions_iff.mp hj
  · intro hv
    rw [peakValues, Finset.mem_image]
    exact ⟨π.symm v, mem_peakPositions_iff.mpr hv, π.apply_symm_apply v⟩

/-- Values zero and one cannot occur at an interior peak. -/
theorem two_le_value_of_mem_peakValues
    {n : ℕ} {π : Equiv.Perm (Fin n)} {v : Fin n}
    (hv : v ∈ peakValues π) :
    2 ≤ v.val := by
  rw [mem_peakValues_iff] at hv
  rcases hv with ⟨i, k, hij, hjk, hi, hk⟩
  have hπi : π i < v := by
    simpa using hi
  have hπk : π k < v := by
    simpa using hk
  have hik : i ≠ k := by
    intro h
    subst k
    lia
  have hπik : π i ≠ π k := π.injective.ne hik
  lia

/-- The squarefree monomial recording the peak values of one permutation. -/
def peakValueMonomial {n : ℕ} (π : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∏ v ∈ peakValues π, MvPolynomial.X v

/-- The multivariate peak-value polynomial `K̂ₙ`. -/
def peakValuePolynomial (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ π : Equiv.Perm (Fin n), peakValueMonomial π

/-- Translate every variable of a real multivariate polynomial by one. -/
def translateVariablesByOne {σ : Type*} (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  MvPolynomial.aeval (fun i => 1 + MvPolynomial.X i) P

/-- The translated peak-value polynomial, presented directly as a positive
sum of products. -/
def peakValueTranslated (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ π : Equiv.Perm (Fin n),
    ∏ v ∈ peakValues π, (1 + MvPolynomial.X v)

theorem peakValueTranslated_eq_translateVariablesByOne (n : ℕ) :
    peakValueTranslated n = translateVariablesByOne (peakValuePolynomial n) := by
  classical
  simp [peakValueTranslated, translateVariablesByOne, peakValuePolynomial,
    peakValueMonomial]

/-- The translated peak-value polynomial has nonnegative coefficients. -/
theorem peakValueTranslated_hasNonnegCoeffs (n : ℕ) :
    MvPolynomial.HasNonnegCoeffs (peakValueTranslated n) := by
  classical
  unfold peakValueTranslated
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro π _
  apply MvPolynomial.HasNonnegCoeffs.prod
  intro v _
  exact MvPolynomial.HasNonnegCoeffs.add
    MvPolynomial.HasNonnegCoeffs.one
    (MvPolynomial.HasNonnegCoeffs.X v)

theorem coeff_peakValueTranslated_nonneg (n : ℕ) (m : Fin n →₀ ℕ) :
    0 ≤ MvPolynomial.coeff m (peakValueTranslated n) :=
  peakValueTranslated_hasNonnegCoeffs n m

/-- At the origin the translated peak-value polynomial counts all
permutations. -/
theorem eval_zero_peakValueTranslated (n : ℕ) :
    MvPolynomial.eval (fun _ => 0) (peakValueTranslated n) = n.factorial := by
  classical
  simp [peakValueTranslated, Fintype.card_perm]

end

end RealRooted
