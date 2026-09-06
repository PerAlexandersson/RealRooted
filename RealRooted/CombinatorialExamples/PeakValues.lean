import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
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

lemma peakPosition_ne_zero {m : ℕ}
    {π : Equiv.Perm (Fin (m + 1))} {j : Fin (m + 1)}
    (hj : IsPeakPosition π j) :
    j ≠ 0 := by
  rintro rfl
  rcases hj with ⟨i, k, hij, hjk, hi, hk⟩
  simp only [Fin.val_zero] at hij
  lia

lemma peakPosition_ne_last {m : ℕ}
    {π : Equiv.Perm (Fin (m + 1))} {j : Fin (m + 1)}
    (hj : IsPeakPosition π j) :
    j ≠ Fin.last m := by
  intro h
  rcases hj with ⟨i, k, hij, hjk, hi, hk⟩
  have hjval : j.val = m := by
    simpa using congrArg Fin.val h
  have hklt : k.val < m + 1 := k.isLt
  lia

lemma peakPositions_not_adjacent {n : ℕ}
    {π : Equiv.Perm (Fin n)} {j k : Fin n}
    (hj : IsPeakPosition π j) (hk : IsPeakPosition π k)
    (hjk : j.val + 1 = k.val) :
    False := by
  rcases hj with ⟨jl, jr, hjl, hjr, hleft, hright⟩
  rcases hk with ⟨kl, kr, hkl, hkr, hleft', hright'⟩
  have hjr_eq : jr = k := Fin.ext (by lia)
  have hkl_eq : kl = j := Fin.ext (by lia)
  subst jr
  subst kl
  exact (lt_asymm hright hleft')

/-- The two slots immediately before and after each peak position, embedded
into all slots except the final one. -/
def peakPairSlot {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) :
    {j // j ∈ peakPositions π} × Bool →
      {x : Fin (m + 1) // x ≠ Fin.last m}
  | (⟨j, hj⟩, false) =>
      ⟨(j.pred (peakPosition_ne_zero (mem_peakPositions_iff.mp hj))).castSucc, by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_pred, Fin.val_last] at hval
        have hjlt := j.isLt
        have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr
          (peakPosition_ne_zero (mem_peakPositions_iff.mp hj))
        lia⟩
  | (⟨j, hj⟩, true) =>
      ⟨j, peakPosition_ne_last (mem_peakPositions_iff.mp hj)⟩

lemma peakPairSlot_injective {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) :
    Function.Injective (peakPairSlot π) := by
  rintro ⟨⟨j, hj⟩, bj⟩ ⟨⟨k, hk⟩, bk⟩ h
  cases bj <;> cases bk
  · have hval := congrArg (fun x => x.1.val) h
    simp only [peakPairSlot, Fin.val_castSucc, Fin.val_pred] at hval
    have hjpos : 0 < j.val := by
      exact Fin.pos_iff_ne_zero.mpr
        (peakPosition_ne_zero (mem_peakPositions_iff.mp hj))
    have hkpos : 0 < k.val := by
      exact Fin.pos_iff_ne_zero.mpr
        (peakPosition_ne_zero (mem_peakPositions_iff.mp hk))
    have hjk : j = k := Fin.ext (by lia)
    subst k
    rfl
  · have hval := congrArg (fun x => x.1.val) h
    simp only [peakPairSlot, Fin.val_castSucc, Fin.val_pred] at hval
    have hjpos : 0 < j.val := by
      exact Fin.pos_iff_ne_zero.mpr
        (peakPosition_ne_zero (mem_peakPositions_iff.mp hj))
    have hkj : k.val + 1 = j.val := by lia
    exact (peakPositions_not_adjacent
      (mem_peakPositions_iff.mp hk) (mem_peakPositions_iff.mp hj) hkj).elim
  · have hval := congrArg (fun x => x.1.val) h
    simp only [peakPairSlot, Fin.val_castSucc, Fin.val_pred] at hval
    have hkpos : 0 < k.val := by
      exact Fin.pos_iff_ne_zero.mpr
        (peakPosition_ne_zero (mem_peakPositions_iff.mp hk))
    have hjk : j.val + 1 = k.val := by lia
    exact (peakPositions_not_adjacent
      (mem_peakPositions_iff.mp hj) (mem_peakPositions_iff.mp hk) hjk).elim
  · have hjk : j = k := by
      apply Subtype.ext_iff.mp h
    subst k
    rfl

theorem card_peakPositions_le {n : ℕ} (π : Equiv.Perm (Fin n)) :
    2 * (peakPositions π).card ≤ n - 1 := by
  cases n with
  | zero =>
      simp [peakPositions]
  | succ m =>
      have hcard := Fintype.card_le_of_injective (peakPairSlot π)
        (peakPairSlot_injective π)
      simpa [Fintype.card_prod, Fintype.card_coe,
        Fintype.card_subtype_compl, Nat.mul_comm] using hcard

/-- A permutation of `Fin n` has at most `⌊(n - 1) / 2⌋` interior peak
values. -/
theorem card_peakValues_le {n : ℕ} (π : Equiv.Perm (Fin n)) :
    2 * (peakValues π).card ≤ n - 1 := by
  have hcard : (peakValues π).card = (peakPositions π).card := by
    rw [peakValues, Finset.card_image_of_injective]
    exact π.injective
  rw [hcard]
  exact card_peakPositions_le π

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

/-- The translated enumerator has degree at most the maximum possible number
of interior peaks. -/
theorem totalDegree_peakValueTranslated_le (n : ℕ) :
    (peakValueTranslated n).totalDegree ≤ (n - 1) / 2 := by
  classical
  unfold peakValueTranslated
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π _
  calc
    (∏ v ∈ peakValues π,
        (1 + MvPolynomial.X v : MvPolynomial (Fin n) ℝ)).totalDegree ≤
        ∑ v ∈ peakValues π,
          (1 + MvPolynomial.X v : MvPolynomial (Fin n) ℝ).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _v ∈ peakValues π, 1 := by
      apply Finset.sum_le_sum
      intro v _
      simpa using MvPolynomial.totalDegree_add
        (1 : MvPolynomial (Fin n) ℝ) (MvPolynomial.X v)
    _ = (peakValues π).card := by simp
    _ ≤ (n - 1) / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      simpa [Nat.mul_comm] using card_peakValues_le π

/-- At the origin the translated peak-value polynomial counts all
permutations. -/
theorem eval_zero_peakValueTranslated (n : ℕ) :
    MvPolynomial.eval (fun _ => 0) (peakValueTranslated n) = n.factorial := by
  classical
  simp [peakValueTranslated, Fintype.card_perm]

end

end RealRooted
