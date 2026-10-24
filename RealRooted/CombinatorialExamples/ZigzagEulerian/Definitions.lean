/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-!
# Zig-zag Eulerian polynomials from alternating permutations

This uses the exact convention of the zig-zag Eulerian proof: positions are
zero-based, even positions ascend and odd positions descend, while a swap at
value `i` means that the position of `i + 1` exceeds the position of `i` by
at least two. The polynomial is the sum over these actual permutations.
-/

@[expose] public section

open Polynomial Finset

noncomputable section

namespace RealRooted.ZigzagEulerian

/-- An up-down permutation has `π 0 < π 1 > π 2 < ⋯` in zero-based positions. -/
def IsUpDown {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val →
    if Even i.val then π i < π j else π j < π i

/-- Values whose inverse positions are separated by at least one other entry.
The index `i` denotes the value `i + 1` in the manuscript's one-based notation. -/
def swapSet {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => ∃ j : Fin n,
    i.val + 1 = j.val ∧ (π.symm i).val + 1 < (π.symm j).val

/-- The swap statistic of the zig-zag Eulerian proof. -/
def swapCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (swapSet π).card

/-- The actual zig-zag Eulerian polynomial `H_n`, summed over up-down
permutations of `Fin n`. In particular the empty row equals one. -/
def zigzagEulerianPolynomial (n : ℕ) : ℝ[X] := by
  classical
  exact ∑ π ∈ (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown,
    X ^ swapCount π

/-- Swap the disjoint pairs of positions `(1,2),(3,4),…`, leaving position
zero and any final unmatched position fixed. -/
private def zigzagValue (n k : ℕ) : ℕ :=
  if k = 0 then 0 else if k % 2 = 0 then k - 1 else if k + 1 < n then k + 1 else k

private theorem zigzagValue_lt {n k : ℕ} (hk : k < n) : zigzagValue n k < n := by
  unfold zigzagValue
  split_ifs <;> lia

private theorem zigzagValue_involutive {n k : ℕ} (hk : k < n) :
    zigzagValue n (zigzagValue n k) = k := by
  by_cases hzero : k = 0
  · simp [zigzagValue, hzero]
  by_cases heven : k % 2 = 0
  · have hodd : (k - 1) % 2 ≠ 0 := by lia
    have hnext : k - 1 + 1 < n := by lia
    have hprev0 : k - 1 ≠ 0 := by lia
    simp [zigzagValue, hzero, heven, hprev0, hodd, hnext]
    lia
  · by_cases hnext : k + 1 < n
    · have hnewEven : (k + 1) % 2 = 0 := by lia
      simp [zigzagValue, hzero, heven, hnext, hnewEven]
    · simp [zigzagValue, hzero, heven, hnext]

/-- A concrete up-down permutation, used to witness nonemptiness at every size. -/
@[no_expose] def zigzagWitness (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨zigzagValue n i.val, zigzagValue_lt i.isLt⟩
  invFun i := ⟨zigzagValue n i.val, zigzagValue_lt i.isLt⟩
  left_inv i := Fin.ext (zigzagValue_involutive i.isLt)
  right_inv i := Fin.ext (zigzagValue_involutive i.isLt)

/-- The explicit witness alternates in the manuscript's orientation. -/
theorem zigzagWitness_isUpDown (n : ℕ) : IsUpDown (zigzagWitness n) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  change if Even i.val then zigzagValue n i.val < zigzagValue n j.val
    else zigzagValue n j.val < zigzagValue n i.val
  by_cases heven : i.val % 2 = 0
  · have hpar : Even i.val := Nat.even_iff.mpr heven
    simp only [hpar, ↓reduceIte]
    by_cases hzero : i.val = 0
    · have hjone : j.val = 1 := by lia
      simp [zigzagValue, hzero, hjone]
      lia
    · have hodd : j.val % 2 ≠ 0 := by lia
      by_cases hnext : j.val + 1 < n <;>
        simp [zigzagValue, hzero, heven, hodd, hnext] <;> lia
  · have hpar : ¬Even i.val := by
      intro h
      exact heven (Nat.even_iff.mp h)
    simp only [hpar, ↓reduceIte]
    have hzero : i.val ≠ 0 := by lia
    have hnext : i.val + 1 < n := by lia
    have hjEven : j.val % 2 = 0 := by lia
    have hjPos : j.val ≠ 0 := by lia
    simp [zigzagValue, hzero, heven, hnext, hjEven, hjPos]
    lia

/-- Every swap lies below the largest value, which has no successor. -/
theorem swapSet_subset_erase_last {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    swapSet π ⊆ (univ : Finset (Fin n)).erase ⟨n - 1, by lia⟩ := by
  intro i hi
  have hlast : (⟨n - 1, by lia⟩ : Fin n) ∉ swapSet π := by
    intro h
    obtain ⟨j, hj, _⟩ := (mem_filter.mp h).2
    have hjlt := j.isLt
    lia
  exact mem_erase.mpr ⟨by intro h; exact hlast (h ▸ hi), mem_univ i⟩

/-- No permutation can have all `n - 1` consecutive inverse-position gaps
strictly greater than one. This bound does not require alternation. -/
theorem swapCount_le_sub_two {n : ℕ} (hn : 2 ≤ n)
    (π : Equiv.Perm (Fin n)) : swapCount π ≤ n - 2 := by
  let s := swapSet π
  have hsub : s ⊆ (univ : Finset (Fin n)).erase ⟨n - 1, by lia⟩ :=
    swapSet_subset_erase_last (by lia) π
  by_contra hbound
  change ¬s.card ≤ n - 2 at hbound
  have hbig : n - 1 ≤ s.card := by lia
  have heq : s = (univ : Finset (Fin n)).erase ⟨n - 1, by lia⟩ := by
    apply eq_of_subset_of_card_le hsub
    simpa [card_erase_of_mem] using hbig
  have hpos : ∀ j : ℕ, ∀ hj : j < n,
      2 * j ≤ (π.symm (⟨j, hj⟩ : Fin n)).val := by
    intro j
    induction j with
    | zero =>
      intro hj
      simp
    | succ j ih =>
      intro hj
      have hj0 : j < n := by lia
      have himem : (⟨j, hj0⟩ : Fin n) ∈ s := by
        rw [heq]
        refine mem_erase.mpr ⟨?_, mem_univ _⟩
        intro he
        have hv := congrArg Fin.val he
        lia
      obtain ⟨k, hk, hgap⟩ := (mem_filter.mp himem).2
      have hkeq : k = (⟨j + 1, hj⟩ : Fin n) := Fin.ext hk.symm
      rw [hkeq] at hgap
      have hprev := ih hj0
      lia
  have hfinal := hpos (n - 1) (by lia)
  have hlt := (π.symm (⟨n - 1, by lia⟩ : Fin n)).isLt
  lia

/-- Every coefficient of the actual up-down permutation sum is nonnegative. -/
theorem zigzagEulerianPolynomial_coeff_nonneg (n k : ℕ) :
    0 ≤ (zigzagEulerianPolynomial n).coeff k := by
  rw [zigzagEulerianPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro π _
  simp only [Polynomial.coeff_X_pow]
  split_ifs <;> positivity

/-- Exact coefficient count in the actual up-down permutation class. -/
def zigzagCoefficientCount (n k : ℕ) : ℕ := by
  letI : DecidablePred (@IsUpDown n) := fun π => by
    unfold IsUpDown
    infer_instance
  exact ((univ : Finset (Equiv.Perm (Fin n))).filter
    fun π => IsUpDown π ∧ swapCount π = k).card

/-- Each coefficient counts alternating permutations with the prescribed swap statistic. -/
theorem zigzagEulerianPolynomial_coeff (n k : ℕ) :
    (zigzagEulerianPolynomial n).coeff k = (zigzagCoefficientCount n k : ℝ) := by
  classical
  rw [zigzagEulerianPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  simp [zigzagCoefficientCount, Finset.filter_filter, eq_comm]

/-- The coefficient support is contained in degrees `0,...,n-2` for `n ≥ 2`. -/
theorem zigzagEulerianPolynomial_coeff_eq_zero_of_gt {n k : ℕ}
    (hn : 2 ≤ n) (hk : n - 2 < k) :
    (zigzagEulerianPolynomial n).coeff k = 0 := by
  classical
  rw [zigzagEulerianPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro π _
  rw [Polynomial.coeff_X_pow]
  have hne : k ≠ swapCount π := by
    have hb := swapCount_le_sub_two hn π
    lia
  simp [hne]

/-- The actual swap statistic gives the elementary support bound. -/
theorem zigzagEulerianPolynomial_natDegree_le_sub_two {n : ℕ} (hn : 2 ≤ n) :
    (zigzagEulerianPolynomial n).natDegree ≤ n - 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact zigzagEulerianPolynomial_coeff_eq_zero_of_gt hn hk

/-- The alternating class contains the explicit pair-swapping witness, so
its actual generating polynomial is nonzero at every size. -/
theorem zigzagEulerianPolynomial_ne_zero (n : ℕ) :
    zigzagEulerianPolynomial n ≠ 0 := by
  classical
  let s : Finset (Equiv.Perm (Fin n)) := univ.filter IsUpDown
  have hw : zigzagWitness n ∈ s :=
    mem_filter.mpr ⟨mem_univ _, zigzagWitness_isUpDown n⟩
  have hc : 0 < s.card := card_pos.mpr ⟨zigzagWitness n, hw⟩
  have heval : (zigzagEulerianPolynomial n).eval 1 = (s.card : ℝ) := by
    simp [zigzagEulerianPolynomial, s, Polynomial.eval_finsetSum]
  intro hzero
  rw [hzero] at heval
  have hcReal : (0 : ℝ) < s.card := by exact_mod_cast hc
  simp at heval
  linarith

/-- The coefficient counts for the initial four rows, checked directly from
the actual finite permutation predicates. -/
theorem zigzagCoefficientCount_small :
    zigzagCoefficientCount 1 0 = 1 ∧
      zigzagCoefficientCount 2 0 = 1 ∧
      zigzagCoefficientCount 3 0 = 1 ∧
      zigzagCoefficientCount 3 1 = 1 ∧
      zigzagCoefficientCount 4 0 = 1 ∧
      zigzagCoefficientCount 4 1 = 3 ∧
      zigzagCoefficientCount 4 2 = 1 := by
  decide

private theorem swapCount_one_eq_zero (π : Equiv.Perm (Fin 1)) : swapCount π = 0 := by
  unfold swapCount swapSet
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  rintro ⟨j, hij, _⟩
  have hj := j.isLt
  lia

/-- The first four rows of the actual alternating-permutation sum. -/
theorem zigzagEulerianPolynomial_one : zigzagEulerianPolynomial 1 = 1 := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k = 0
  · subst k
    rcases zigzagCoefficientCount_small with ⟨h, _, _, _, _, _, _⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    simp
  · rw [zigzagEulerianPolynomial, Polynomial.finsetSum_coeff]
    have hz : ∑ π ∈ (univ : Finset (Equiv.Perm (Fin 1))).filter IsUpDown,
        (X ^ swapCount π : ℝ[X]).coeff k = 0 := by
      apply Finset.sum_eq_zero
      intro π _
      rw [swapCount_one_eq_zero π, pow_zero, Polynomial.coeff_one]
      simp [hk]
    rw [hz]
    rw [Polynomial.coeff_one]
    simp [hk]

/-- The size-two zig-zag Eulerian polynomial is constant. -/
theorem zigzagEulerianPolynomial_two : zigzagEulerianPolynomial 2 = 1 := by
  apply Polynomial.ext
  intro k
  by_cases hk : k = 0
  · subst k
    rcases zigzagCoefficientCount_small with ⟨_, h, _, _, _, _, _⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    rw [Polynomial.coeff_one]
    simp
  · have hgt : 2 - 2 < k := by lia
    rw [zigzagEulerianPolynomial_coeff_eq_zero_of_gt (by norm_num) hgt]
    rw [Polynomial.coeff_one]
    simp [hk]

/-- The size-three zig-zag Eulerian polynomial is linear. -/
theorem zigzagEulerianPolynomial_three : zigzagEulerianPolynomial 3 = 1 + X := by
  apply Polynomial.ext
  intro k
  by_cases h0 : k = 0
  · subst k
    rcases zigzagCoefficientCount_small with ⟨_, _, h, _, _, _, _⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X]
  by_cases h1 : k = 1
  · subst k
    rcases zigzagCoefficientCount_small with ⟨_, _, _, h, _, _, _⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hgt : 3 - 2 < k := by lia
    rw [zigzagEulerianPolynomial_coeff_eq_zero_of_gt (by norm_num) hgt]
    have h1' : 1 ≠ k := Ne.symm h1
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      ite_eq_right h0, ite_eq_right h1']
    norm_num

/-- The size-four zig-zag Eulerian polynomial is quadratic. -/
theorem zigzagEulerianPolynomial_four : zigzagEulerianPolynomial 4 = 1 + 3 * X + X ^ 2 := by
  apply Polynomial.ext
  intro k
  by_cases h0 : k = 0
  · subst k
    rcases zigzagCoefficientCount_small with ⟨_, _, _, _, h, _, _⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow]
  by_cases h1 : k = 1
  · subst k
    rcases zigzagCoefficientCount_small with ⟨_, _, _, _, _, h, _⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow]
  by_cases h2 : k = 2
  · subst k
    rcases zigzagCoefficientCount_small with ⟨_, _, _, _, _, _, h⟩
    rw [zigzagEulerianPolynomial_coeff, h]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow]
  · have hgt : 4 - 2 < k := by lia
    rw [zigzagEulerianPolynomial_coeff_eq_zero_of_gt (by norm_num) hgt]
    have hmul : (3 * X : ℝ[X]).coeff k = 0 := by
      have hthree : (3 : ℝ[X]) = C (3 : ℝ) := (Polynomial.C_ofNat 3).symm
      rw [hthree, Polynomial.coeff_C_mul_X, ite_eq_right h1]
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_X_pow, ite_eq_right h0, ite_eq_right h2, hmul]
    norm_num

end RealRooted.ZigzagEulerian
