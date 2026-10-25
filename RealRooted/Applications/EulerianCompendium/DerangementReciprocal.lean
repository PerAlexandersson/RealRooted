module

public import RealRooted.Applications.EulerianCompendium.DeletionRoots
public import RealRooted.Applications.EulerianCompendium.Derangements
public import RealRooted.Applications.EulerianCompendium.DerangementRecurrence
public import RealRooted.DegreeDropReversal

/-!
# Reciprocal derangement polynomials

The reflection calculation below is the operator identity in paper
`eq:reciprocalPolynomial`. It uses Mathlib's ambient-degree reflection,
so it also covers polynomials whose degree is smaller than the ambient bound.
-/

@[expose] public section

open Polynomial RealRooted

noncomputable section

namespace RealRooted.EulerianCompendium

/-- Aristotle's adjacent-position descent statistic agrees with the existing
`Equiv.Perm.descentCount` convention on `Fin n`. -/
theorem derangementDescent_des_eq_descentCount {n : ℕ}
    (π : Equiv.Perm (Fin n)) : DerangementDescent.des π = π.descentCount := by
  classical
  have hset : (DerangementDescent.descentSet π).map Fin.valEmbedding =
      π.descentSet := by
    ext j
    rw [Finset.mem_map, Equiv.Perm.descentSet_eq_list,
      List.mem_descentSet_ofFn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [DerangementDescent.descentSet, Finset.mem_filter,
        Finset.mem_univ, true_and] at hi
      rcases hi with ⟨h, hd⟩
      exact ⟨h, by simpa using hd⟩
    · rintro ⟨h, hd⟩
      refine ⟨⟨j, by lia⟩, ?_, rfl⟩
      simp only [DerangementDescent.descentSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨h, by simpa using hd⟩
  have hcard := congrArg Finset.card hset
  simpa [DerangementDescent.des, DerangementDescent.descentSet,
    Equiv.Perm.descentCount, Finset.card_map] using hcard

/-- The Aristotle word-counting recurrence concerns precisely the
permutation sum already fixed in this paper's challenge. -/
theorem derangementDescent_D_eq (n : ℕ) :
    DerangementDescent.D n = derangementDescentPolynomial n := by
  classical
  simp only [DerangementDescent.D, derangementDescentPolynomial,
    derangementDescent_des_eq_descentCount]

/-- Fu--Lin--Zeng's recurrence for the fixed descent enumerator, in the
Euler operator notation used by paper `eq:fuLinZengRecurrence`. -/
theorem derangementDescentPolynomial_recurrence (n : ℕ) (hn : 2 ≤ n) :
    derangementDescentPolynomial n =
      eulerInsertionStep 1 (n - 2) (derangementDescentPolynomial (n - 1)) +
        C ((-1 : ℝ) ^ n) * X ^ (n - 1) := by
  have hcast : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    have hnat : n - 2 + 2 = n := by lia
    have hreal := congrArg (fun k : ℕ => (k : ℝ)) hnat
    push_cast at hreal
    linarith
  have hcoef : (n : ℝ[X]) - 1 = C (((n - 2 : ℕ) : ℝ) + 1) := by
    rw [hcast, map_sub]
    simp only [map_natCast, map_one]
  rw [← derangementDescent_D_eq n,
    ← derangementDescent_D_eq (n - 1), DerangementDescent.D_recurrence n hn,
    eulerInsertionStep_eq, hcoef]
  have hnegpow : (-1 : ℝ[X]) ^ n = C ((-1 : ℝ) ^ n) := by
    simp
  rw [hnegpow, hcast]
  simp only [map_one]
  ring

private theorem derangementDescentPolynomial_one :
    derangementDescentPolynomial 1 = 0 := by
  classical
  rw [← derangementDescent_D_eq]
  unfold DerangementDescent.D
  apply Finset.sum_eq_zero
  intro π _
  have hfix : π 0 = (0 : Fin 1) := Subsingleton.elim _ _
  simp [hfix]

private theorem derangementDescentPolynomial_two :
    derangementDescentPolynomial 2 = X := by
  have h := derangementDescentPolynomial_recurrence 2 (by lia)
  simpa [derangementDescentPolynomial_one] using h

/-- Euler insertion commutes with coefficient reversal in the paper's
degree box. In manuscript notation, this is
`x^(m+1) (T_(m+2) f)(1/x) = T_(m+2) (x^m f(1/x))`. -/
theorem reflect_eulerInsertionStep_one (m : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ m) :
    (eulerInsertionStep 1 m p).reflect (m + 1) =
      eulerInsertionStep 1 m (p.reflect m) := by
  have hqdeg : (p.reflect m).natDegree ≤ m := by
    exact (natDegree_reflect_le).trans (by simp [max_eq_left hp])
  have houtdeg : (eulerInsertionStep 1 m p).natDegree ≤ m + 1 :=
    (natDegree_eulerInsertionStep_le 1 m p).trans (by lia)
  have hroutdeg : (eulerInsertionStep 1 m (p.reflect m)).natDegree ≤ m + 1 :=
    (natDegree_eulerInsertionStep_le 1 m (p.reflect m)).trans (by lia)
  ext k
  by_cases hk : k ≤ m + 1
  · cases k with
    | zero =>
      rw [coeff_reflect, revAt_zero, coeff_eulerInsertionStep_succ,
        coeff_eulerInsertionStep_zero, coeff_reflect, revAt_zero]
      have hzero : p.coeff (m + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      rw [hzero]
      ring
    | succ i =>
      by_cases hi : i = m
      · subst i
        rw [coeff_reflect, revAt_le (by lia : m + 1 ≤ m + 1), Nat.sub_self,
          coeff_eulerInsertionStep_zero, coeff_eulerInsertionStep_succ,
          coeff_reflect, coeff_reflect,
          revAt_eq_self_of_lt (by lia : m < m + 1),
          revAt_le (by lia : m ≤ m)]
        have hzero : p.coeff (m + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        simp [hzero]
      · have him : i < m := by lia
        have hindex : m + 1 - (i + 1) = (m - i - 1) + 1 := by lia
        rw [coeff_reflect, revAt_le hk, hindex,
          coeff_eulerInsertionStep_succ, coeff_eulerInsertionStep_succ,
          coeff_reflect, coeff_reflect,
          revAt_le (by lia : i + 1 ≤ m),
          revAt_le (by lia : i ≤ m)]
        have hsub : ((m - i - 1 : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) - 1 := by
          have h : m - i - 1 + i + 1 = m := by lia
          have hcast := congrArg (fun z : ℕ => (z : ℝ)) h
          push_cast at hcast
          linarith
        rw [hsub]
        have hidxA : (m - i - 1) + 1 = m - i := by lia
        have hidxB : m - (i + 1) = m - i - 1 := by lia
        rw [hidxA, hidxB]
        ring
  · have hkm : m + 1 < k := by lia
    rw [coeff_reflect, revAt_eq_self_of_lt hkm,
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt houtdeg hkm),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hroutdeg hkm)]

/-- Ambient-degree reciprocal of the actual derangement descent enumerator. -/
def reciprocalDerangementPolynomial (n : ℕ) : ℝ[X] :=
  (derangementDescentPolynomial n).reflect (n - 1)

/-- A word on `n` letters has at most `n - 1` descents, giving the
ambient degree bound used by the reciprocal recurrence. -/
theorem derangementDescentPolynomial_natDegree_le (n : ℕ) :
    (derangementDescentPolynomial n).natDegree ≤ n - 1 := by
  classical
  unfold derangementDescentPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro π _
  split_ifs
  · rw [natDegree_X_pow]
    simpa [Equiv.Perm.descentCount_eq_list] using
      (List.descentCount_le_length_sub_one (List.ofFn π))
  · simp

/-- The algebraic passage from the Fu--Lin--Zeng recurrence to the
reciprocal recurrence. The hypothesis is exactly the semantic recurrence
for the actual derangement descent enumerator. -/
private theorem reciprocalDerangementPolynomial_recurrence_of_descent
    (n : ℕ) (hn : 1 ≤ n)
    (hrec : derangementDescentPolynomial (n + 1) =
      eulerInsertionStep 1 (n - 1) (derangementDescentPolynomial n) +
        C ((-1 : ℝ) ^ (n + 1)) * X ^ n) :
    reciprocalDerangementPolynomial (n + 1) =
      eulerInsertionStep 1 (n - 1) (reciprocalDerangementPolynomial n) +
        C ((-1 : ℝ) ^ (n + 1)) := by
  have hbound := derangementDescentPolynomial_natDegree_le n
  have hidx : n - 1 + 1 = n := by lia
  have hreflect :
      (eulerInsertionStep 1 (n - 1) (derangementDescentPolynomial n)).reflect n =
        eulerInsertionStep 1 (n - 1)
          ((derangementDescentPolynomial n).reflect (n - 1)) := by
    simpa only [hidx] using
      reflect_eulerInsertionStep_one (n - 1) (derangementDescentPolynomial n) hbound
  unfold reciprocalDerangementPolynomial
  rw [show n + 1 - 1 = n by lia, hrec, reflect_add,
    hreflect, reflect_C_mul_X_pow]
  simp [revAt_le]

/-- The reciprocal recurrence uniquely identifies the reciprocal sequence
with the `a = 1` deletion-stable family. Both premises will be discharged
from the actual permutation enumerator. -/
private theorem reciprocalDerangementPolynomial_eq_deletion_of_recurrence
    (hbase : reciprocalDerangementPolynomial 2 = 1)
    (hrec : ∀ n, 2 ≤ n → reciprocalDerangementPolynomial (n + 1) =
      eulerInsertionStep 1 (n - 1) (reciprocalDerangementPolynomial n) +
        C ((-1 : ℝ) ^ (n + 1)))
    (r : ℕ) :
    reciprocalDerangementPolynomial (r + 2) = deletionPolynomial 1 r := by
  induction r with
  | zero => simpa [deletionPolynomial] using hbase
  | succ r ih =>
    have hstep := hrec (r + 2) (by lia)
    have hindex : r + 1 + 2 = r + 2 + 1 := by lia
    have hopen : 1 + r = r + 2 - 1 := by lia
    have hsign : (-1 : ℝ) ^ (r + 2 + 1) = (-1 : ℝ) ^ (r + 1) := by
      have hindex' : r + 2 + 1 = r + 1 + 2 := by lia
      rw [hindex', pow_add]
      norm_num
    rw [hindex, hstep, ih, ← hopen, hsign]
    exact (deletionPolynomial_recurrence 1 r).symm

/-- Algebraic root transfer back through reflection; this uses the actual
descent polynomial and the proved larger-family PF theorem. -/
private theorem derangementDescentPolynomial_splits_of_reciprocal_eq
    (n r : ℕ) (heq : reciprocalDerangementPolynomial n = deletionPolynomial 1 r) :
    (derangementDescentPolynomial n).Splits := by
  have hdeg := derangementDescentPolynomial_natDegree_le n
  have hpos := (deletionPolynomial_degree_nonneg 1 r).2.1
  have hsplit : (deletionPolynomial 1 r).Splits :=
    (deletionPolynomial_isPF 1 r).eq_zero_or_splits.resolve_left hpos.ne_zero
  have hsplitQ : (reciprocalDerangementPolynomial n).Splits := heq.symm ▸ hsplit
  exact (Polynomial.splits_reflect_iff hdeg).mp (by
    simpa only [reciprocalDerangementPolynomial] using hsplitQ)

/-- The first reciprocal derangement descent polynomial is one. -/
theorem reciprocalDerangementPolynomial_two :
    reciprocalDerangementPolynomial 2 = 1 := by
  simp [reciprocalDerangementPolynomial, derangementDescentPolynomial_two]

/-- Paper `eq:reciprocalRecurrence` for the actual permutation enumerator. -/
theorem reciprocalDerangementPolynomial_recurrence (n : ℕ) (hn : 2 ≤ n) :
    reciprocalDerangementPolynomial (n + 1) =
      eulerInsertionStep 1 (n - 1) (reciprocalDerangementPolynomial n) +
        C ((-1 : ℝ) ^ (n + 1)) := by
  apply reciprocalDerangementPolynomial_recurrence_of_descent n (by lia)
  simpa only [show n + 1 - 2 = n - 1 by lia,
    show n + 1 - 1 = n by lia] using
      derangementDescentPolynomial_recurrence (n + 1) (by lia)

/-- The reciprocal derangement descent sequence is the `a = 1`
specialization of paper `thm:largerFamily`. -/
theorem reciprocalDerangementPolynomial_eq_deletion (r : ℕ) :
    reciprocalDerangementPolynomial (r + 2) = deletionPolynomial 1 r :=
  reciprocalDerangementPolynomial_eq_deletion_of_recurrence
    reciprocalDerangementPolynomial_two
    (fun n hn => reciprocalDerangementPolynomial_recurrence n hn) r

/-- The reciprocal derangement polynomial has the exact manuscript degree
`n - 2` for `n ≥ 2`. -/
theorem reciprocalDerangementPolynomial_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (reciprocalDerangementPolynomial n).natDegree = n - 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by lia⟩
  rw [reciprocalDerangementPolynomial_eq_deletion,
    (deletionPolynomial_degree_nonneg 1 r).1]
  simp

/-- Paper `eq:reciprocalPolynomial`, interpreted as an actual permutation
enumerator: reflection exchanges descents and ascents. -/
theorem reciprocalDerangementPolynomial_eq_ascent_sum (n : ℕ) :
    reciprocalDerangementPolynomial n =
      ∑ π : Equiv.Perm (Fin n),
        if ∀ i, π i ≠ i then X ^ π.ascentCount else 0 := by
  classical
  have hsum (s : Finset (Equiv.Perm (Fin n))) :
      (s.sum fun π => if ∀ i, π i ≠ i then (X : ℝ[X]) ^ π.descentCount else 0).reflect
          (n - 1) =
        s.sum fun π =>
          (if ∀ i, π i ≠ i then (X : ℝ[X]) ^ π.descentCount else 0).reflect
            (n - 1) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert π s hπ ih => simp only [Finset.sum_insert hπ, reflect_add, ih]
  unfold reciprocalDerangementPolynomial derangementDescentPolynomial
  rw [hsum]
  apply Finset.sum_congr rfl
  intro π _
  split_ifs with hπ
  · rw [reflect_monomial, revAt_le (by
      have h := π.descentCount_add_ascentCount
      lia)]
    have h := π.descentCount_add_ascentCount
    congr 1
    lia
  · simp

/-- Paper `thm:derangementRealRooted`: the actual derangement descent
polynomial splits over the reals for all `n ≥ 2`. -/
theorem derangementDescentPolynomial_splits (n : ℕ) (hn : 2 ≤ n) :
    (derangementDescentPolynomial n).Splits := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by lia⟩
  exact derangementDescentPolynomial_splits_of_reciprocal_eq (r + 2) r
    (reciprocalDerangementPolynomial_eq_deletion r)

/-- Paper `thm:derangementRealRooted`, including the nonpositive root
location supplied by the enumerator's nonnegative coefficients. -/
theorem derangementDescentPolynomial_hasOnlyNonposRoots (n : ℕ) (hn : 2 ≤ n) :
    HasOnlyNonposRoots (derangementDescentPolynomial n) :=
  Or.inr ⟨derangementDescentPolynomial_splits n hn,
    derangementDescentPolynomial_roots_nonpos n⟩

end RealRooted.EulerianCompendium
