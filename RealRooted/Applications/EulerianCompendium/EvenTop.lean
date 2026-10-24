import RealRooted.Applications.EulerianCompendium.Definitions
import RealRooted.CombinatorialExamples.PeakValues.Insertion

/-!
# Descents with even top

The fixed polynomial is the permutation sum in `Definitions`. The insertion
equivalence in the pinned RealRooted library provides the combinatorial route
to the two recurrences of `thm:evenTopInterlacing`: an old even-top descent is
destroyed precisely when the maximum is inserted immediately after its top;
the new maximum contributes a descent precisely when it is even and is not
inserted at the final slot.
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerianCompendium

/-- The permutation sum has total mass `n!` at `1`. -/
theorem evenTopDescentPolynomial_eval_one (n : ℕ) :
    (evenTopDescentPolynomial n).eval 1 = (Nat.factorial n : ℝ) := by
  simp [evenTopDescentPolynomial, eval_finsetSum, Fintype.card_perm]

/-- Every row of the actual permutation enumerator is nonzero. -/
theorem evenTopDescentPolynomial_ne_zero (n : ℕ) :
    evenTopDescentPolynomial n ≠ 0 := by
  intro h
  have hval := congrArg (fun p : ℝ[X] => p.eval 1) h
  rw [evenTopDescentPolynomial_eval_one] at hval
  exact Nat.factorial_ne_zero n (by simpa using hval)

/-- The actual permutation sum has nonnegative coefficients. -/
theorem evenTopDescentPolynomial_nonneg_coeffs (n : ℕ) :
    RealRooted.HasNonnegCoeffs (evenTopDescentPolynomial n) := by
  unfold evenTopDescentPolynomial
  exact RealRooted.hasNonnegCoeffs_finsetSum _ _
    (fun _ _ => RealRooted.hasNonnegCoeffs_X.pow _)

/-- Every row has positive leading coefficient. -/
theorem evenTopDescentPolynomial_pos_leadingCoeff (n : ℕ) :
    RealRooted.HasPosLeadingCoeff (evenTopDescentPolynomial n) :=
  (evenTopDescentPolynomial_nonneg_coeffs n).pos_leadingCoeff
    (evenTopDescentPolynomial_ne_zero n)

/-- The identity permutation contributes to the constant coefficient. -/
theorem evenTopDescentCount_one (n : ℕ) :
    evenTopDescentCount (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold evenTopDescentCount
  rw [Finset.card_filter_eq_zero_iff]
  intro j _
  rintro ⟨_, k, hk, hlt⟩
  simp only [Equiv.Perm.coe_one, id_eq] at hlt
  have hjk : j < k := by
    apply Fin.lt_def.mpr
    lia
  exact (lt_asymm hjk hlt)

/-- Every row has strictly positive constant term. -/
theorem evenTopDescentPolynomial_eval_zero_pos (n : ℕ) :
    0 < (evenTopDescentPolynomial n).eval 0 := by
  rw [evenTopDescentPolynomial, eval_finsetSum]
  have hnonneg : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      0 ≤ (X ^ evenTopDescentCount π : ℝ[X]).eval 0 := by
    intro π _
    simp only [eval_pow, eval_X]
    positivity
  have hone : 0 < (X ^ evenTopDescentCount (1 : Equiv.Perm (Fin n)) : ℝ[X]).eval 0 := by
    simp [evenTopDescentCount_one]
  exact lt_of_lt_of_le hone (Finset.single_le_sum hnonneg (Finset.mem_univ _))

/-- The empty permutation gives the constant initial row. -/
theorem evenTopDescentPolynomial_zero : evenTopDescentPolynomial 0 = 1 := by
  simp [evenTopDescentPolynomial, evenTopDescentCount]

theorem evenTopDescentCount_le {n : ℕ} (π : Equiv.Perm (Fin n)) :
    evenTopDescentCount π ≤ n := by
  unfold evenTopDescentCount
  simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun j : Fin n =>
      ((π j).val + 1) % 2 = 0 ∧
        ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j))

/-- A descent top cannot be in the final position. -/
theorem evenTopDescentCount_lt (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    evenTopDescentCount π < n + 1 := by
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun j =>
    ((π j).val + 1) % 2 = 0 ∧
      ∃ k : Fin (n + 1), j.val + 1 = k.val ∧ π k < π j
  have hlast : Fin.last n ∉ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨_, k, hk, _⟩
    have hklt := k.isLt
    simp only [Fin.val_last] at hk
    lia
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  have hss : s ⊂ Finset.univ :=
    (Finset.ssubset_iff_of_subset hsub).2
      ⟨Fin.last n, Finset.mem_univ _, hlast⟩
  simpa [evenTopDescentCount, s] using Finset.card_lt_card hss

/-- Every nonempty row has degree strictly below its number of letters. -/
theorem evenTopDescentPolynomial_natDegree_lt (n : ℕ) :
    (evenTopDescentPolynomial (n + 1)).natDegree < n + 1 := by
  have hle : (evenTopDescentPolynomial (n + 1)).natDegree ≤ n := by
    unfold evenTopDescentPolynomial
    apply natDegree_sum_le_of_forall_le
    intro π _
    rw [natDegree_X_pow]
    exact Nat.lt_succ_iff.mp (evenTopDescentCount_lt n π)
  lia

/-- After inserting a maximum, its position is a descent top exactly when
the insertion slot is not the final position. -/
private theorem insertMaximum_has_smaller_successor {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    (∃ k : Fin (n + 1), slot.val + 1 = k.val ∧
      RealRooted.insertMaximum slot π k < RealRooted.insertMaximum slot π slot) ↔
      slot ≠ Fin.last n := by
  constructor
  · rintro ⟨k, hk, _⟩ hlast
    have hslot : slot.val = n := by simp [hlast]
    have hklt := k.isLt
    lia
  · intro hlast
    have hslot : slot.val < n := by
      have h : slot < Fin.last n := Fin.lt_last_iff_ne_last.mpr hlast
      exact h
    let k : Fin (n + 1) := ⟨slot.val + 1, by lia⟩
    refine ⟨k, rfl, ?_⟩
    have hk_ne : k ≠ slot := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [k] at hv
      lia
    have himage_ne : RealRooted.insertMaximum slot π k ≠ Fin.last n := by
      intro h
      exact hk_ne ((RealRooted.insertMaximum_apply_eq_last_iff slot k π).mp h)
    simpa using (Fin.lt_last_iff_ne_last.mpr himage_ne)

/-- The newly inserted value contributes exactly when it is even and is
followed by an old value. -/
theorem insertMaximum_new_evenTop_iff {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    ((RealRooted.insertMaximum slot π slot).val + 1) % 2 = 0 ∧
      (∃ k : Fin (n + 1), slot.val + 1 = k.val ∧
        RealRooted.insertMaximum slot π k < RealRooted.insertMaximum slot π slot) ↔
      (n + 1) % 2 = 0 ∧ slot ≠ Fin.last n := by
  rw [insertMaximum_has_smaller_successor]
  simp

/-- An old even-top descent survives insertion unless the new maximum is
inserted immediately after its top. -/
theorem insertMaximum_old_evenTop_iff {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    (((RealRooted.insertMaximum slot π (slot.succAbove j)).val + 1) % 2 = 0 ∧
      ∃ k' : Fin (n + 1), (slot.succAbove j).val + 1 = k'.val ∧
        RealRooted.insertMaximum slot π k' <
          RealRooted.insertMaximum slot π (slot.succAbove j)) ↔
      ((π j).val + 1) % 2 = 0 ∧
        ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j ∧ slot.val ≠ k.val := by
  constructor
  · rintro ⟨hpar, k', hadj, hlt⟩
    have hk_ne : k' ≠ slot := by
      intro hk
      subst k'
      have hbad : Fin.last n < (π j).castSucc := by simpa using hlt
      have hjlt := (π j).isLt
      have hbadval : n < (π j).val := hbad
      lia
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hk_ne
    obtain ⟨hjk, hslot⟩ :=
      (RealRooted.succAbove_adjacent_iff slot j k).mp hadj
    refine ⟨by simpa using hpar, k, hjk, ?_, hslot⟩
    simpa using hlt
  · rintro ⟨hpar, k, hjk, hlt, hslot⟩
    refine ⟨by simpa using hpar, slot.succAbove k, ?_, ?_⟩
    · exact (RealRooted.succAbove_adjacent_iff slot j k).mpr ⟨hjk, hslot⟩
    · simpa using hlt

/-- The exact statistic change under insertion, before summing over slots. -/
theorem evenTopDescentCount_insertMaximum {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    evenTopDescentCount (RealRooted.insertMaximum slot π) =
      (if (n + 1) % 2 = 0 ∧ slot ≠ Fin.last n then 1 else 0) +
        (Finset.univ.filter fun j : Fin n =>
          ((π j).val + 1) % 2 = 0 ∧
            ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j ∧ slot.val ≠ k.val).card := by
  classical
  unfold evenTopDescentCount
  rw [Finset.card_filter, Fin.sum_univ_succAbove _ slot]
  simp_rw [insertMaximum_new_evenTop_iff, insertMaximum_old_evenTop_iff]
  rw [Finset.card_filter]

/-- Reindex the actual permutation polynomial by the insertion slot of its
maximum value. -/
theorem evenTopDescentPolynomial_succ_as_insertion_sum (n : ℕ) :
    evenTopDescentPolynomial (n + 1) =
      ∑ π : Equiv.Perm (Fin n), ∑ slot : Fin (n + 1),
        X ^ evenTopDescentCount (RealRooted.insertMaximum slot π) := by
  rw [evenTopDescentPolynomial,
    ← Equiv.sum_comp (RealRooted.insertMaximumEquiv n)
      (fun ρ => X ^ evenTopDescentCount ρ)]
  simp only [RealRooted.insertMaximumEquiv_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Slots immediately after an old even-top descent. They are the only slots
where insertion destroys an old counted descent. -/
def evenTopDestroySlots {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin (n + 1)) :=
  (Finset.univ.filter fun j : Fin n =>
    ((π j).val + 1) % 2 = 0 ∧
      ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j).image Fin.succ

theorem evenTopDestroySlots_card {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (evenTopDestroySlots π).card = evenTopDescentCount π := by
  classical
  simpa [evenTopDestroySlots, evenTopDescentCount] using
    (Finset.card_image_of_injective
      (Finset.univ.filter fun j : Fin n =>
        ((π j).val + 1) % 2 = 0 ∧
          ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j)
      (Fin.succ_injective n))

theorem mem_evenTopDestroySlots_iff {n : ℕ}
    (π : Equiv.Perm (Fin n)) (slot : Fin (n + 1)) :
    slot ∈ evenTopDestroySlots π ↔
      ∃ j : Fin n,
        (((π j).val + 1) % 2 = 0 ∧
          ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j) ∧
        slot = j.succ := by
  simp [evenTopDestroySlots, eq_comm]

theorem last_not_mem_evenTopDestroySlots {n : ℕ}
    (π : Equiv.Perm (Fin n)) : Fin.last n ∉ evenTopDestroySlots π := by
  intro h
  obtain ⟨j, ⟨_, k, hjk, _⟩, hslot⟩ :=
    (mem_evenTopDestroySlots_iff π (Fin.last n)).mp h
  have hlast : n = j.val + 1 := by simpa using congrArg Fin.val hslot
  have hklt := k.isLt
  lia

/-- The surviving old descents are exactly those whose successor slot was
not chosen. -/
private theorem surviving_evenTop_positions_eq_filter {n : ℕ}
    (π : Equiv.Perm (Fin n)) (slot : Fin (n + 1)) :
    (Finset.univ.filter fun j : Fin n =>
      ((π j).val + 1) % 2 = 0 ∧
        ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j ∧ slot.val ≠ k.val) =
      (Finset.univ.filter fun j : Fin n =>
        ((π j).val + 1) % 2 = 0 ∧
          ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j).filter
        (fun j => slot ≠ j.succ) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hpar, k, hjk, hlt, hneq⟩
    refine ⟨⟨hpar, k, hjk, hlt⟩, ?_⟩
    intro h
    have hv := congrArg Fin.val h
    exact hneq (by simpa using hv.trans hjk)
  · rintro ⟨⟨hpar, k, hjk, hlt⟩, hneq⟩
    refine ⟨hpar, k, hjk, hlt, ?_⟩
    intro h
    apply hneq
    apply Fin.ext
    simp only [Fin.val_succ]
    lia

/-- Choosing a destroying slot removes exactly one old descent; every other
slot leaves the old count unchanged. -/
theorem surviving_evenTop_positions_card {n : ℕ}
    (π : Equiv.Perm (Fin n)) (slot : Fin (n + 1)) :
    (Finset.univ.filter fun j : Fin n =>
      ((π j).val + 1) % 2 = 0 ∧
        ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j ∧ slot.val ≠ k.val).card =
      if slot ∈ evenTopDestroySlots π then evenTopDescentCount π - 1
      else evenTopDescentCount π := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j =>
    ((π j).val + 1) % 2 = 0 ∧
      ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j
  have hS : S.card = evenTopDescentCount π := rfl
  rw [surviving_evenTop_positions_eq_filter]
  change (S.filter fun j => slot ≠ j.succ).card = _
  by_cases hD : slot ∈ evenTopDestroySlots π
  · obtain ⟨j₀, hj₀, hslot⟩ := (mem_evenTopDestroySlots_iff π slot).mp hD
    have hj₀S : j₀ ∈ S := by simpa [S] using hj₀
    have hiff (j : Fin n) : slot = j.succ ↔ j = j₀ := by
      constructor
      · intro h
        exact (Fin.succ_injective n) (h.symm.trans hslot)
      · rintro rfl
        exact hslot
    have hfilter : S.filter (fun j => slot ≠ j.succ) = S.erase j₀ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hj, hneq⟩
        exact ⟨fun heq => hneq ((hiff j).mpr heq), hj⟩
      · rintro ⟨hneq, hj⟩
        exact ⟨hj, fun hs => hneq ((hiff j).mp hs)⟩
    rw [hfilter, Finset.card_erase_of_mem hj₀S, hS]
    simp [hD]
  · have hfilter : S.filter (fun j => slot ≠ j.succ) = S := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hj
        refine ⟨hj, ?_⟩
        intro hs
        exact hD ((mem_evenTopDestroySlots_iff π slot).mpr
          ⟨j, by simpa [S] using hj, hs⟩)
    rw [hfilter, hS]
    simp [hD]

/-- The insertion change depends only on whether the slot destroys an old
descent and whether the new maximum itself is counted. -/
theorem evenTopDescentCount_insertMaximum_by_slots {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    evenTopDescentCount (RealRooted.insertMaximum slot π) =
      (if (n + 1) % 2 = 0 ∧ slot ≠ Fin.last n then 1 else 0) +
        if slot ∈ evenTopDestroySlots π then evenTopDescentCount π - 1
        else evenTopDescentCount π := by
  rw [evenTopDescentCount_insertMaximum, surviving_evenTop_positions_card]

private theorem sum_if_mem_finset {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) (a b : ℝ[X]) :
    (∑ i : α, if i ∈ D then a else b) =
      D.card • a + (Fintype.card α - D.card) • b := by
  classical
  rw [Finset.sum_ite]
  have hD : (Finset.univ.filter fun i : α => i ∈ D) = D := by
    ext i
    simp
  have hnotD : (Finset.univ.filter fun i : α => i ∉ D) = Finset.univ \ D := by
    ext i
    simp
  rw [hD, hnotD]
  simp [Finset.card_sdiff]

/-- Fixed-permutation slot sum when the inserted maximum is odd. -/
theorem evenTop_odd_insertion_slot_sum {n : ℕ} (hodd : (n + 1) % 2 ≠ 0)
    (π : Equiv.Perm (Fin n)) :
    (∑ slot : Fin (n + 1),
      (X : ℝ[X]) ^ evenTopDescentCount (RealRooted.insertMaximum slot π)) =
      (evenTopDestroySlots π).card • X ^ (evenTopDescentCount π - 1) +
        (n + 1 - (evenTopDestroySlots π).card) • X ^ evenTopDescentCount π := by
  classical
  simp_rw [evenTopDescentCount_insertMaximum_by_slots]
  simp only [hodd, false_and, ite_false, zero_add]
  simpa using
    (sum_if_mem_finset (evenTopDestroySlots π)
      (X ^ (evenTopDescentCount π - 1)) (X ^ evenTopDescentCount π))

/-- Fixed-permutation slot sum when the inserted maximum is even. -/
theorem evenTop_even_insertion_slot_sum {n : ℕ} (heven : (n + 1) % 2 = 0)
    (π : Equiv.Perm (Fin n)) :
    (∑ slot : Fin (n + 1),
      (X : ℝ[X]) ^ evenTopDescentCount (RealRooted.insertMaximum slot π)) =
      (evenTopDescentCount π + 1) • X ^ evenTopDescentCount π +
        (n - evenTopDescentCount π) • X ^ (evenTopDescentCount π + 1) := by
  classical
  have hpoint (slot : Fin (n + 1)) :
      evenTopDescentCount (RealRooted.insertMaximum slot π) =
        if slot ∈ insert (Fin.last n) (evenTopDestroySlots π)
        then evenTopDescentCount π else evenTopDescentCount π + 1 := by
    rw [evenTopDescentCount_insertMaximum_by_slots]
    by_cases hlast : slot = Fin.last n
    · subst slot
      simp [heven, last_not_mem_evenTopDestroySlots π]
    · by_cases hD : slot ∈ evenTopDestroySlots π
      · have hkpos : 1 ≤ evenTopDescentCount π := by
          have hcard := evenTopDestroySlots_card π
          have hpositive : 0 < (evenTopDestroySlots π).card :=
            Finset.card_pos.mpr ⟨slot, hD⟩
          lia
        simp [heven, hlast, hD]
        lia
      · simp [heven, hlast, hD]
        lia
  simp_rw [hpoint]
  simp_rw [pow_ite]
  rw [sum_if_mem_finset]
  have hcard : (insert (Fin.last n) (evenTopDestroySlots π)).card =
      evenTopDescentCount π + 1 := by
    rw [Finset.card_insert_of_notMem (last_not_mem_evenTopDestroySlots π),
      evenTopDestroySlots_card]
  rw [hcard]
  simp only [Fintype.card_fin]
  have hsub : n + 1 - (evenTopDescentCount π + 1) =
      n - evenTopDescentCount π := by lia
  rw [hsub]

private theorem odd_monomial_recurrence (n k : ℕ) (hk : k ≤ n) :
    k • (X : ℝ[X]) ^ (k - 1) + (n + 1 - k) • X ^ k =
      (1 - X) * (X ^ k).derivative + C ((n + 1 : ℕ) : ℝ) * X ^ k := by
  simp only [nsmul_eq_mul, derivative_X_pow, C_eq_natCast]
  have hsub : ((n + 1 - k : ℕ) : ℝ[X]) =
      ((n + 1 : ℕ) : ℝ[X]) - (k : ℝ[X]) := by
    exact Nat.cast_sub (by lia : k ≤ n + 1)
  by_cases hkzero : k = 0
  · subst k
    simp
  · have hkpos : 1 ≤ k := by lia
    have hpow : (X : ℝ[X]) * X ^ (k - 1) = X ^ k := by
      rw [← pow_succ', Nat.sub_add_cancel hkpos]
    calc
      (k : ℝ[X]) * X ^ (k - 1) + ((n + 1 - k : ℕ) : ℝ[X]) * X ^ k =
          (k : ℝ[X]) * X ^ (k - 1) + ((n + 1 : ℕ) : ℝ[X]) * X ^ k -
            (k : ℝ[X]) * (X * X ^ (k - 1)) := by
            rw [hsub, hpow]
            ring
      _ = (1 - X) * ((k : ℝ[X]) * X ^ (k - 1)) +
            ((n + 1 : ℕ) : ℝ[X]) * X ^ k := by ring

private theorem even_monomial_recurrence (n k : ℕ) (hk : k ≤ n) :
    (k + 1) • (X : ℝ[X]) ^ k + (n - k) • X ^ (k + 1) =
      X * (1 - X) * (X ^ k).derivative + (1 + C (n : ℝ) * X) * X ^ k := by
  simp only [nsmul_eq_mul, derivative_X_pow, C_eq_natCast]
  have hsub : ((n - k : ℕ) : ℝ[X]) = (n : ℝ[X]) - (k : ℝ[X]) := by
    exact Nat.cast_sub hk
  by_cases hkzero : k = 0
  · subst k
    simp
  · have hkpos : 1 ≤ k := by lia
    have hpow : (X : ℝ[X]) * X ^ (k - 1) = X ^ k := by
      rw [← pow_succ', Nat.sub_add_cancel hkpos]
    have hpow2 : (X : ℝ[X]) * X ^ k = X ^ (k + 1) := by
      rw [← pow_succ']
    rw [hsub]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      (↑k + 1 : ℝ[X]) * X ^ k + ((n : ℝ[X]) - (k : ℝ[X])) * X ^ (k + 1) =
          (↑k + 1 : ℝ[X]) * X ^ k +
            ((n : ℝ[X]) - (k : ℝ[X])) * (X * X ^ k) := by
            rw [hpow2]
      _ = X * (1 - X) * ((k : ℝ[X]) * X ^ (k - 1)) +
            (1 + (n : ℝ[X]) * X) * X ^ k := by
            rw [← hpow]
            ring

/-- The manuscript's odd-rank differential recurrence, proved for the actual
permutation sum. -/
theorem evenTop_odd_rank_recurrence (n : ℕ) (hodd : (n + 1) % 2 ≠ 0) :
    evenTopDescentPolynomial (n + 1) =
      (1 - X) * (evenTopDescentPolynomial n).derivative +
        C ((n + 1 : ℕ) : ℝ) * evenTopDescentPolynomial n := by
  rw [evenTopDescentPolynomial_succ_as_insertion_sum]
  have hpoint (π : Equiv.Perm (Fin n)) :
      (∑ slot : Fin (n + 1),
        (X : ℝ[X]) ^ evenTopDescentCount (RealRooted.insertMaximum slot π)) =
        (1 - X) * (X ^ evenTopDescentCount π).derivative +
          C ((n + 1 : ℕ) : ℝ) * X ^ evenTopDescentCount π := by
    rw [evenTop_odd_insertion_slot_sum hodd, evenTopDestroySlots_card]
    exact odd_monomial_recurrence n (evenTopDescentCount π)
      (evenTopDescentCount_le π)
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← derivative_sum]
  rfl

/-- The manuscript's even-rank differential recurrence, proved for the actual
permutation sum. -/
theorem evenTop_even_rank_recurrence (n : ℕ) (heven : (n + 1) % 2 = 0) :
    evenTopDescentPolynomial (n + 1) =
      X * (1 - X) * (evenTopDescentPolynomial n).derivative +
        (1 + C (n : ℝ) * X) * evenTopDescentPolynomial n := by
  rw [evenTopDescentPolynomial_succ_as_insertion_sum]
  have hpoint (π : Equiv.Perm (Fin n)) :
      (∑ slot : Fin (n + 1),
        (X : ℝ[X]) ^ evenTopDescentCount (RealRooted.insertMaximum slot π)) =
        X * (1 - X) * (X ^ evenTopDescentCount π).derivative +
          (1 + C (n : ℝ) * X) * X ^ evenTopDescentCount π := by
    rw [evenTop_even_insertion_slot_sum heven]
    exact even_monomial_recurrence n (evenTopDescentCount π)
      (evenTopDescentCount_le π)
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← derivative_sum]
  rfl

/-- The unique permutation of one element contributes one. -/
theorem evenTopDescentPolynomial_one : evenTopDescentPolynomial 1 = 1 := by
  have h := evenTop_odd_rank_recurrence 0 (by norm_num)
  simpa [evenTopDescentPolynomial_zero] using h

/-- The two permutations of two elements give `1 + X`. -/
theorem evenTopDescentPolynomial_two : evenTopDescentPolynomial 2 = 1 + X := by
  have h := evenTop_even_rank_recurrence 1 (by norm_num)
  simpa [evenTopDescentPolynomial_one] using h

end RealRooted.EulerianCompendium
