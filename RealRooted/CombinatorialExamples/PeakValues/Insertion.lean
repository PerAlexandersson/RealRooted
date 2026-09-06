import RealRooted.CombinatorialExamples.PeakValues

/-!
# Inserting the maximum into a permutation

This file begins the order-preserving insertion infrastructure used to derive
the peak-value recurrence. The insertion slot is a position in the new
permutation, and the old positions and values retain their relative order.
-/

namespace RealRooted

/-- Rename the final value of a rank-`n + 1` polynomial as `none`, retaining
the old values as `some i`. -/
noncomputable def identifyLast (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  MvPolynomial.renameEquiv ℝ (finSuccEquiv' (Fin.last n)) P

/-- Embed a polynomial in the old variables into the enlarged value set. -/
noncomputable def liftOld {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  MvPolynomial.rename some P

/-- Insert the new maximum value into `π` at `slot`, preserving the order of
the old positions and the names of the old values. -/
def insertMaximum {n : ℕ} (slot : Fin (n + 1))
    (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' slot).trans
    (π.optionCongr.trans (finSuccEquiv' (Fin.last n)).symm)

@[simp] theorem insertMaximum_apply_slot {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    insertMaximum slot π slot = Fin.last n := by
  simp [insertMaximum]

@[simp] theorem insertMaximum_apply_succAbove {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    insertMaximum slot π (slot.succAbove i) = (π i).castSucc := by
  simp [insertMaximum]

@[simp] theorem insertMaximum_symm_apply_last {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    (insertMaximum slot π).symm (Fin.last n) = slot := by
  apply (insertMaximum slot π).injective
  simp

@[simp] theorem insertMaximum_symm_apply_castSucc {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (insertMaximum slot π).symm v.castSucc =
      slot.succAbove (π.symm v) := by
  apply (insertMaximum slot π).injective
  simp

lemma succAbove_val {n : ℕ} (slot : Fin (n + 1)) (i : Fin n) :
    (slot.succAbove i).val =
      if i.val < slot.val then i.val else i.val + 1 := by
  by_cases h : i.castSucc < slot
  · have hv : i.val < slot.val := h
    simp [Fin.succAbove, h, hv]
  · have hv : ¬ i.val < slot.val := h
    simp [Fin.succAbove, h, hv]

lemma succAbove_adjacent_iff {n : ℕ} (slot : Fin (n + 1))
    (i j : Fin n) :
    (slot.succAbove i).val + 1 = (slot.succAbove j).val ↔
      i.val + 1 = j.val ∧ slot.val ≠ j.val := by
  rw [succAbove_val, succAbove_val]
  split_ifs <;> lia

lemma isPeakPosition_succAbove_iff {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    IsPeakPosition (insertMaximum slot π) (slot.succAbove j) ↔
      IsPeakPosition π j ∧
        slot.val ≠ j.val ∧ slot.val ≠ j.val + 1 := by
  constructor
  · rintro ⟨I, K, hIJ, hJK, hI, hK⟩
    have hI_ne : I ≠ slot := by
      intro h
      subst I
      have hbad : Fin.last n < (π j).castSucc := by
        simpa using hI
      have hjlt := (π j).isLt
      have hbadval : n < (π j).val := hbad
      lia
    have hK_ne : K ≠ slot := by
      intro h
      subst K
      have hbad : Fin.last n < (π j).castSucc := by
        simpa using hK
      have hjlt := (π j).isLt
      have hbadval : n < (π j).val := hbad
      lia
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hI_ne
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hK_ne
    subst I
    subst K
    have hij := (succAbove_adjacent_iff slot i j).mp hIJ
    have hjk := (succAbove_adjacent_iff slot j k).mp hJK
    refine ⟨⟨i, k, hij.1, hjk.1, ?_, ?_⟩, hij.2, ?_⟩
    · simpa using hI
    · simpa using hK
    · intro heq
      exact hjk.2 (by lia)
  · rintro ⟨⟨i, k, hij, hjk, hi, hk⟩, hbefore, hafter⟩
    refine ⟨slot.succAbove i, slot.succAbove k, ?_, ?_, ?_, ?_⟩
    · exact (succAbove_adjacent_iff slot i j).mpr ⟨hij, hbefore⟩
    · apply (succAbove_adjacent_iff slot j k).mpr
      refine ⟨hjk, ?_⟩
      intro heq
      exact hafter (by lia)
    · simpa using hi
    · simpa using hk

theorem last_mem_peakValues_insertMaximum_iff {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    Fin.last n ∈ peakValues (insertMaximum slot π) ↔
      slot ≠ 0 ∧ slot ≠ Fin.last n := by
  rw [mem_peakValues_iff, insertMaximum_symm_apply_last]
  constructor
  · rintro ⟨i, k, hij, hjk, hi, hk⟩
    constructor
    · intro h
      have hval : slot.val = 0 := by
        simpa using congrArg Fin.val h
      lia
    · intro h
      have hval : slot.val = n := by
        simpa using congrArg Fin.val h
      have hklt := k.isLt
      lia
  · rintro ⟨hzero, hlast⟩
    let i : Fin (n + 1) :=
      ⟨slot.val - 1, by
        have hslot := slot.isLt
        lia⟩
    let k : Fin (n + 1) :=
      ⟨slot.val + 1, by
        have hslt : slot < Fin.last n :=
          Fin.lt_last_iff_ne_last.mpr hlast
        have hsltval : slot.val < n := hslt
        lia⟩
    refine ⟨i, k, ?_, ?_, ?_, ?_⟩
    · dsimp [i]
      have hpos : 0 < slot.val := Fin.pos_iff_ne_zero.mpr hzero
      lia
    · rfl
    · have hi_ne : i ≠ slot := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [i] at hval
        have hpos : 0 < slot.val := Fin.pos_iff_ne_zero.mpr hzero
        lia
      have himage_ne := (insertMaximum slot π).injective.ne hi_ne
      have himage_lt : insertMaximum slot π i < Fin.last n :=
        Fin.lt_last_iff_ne_last.mpr (by simpa using himage_ne)
      simpa using himage_lt
    · have hk_ne : k ≠ slot := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [k] at hval
        lia
      have hkimage_ne := (insertMaximum slot π).injective.ne hk_ne
      have hkimage_lt : insertMaximum slot π k < Fin.last n :=
        Fin.lt_last_iff_ne_last.mpr (by simpa using hkimage_ne)
      simpa using hkimage_lt

theorem castSucc_mem_peakValues_insertMaximum_iff {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    v.castSucc ∈ peakValues (insertMaximum slot π) ↔
      v ∈ peakValues π ∧
        slot ≠ (π.symm v).castSucc ∧ slot ≠ (π.symm v).succ := by
  rw [mem_peakValues_iff, insertMaximum_symm_apply_castSucc,
    isPeakPosition_succAbove_iff, ← mem_peakValues_iff]
  constructor
  · rintro ⟨hv, hbefore, hafter⟩
    refine ⟨hv, ?_, ?_⟩
    · intro heq
      apply hbefore
      simpa using congrArg Fin.val heq
    · intro heq
      apply hafter
      simpa using congrArg Fin.val heq
  · rintro ⟨hv, hbefore, hafter⟩
    refine ⟨hv, ?_, ?_⟩
    · intro heq
      apply hbefore
      apply Fin.ext
      simpa using heq
    · intro heq
      apply hafter
      apply Fin.ext
      simpa using heq

theorem insertMaximum_apply_eq_last_iff {n : ℕ}
    (slot j : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    insertMaximum slot π j = Fin.last n ↔ j = slot := by
  constructor
  · intro h
    apply (insertMaximum slot π).injective
    rw [h, insertMaximum_apply_slot]
  · rintro rfl
    simp

private theorem insertMaximumPair_injective (n : ℕ) :
    Function.Injective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        insertMaximum p.1 p.2) := by
  rintro ⟨slot, π⟩ ⟨slot', π'⟩ h
  change insertMaximum slot π = insertMaximum slot' π' at h
  have hslot : slot = slot' := by
    rw [← insertMaximum_apply_eq_last_iff slot' slot π']
    calc
      insertMaximum slot' π' slot = insertMaximum slot π slot :=
        (congrArg (fun e : Equiv.Perm (Fin (n + 1)) => e slot) h).symm
      _ = Fin.last n := insertMaximum_apply_slot slot π
  subst slot'
  have hπ : π = π' := by
    apply Equiv.ext
    intro i
    apply Fin.castSucc_injective
    simpa using congrArg
      (fun e : Equiv.Perm (Fin (n + 1)) => e (slot.succAbove i)) h
  subst π'
  rfl

/-- Every permutation of `Fin (n + 1)` is uniquely obtained by inserting the
new maximum into a permutation of `Fin n`. -/
noncomputable def insertMaximumEquiv (n : ℕ) :
    Fin (n + 1) × Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective
    (fun p => insertMaximum p.1 p.2)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨insertMaximumPair_injective n, by
        simp [Fintype.card_perm, Nat.factorial_succ]⟩)

@[simp] theorem insertMaximumEquiv_apply (n : ℕ)
    (p : Fin (n + 1) × Equiv.Perm (Fin n)) :
    insertMaximumEquiv n p = insertMaximum p.1 p.2 :=
  rfl

/-- Reindex the finite sum over rank-`n + 1` permutations by insertion slot
and a rank-`n` permutation. -/
theorem univ_perm_succ_eq_map_insertMaximumEquiv (n : ℕ) :
    (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))) =
      (Finset.univ : Finset (Fin (n + 1) × Equiv.Perm (Fin n))).map
        (insertMaximumEquiv n).toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm

end RealRooted
