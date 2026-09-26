import RealRooted.BrandenVecchi.SmirnovRecurrence
import RealRooted.BrandenVecchi.SmirnovSpecialization

/-!
# Interlacing of literal Smirnov descent polynomials

This file applies the Gustafsson--Solus threshold-matrix theorem to the
reversed-last-letter recurrence.  It keeps the zero-aware boundary cases, in
particular the one-letter alphabet in word lengths at least two.
-/

open Polynomial

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The identity thresholds in the reversed-last-letter recurrence are
weakly increasing. -/
theorem smirnovThreshold_weaklyIncreasing (m : ℕ) :
    GustafssonSolusWeaklyIncreasing (id : Fin m → Fin m) := by
  intro i j hij
  simpa using hij

/-- Deleting every equal-letter pivot satisfies the Gustafsson--Solus
no-switch condition. -/
theorem smirnovDropPivot_noSwitchAfterDrop (m : ℕ) :
    GustafssonSolusNoSwitchAfterDrop
      (id : Fin m → Fin m) (fun _ => true) := by
  intro i j hij heq hi
  rfl

private theorem smirnovRecurrenceMatrix_nonneg (m : ℕ) :
    ∀ row ∈ gustafssonSolusMatrix
        (id : Fin m → Fin m) (fun _ => true),
      ∀ p ∈ row, HasNonnegCoeffs p := by
  have hstructure :=
    hasRowThresholdLinearStructure_gustafssonSolusMatrix
      (dropPivot := fun _ => true)
      (smirnovThreshold_weaklyIncreasing m)
  obtain ⟨threshold, hrows, hmono⟩ := hstructure
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hrow
  exact hasRowThreshold_nonneg (hrows i)

private theorem smirnovDescentRefinedList_zero_data (m : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (smirnovDescentRefinedList m 0) := by
  rw [smirnovDescentRefinedList_zero]
  constructor
  · constructor
    · rw [isInterlacingSeq0_iff_pairwise]
      have hinterl : Interl (1 : ℝ[X]) 1 :=
        Interl.refl fun _ => Polynomial.Splits.one
      simp [hinterl]
    · intro f hf
      simp only [List.mem_replicate] at hf
      rcases hf with ⟨hm, rfl⟩
      exact hasNonnegCoeffs_one
  · intro f hf hne
    simp only [List.mem_replicate] at hf
    rcases hf with ⟨hm, rfl⟩
    exact ⟨one_ne_zero, Polynomial.Splits.one⟩

private theorem smirnovDescentRefinedList_step
    (m r : ℕ)
    (hdata : IsInterlacingSeq0NonnegRealRooted
      (smirnovDescentRefinedList m r)) :
    IsInterlacingSeq0NonnegRealRooted
      (smirnovDescentRefinedList m (r + 1)) := by
  rw [smirnovDescentRefinedList_succ]
  exact matrix_preserves_interlacing_seq0_of_2x2_weak
    (gustafssonSolusMatrix (id : Fin m → Fin m) (fun _ => true))
    (gustafssonSolusMatrix_rect _ _)
    (smirnovRecurrenceMatrix_nonneg m)
    (GustafssonSolus2x2FromNoSwitchStatement
      (id : Fin m → Fin m) (fun _ => true)
      (smirnovThreshold_weaklyIncreasing m)
      (smirnovDropPivot_noSwitchAfterDrop m))
    (smirnovDescentRefinedList m r)
    (length_smirnovDescentRefinedList m r)
    hdata.1 hdata.2

/-- Every reversed-last-letter vector is zero-aware nonnegatively
interlacing, and every nonzero component splits over the reals. -/
theorem smirnovDescentRefined_interlacing (m r : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (smirnovDescentRefinedList m r) := by
  induction r with
  | zero => exact smirnovDescentRefinedList_zero_data m
  | succ r ih => exact smirnovDescentRefinedList_step m r ih

/-- Ordered reversed-last-letter components are in zero-aware proper
position. -/
theorem smirnovDescentRefined_interl (m r : ℕ) (i j : Fin m)
    (hij : i < j) :
    Interl (smirnovDescentRefined m r i)
      (smirnovDescentRefined m r j) := by
  let i' : Fin (smirnovDescentRefinedList m r).length :=
    ⟨i, by simp⟩
  let j' : Fin (smirnovDescentRefinedList m r).length :=
    ⟨j, by simp⟩
  have hij' : i' < j' := by simpa [i', j'] using hij
  have hinterl :=
    (smirnovDescentRefined_interlacing m r).1.1.prec0 hij'
  simpa [smirnovDescentRefinedList, i', j'] using hinterl

/-- On an alphabet with at least two letters, every fixed-final-letter
component is nonzero. -/
theorem smirnovDescentRefined_ne_zero (m r : ℕ) (hm : 1 < m)
    (i : Fin m) :
    smirnovDescentRefined m r i ≠ 0 := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
      rw [smirnovDescentRefined_succ, ← List.sum_ofFn]
      obtain ⟨j, hji⟩ :=
        Fintype.exists_ne_of_one_lt_card (by simpa using hm) i
      refine sum_ne_zero_of_hasNonnegCoeffs_of_mem_ne_zero
        (p := gustafssonSolusEntry i true j *
          smirnovDescentRefined m r j) ?_ ?_ ?_
      · intro p hp
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
        exact
          (isNonnegLinearForm_hasNonnegCoeffs
            (isNonnegLinearForm_gustafssonSolusEntry i true k)).mul
          ((smirnovDescentRefined_interlacing m r).1.2 _
            (List.mem_ofFn.mpr ⟨k, rfl⟩))
      · exact List.mem_ofFn.mpr ⟨j, rfl⟩
      · apply mul_ne_zero
        · by_cases hlt : j < i
          · simp [gustafssonSolusEntry, hlt]
          · simp [gustafssonSolusEntry, hlt, hji]
        · exact ih j

/-- The refined vector has nonzero sum on an alphabet with at least two
letters. -/
theorem smirnovDescentRefinedList_sum_ne_zero
    (m : ℕ) (hm : 1 < m) (r : ℕ) :
    (smirnovDescentRefinedList m r).sum ≠ 0 := by
  let i : Fin m := ⟨0, by lia⟩
  let i' : Fin (smirnovDescentRefinedList m r).length :=
    ⟨i, by simp⟩
  refine sum_ne_zero_of_hasNonnegCoeffs_of_mem_ne_zero
    (smirnovDescentRefined_interlacing m r).1.2
    (List.get_mem _ i') ?_
  simpa [smirnovDescentRefinedList, i'] using
    smirnovDescentRefined_ne_zero m r hm i

/-- The one-letter refinement vanishes after one transition because its only
matrix entry is the deleted pivot. -/
@[simp]
theorem smirnovDescentRefined_one_succ (r : ℕ) (i : Fin 1) :
    smirnovDescentRefined 1 (r + 1) i = 0 := by
  rw [smirnovDescentRefined_succ]
  simp [gustafssonSolusEntry, Subsingleton.elim i 0]

/-- There are no Smirnov words of length at least two on a one-letter
alphabet. -/
@[simp]
theorem smirnovDescentPolynomial_one_add_two (r : ℕ) :
    smirnovDescentPolynomial 1 (r + 2) = 0 := by
  rw [show r + 2 = (r + 1) + 1 by lia,
    smirnovDescentPolynomial_succ]
  simp [smirnovDescentRefinedList]

/-- The length-one polynomial records the size of the alphabet. -/
@[simp]
theorem smirnovDescentPolynomial_one (m : ℕ) :
    smirnovDescentPolynomial m 1 = C (m : ℝ) := by
  rw [show 1 = 0 + 1 by rfl, smirnovDescentPolynomial_succ,
    smirnovDescentRefinedList_zero]
  simp

/-- Literal Smirnov descent polynomials have nonnegative coefficients. -/
theorem smirnovDescentPolynomial_nonnegCoeffs (m n : ℕ) :
    HasNonnegCoeffs (smirnovDescentPolynomial m n) := by
  cases n with
  | zero =>
      rw [smirnovDescentPolynomial, weightedSmirnovPolynomial_zero]
      exact hasNonnegCoeffs_one
  | succ r =>
      rw [smirnovDescentPolynomial_succ]
      exact hasNonnegCoeffs_sum _
        (smirnovDescentRefined_interlacing m r).1.2

/-- Literal Smirnov descent polynomials are nonzero in every length when the
alphabet has at least two letters. -/
theorem smirnovDescentPolynomial_ne_zero
    (m : ℕ) (hm : 1 < m) (n : ℕ) :
    smirnovDescentPolynomial m n ≠ 0 := by
  cases n with
  | zero =>
      simp [smirnovDescentPolynomial]
  | succ r =>
      rw [smirnovDescentPolynomial_succ]
      exact smirnovDescentRefinedList_sum_ne_zero m hm r

/-- On any nonempty alphabet, the empty- and one-letter word polynomials are
nonzero.  Longer words require at least two alphabet letters. -/
theorem smirnovDescentPolynomial_ne_zero_of_pos_of_le_one
    (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : n ≤ 1) :
    smirnovDescentPolynomial m n ≠ 0 := by
  obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hn
  · simp [smirnovDescentPolynomial]
  · rw [smirnovDescentPolynomial_one]
    exact C_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')

/-- Literal Smirnov descent polynomials split over the reals, including the
zero polynomial on a one-letter alphabet in lengths at least two. -/
theorem smirnovDescentPolynomial_splits (m n : ℕ) :
    (smirnovDescentPolynomial m n).Splits := by
  cases n with
  | zero =>
      simp [smirnovDescentPolynomial]
  | succ r =>
      rw [smirnovDescentPolynomial_succ]
      by_cases hsum : (smirnovDescentRefinedList m r).sum = 0
      · rw [hsum]
        exact Polynomial.Splits.zero
      · exact (isRealRooted_sum_of_isInterlacingSeq0Nonneg
          (smirnovDescentRefined_interlacing m r).1
          (smirnovDescentRefined_interlacing m r).2 hsum).2

/-- The positive finite supersymmetric Chow specialization has nonnegative
coefficients. -/
theorem finiteSupersymmetricChow_replicate_one_nil_nonnegCoeffs
    (m n : ℕ) :
    HasNonnegCoeffs
      (finiteSupersymmetricChow (List.replicate m (1 : ℝ)) [] n) := by
  rw [finiteSupersymmetricChow_replicate_one_nil_eq_smirnov]
  exact smirnovDescentPolynomial_nonnegCoeffs m n

/-- The positive finite supersymmetric Chow specialization splits over the
reals. -/
theorem finiteSupersymmetricChow_replicate_one_nil_splits
    (m n : ℕ) :
    (finiteSupersymmetricChow
      (List.replicate m (1 : ℝ)) [] n).Splits := by
  rw [finiteSupersymmetricChow_replicate_one_nil_eq_smirnov]
  exact smirnovDescentPolynomial_splits m n

/-- The positive finite supersymmetric Chow specialization is nonzero in
every length when at least two positive letters are present. -/
theorem finiteSupersymmetricChow_replicate_one_nil_ne_zero
    (m : ℕ) (hm : 1 < m) (n : ℕ) :
    finiteSupersymmetricChow
      (List.replicate m (1 : ℝ)) [] n ≠ 0 := by
  rw [finiteSupersymmetricChow_replicate_one_nil_eq_smirnov]
  exact smirnovDescentPolynomial_ne_zero m hm n

/-! ## Deprecated interlacing names -/

@[deprecated smirnovDescentRefined_interl (since := "2026-09-26")]
alias smirnovDescentRefined_prec0 := smirnovDescentRefined_interl

end

end RealRooted.BrandenVecchi
