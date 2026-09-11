import RealRooted.ParkingFunctions.Descents.Basic
import RealRooted.ThresholdMatrix

/-!
# All-word descent polynomials

This is the all-word side of the Diaconis--Hicks parking-function descent
identity.  It uses a last-letter refinement and the checked
Haglund--Zhang threshold-matrix theorem to prove splitness of the recursively
defined word polynomial.  Identifying that polynomial with the literal finite
sum over words, and transferring it to parking functions, remain separate
combinatorial work.

This module is extracted from the checked all-word A333829 development in
`sqrt-of-2/real-rooted-oeis-proofs` PR #123.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

open RealRooted.OEIS.Backend

/-- Threshold rows for the reversed-last-letter word recursion. -/
def wordDescentRows (m : ℕ) : List (ℕ × ℝ[X]) :=
  (List.range m).map fun j => (j, (1 : ℝ[X]))

@[simp]
theorem length_wordDescentRows (m : ℕ) : (wordDescentRows m).length = m := by
  simp [wordDescentRows]

@[simp]
theorem get_wordDescentRows_fst (m : ℕ) (i : Fin (wordDescentRows m).length) :
    ((wordDescentRows m).get i).1 = i.1 := by
  simp only [wordDescentRows, List.get_eq_getElem, List.getElem_map]
  grind

private theorem wordDescentRows_data (m : ℕ) : HZData (wordDescentRows m) := by
  constructor
  · intro p hp
    simp only [wordDescentRows, List.mem_map] at hp
    obtain ⟨j, _, rfl⟩ := hp
    exact Or.inl rfl
  · intro i j hij
    rw [get_wordDescentRows_fst, get_wordDescentRows_fst]
    exact hij
  · intro i j _ _ h
    simp [wordDescentRows, List.get_eq_getElem, List.getElem_map] at h

/-- Last-letter-refined descent enumerators for nonempty words on an alphabet
of size `m`, with terminal letters in reverse order. -/
def wordDescentRefined (m : ℕ) : ℕ → List ℝ[X]
  | 0 => List.replicate m 1
  | r + 1 => matPolyAction (hzMatrix m (wordDescentRows m)) (wordDescentRefined m r)

@[simp]
theorem length_wordDescentRefined (m r : ℕ) :
    (wordDescentRefined m r).length = m := by
  induction r with
  | zero => simp [wordDescentRefined]
  | succ r => simp [wordDescentRefined]

private theorem replicate_one_zipWith_sum (fs : List ℝ[X]) :
    ((List.replicate fs.length 1).zipWith (· * ·) fs).sum = fs.sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, one_mul, List.sum_cons]
      simp_all

private theorem thresholdRow_zero_one (q : ℕ) :
    thresholdRow q 0 (1 : ℝ[X]) = List.replicate q 1 := by
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    rw [show (thresholdRow q 0 (1 : ℝ[X])).get ⟨i, hi₁⟩ =
        thresholdEntry 0 1 i by exact get_thresholdRow ⟨i, hi₁⟩]
    simp [thresholdEntry]

private theorem thresholdRow_succ (q t : ℕ) :
    thresholdRow (q + 1) (t + 1) (1 : ℝ[X]) =
      X :: thresholdRow q t 1 := by
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    rw [show (thresholdRow (q + 1) (t + 1) (1 : ℝ[X])).get ⟨i, hi₁⟩ =
        thresholdEntry (t + 1) 1 i by exact get_thresholdRow ⟨i, hi₁⟩]
    cases i with
    | zero => simp [thresholdEntry]
    | succ i =>
        rw [show (X :: thresholdRow q t (1 : ℝ[X])).get ⟨i + 1, hi₂⟩ =
            (thresholdRow q t 1).get ⟨i, by grind⟩ by simp]
        rw [show (thresholdRow q t (1 : ℝ[X])).get ⟨i, by grind⟩ =
            thresholdEntry t 1 i by exact get_thresholdRow ⟨i, by grind⟩]
        rcases lt_trichotomy i t with hit | hit | hit
        · have hs : i + 1 < t + 1 := by lia
          simp [thresholdEntry, hit, hs]
        · simp_all
        · simp [thresholdEntry]

private theorem zipWith_thresholdRow_one_sum (fs : List ℝ[X]) (t : ℕ) :
    ((thresholdRow fs.length t 1).zipWith (· * ·) fs).sum =
      staircaseSum fs t := by
  induction fs generalizing t with
  | nil => simp [staircaseSum, thresholdRow]
  | cons f fs ih =>
      cases t with
      | zero =>
          rw [thresholdRow_zero_one]
          simp only [List.length_cons]
          rw [List.replicate_succ, List.zipWith_cons_cons, List.sum_cons,
            one_mul, replicate_one_zipWith_sum]
          simp
      | succ t =>
          rw [List.length_cons, thresholdRow_succ]
          simp only [List.zipWith_cons_cons, List.sum_cons]
          rw [ih]
          simp [staircaseSum]
          ring

/-- The matrix definition unfolds to the expected last-letter recurrence. -/
theorem wordDescentRefined_succ_get (m r : ℕ) (i : Fin m) :
    (wordDescentRefined m (r + 1))[i.1]'(by simp) =
      staircaseSum (wordDescentRefined m r) i.1 := by
  change
    (matPolyAction (hzMatrix m (wordDescentRows m))
      (wordDescentRefined m r))[i.1]'_ = staircaseSum (wordDescentRefined m r) i.1
  simp only [matPolyAction, hzMatrix, thresholdMatrix, wordDescentRows, List.map_map,
    List.getElem_map, List.getElem_range, Function.comp_apply]
  simpa only [length_wordDescentRefined] using
    zipWith_thresholdRow_one_sum (wordDescentRefined m r) i.1

private theorem wordDescentRefined_zero_interlacing (m : ℕ) :
    IsInterlacingSeq0Nonneg (wordDescentRefined m 0) := by
  constructor
  · rw [isInterlacingSeq0_iff_pairwise]
    have hprec : Prec0 (1 : ℝ[X]) 1 :=
      (prec_refl (by simp) Polynomial.Splits.one).toPrec0
    simp [wordDescentRefined, hprec]
  · intro f hf
    simp only [wordDescentRefined, List.mem_replicate] at hf
    rcases hf with ⟨_, rfl⟩
    exact hasNonnegCoeffs_one

private theorem wordDescentRefined_zero_realRooted (m : ℕ) :
    ∀ f ∈ wordDescentRefined m 0, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  intro f hf _
  simp only [wordDescentRefined, List.mem_replicate] at hf
  rcases hf with ⟨_, rfl⟩
  exact ⟨one_ne_zero, Polynomial.Splits.one⟩

/-- Every last-letter vector is weakly interlacing, and every nonzero
component is split with nonnegative coefficients. -/
theorem wordDescentRefined_interlacing (m r : ℕ) :
    IsInterlacingSeq0Nonneg (wordDescentRefined m r) ∧
      ∀ f ∈ wordDescentRefined m r, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  induction r with
  | zero =>
      exact ⟨wordDescentRefined_zero_interlacing m, wordDescentRefined_zero_realRooted m⟩
  | succ r ih =>
      simpa [wordDescentRefined] using
        haglund_zhang_s_inversion_interlacing_weak
          (wordDescentRows m) (wordDescentRows_data m) (wordDescentRefined m r)
          (length_wordDescentRefined m r) ih.1 ih.2

/-- The refined sum is nonzero on every nonempty alphabet. -/
theorem wordDescentRefined_sum_ne_zero (m : ℕ) (hm : 0 < m) (r : ℕ) :
    (wordDescentRefined m r).sum ≠ 0 := by
  induction r with
  | zero =>
      simp [wordDescentRefined, hm.ne']
  | succ r ih =>
      have hdata := wordDescentRefined_interlacing m (r + 1)
      let i : Fin (wordDescentRefined m (r + 1)).length :=
        ⟨0, by simpa using hm⟩
      refine sum_ne_zero_of_hasNonnegCoeffs_of_mem_ne_zero
        hdata.1.2 (List.get_mem _ i) ?_
      change (wordDescentRefined m (r + 1))[0]'(by simpa using hm) ≠ 0
      rw [wordDescentRefined_succ_get m r ⟨0, hm⟩]
      simpa using ih

/-- Descent polynomial of all words of length `n` on an alphabet of size `m`.
The empty word has weight `1`; positive lengths use the last-letter refinement. -/
def wordDescentPolynomial (m : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | r + 1 => (wordDescentRefined m r).sum

theorem wordDescentPolynomial_ne_zero (m : ℕ) (hm : 0 < m) (n : ℕ) :
    wordDescentPolynomial m n ≠ 0 := by
  cases n with
  | zero => simp [wordDescentPolynomial]
  | succ r =>
      simpa [wordDescentPolynomial] using wordDescentRefined_sum_ne_zero m hm r

/-- The recursively defined descent polynomial of all words on a nonempty
alphabet splits over the reals. -/
theorem wordDescentPolynomial_splits (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (wordDescentPolynomial m n).Splits := by
  cases n with
  | zero => simp [wordDescentPolynomial]
  | succ r =>
      exact
        (isRealRooted_sum_of_isInterlacingSeq0Nonneg
          (wordDescentRefined_interlacing m r).1
          (wordDescentRefined_interlacing m r).2
          (wordDescentRefined_sum_ne_zero m hm r)).2

end

end RealRooted.ParkingFunctions
