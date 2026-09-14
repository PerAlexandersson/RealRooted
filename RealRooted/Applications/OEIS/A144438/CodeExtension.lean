import RealRooted.Applications.OEIS.A144438.AdmissibleCode
import RealRooted.Applications.OEIS.A144438.InverseWord

/-!
# Extension of chronological Deco codes

This file packages the last-step operations on chronological Deco codes.  A
normal construction appends one bounded entry, while an exceptional
construction appends the pair `(1, 0)`.  The definitions are independent of
the polynomial recurrence and expose their exact behavior under the generic
minimum-insertion decoder.
-/

namespace RealRooted.Applications.OEIS.DecoCode

/-- Append one bounded entry to a chronological code. -/
def snoc {h : Nat} (c : DecoCode h) (r : Fin (h + 1)) : DecoCode (h + 1) where
  entry := Fin.snoc c r
  entry_lt := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using r.isLt
    · simpa using c.entry_lt i

@[simp] theorem snoc_apply_castSucc {h : Nat} (c : DecoCode h)
    (r : Fin (h + 1)) (j : Fin h) : c.snoc r j.castSucc = c j := by
  simp [snoc]

@[simp] theorem snoc_apply_last {h : Nat} (c : DecoCode h)
    (r : Fin (h + 1)) : c.snoc r (Fin.last h) = r := by
  simp [snoc]

/-- Remove the final entry of a nonempty chronological code. -/
def init {h : Nat} (c : DecoCode (h + 1)) : DecoCode h where
  entry j := c j.castSucc
  entry_lt j := c.entry_lt j.castSucc

@[simp] theorem init_apply {h : Nat} (c : DecoCode (h + 1)) (j : Fin h) :
    c.init j = c j.castSucc := rfl

@[simp] theorem init_snoc {h : Nat} (c : DecoCode h) (r : Fin (h + 1)) :
    (c.snoc r).init = c := by
  ext j
  simp

@[simp] theorem snoc_init_last {h : Nat} (c : DecoCode (h + 1)) :
    c.init.snoc ⟨c (Fin.last h), c.entry_lt (Fin.last h)⟩ = c := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

/-- Split a nonempty chronological code into its prefix and final entry. -/
def snocEquiv (h : Nat) : DecoCode (h + 1) ≃ DecoCode h × Fin (h + 1) where
  toFun c := ⟨c.init, ⟨c (Fin.last h), c.entry_lt (Fin.last h)⟩⟩
  invFun cr := cr.1.snoc cr.2
  left_inv := snoc_init_last
  right_inv cr := by simp

/-- The final entry of an admissible code cannot start an exceptional pair. -/
theorem last_ne_one_of_isAdmissible {h : Nat} {c : DecoCode (h + 1)}
    (hc : c.IsAdmissible) : c (Fin.last h) ≠ 1 := by
  intro hlast
  obtain ⟨_, hnext, _⟩ := hc (Fin.last h) hlast
  rw [Fin.val_last] at hnext
  exact (Nat.lt_irrefl (h + 1)) hnext

/-- Removing a nonzero final entry preserves admissibility. -/
theorem init_isAdmissible_of_last_ne_zero {h : Nat}
    {c : DecoCode (h + 1)} (hc : c.IsAdmissible)
    (hlast : c (Fin.last h) ≠ 0) : c.init.IsAdmissible := by
  intro j hj
  have hjOne : c j.castSucc = 1 := hj
  rcases hc j.castSucc hjOne with ⟨hjLower, hjBound, hjZero⟩
  have hjPrefixBound : j.1 + 1 < h := by
    by_contra hnot
    have heq : j.1 + 1 = h := by lia
    have hindex : (⟨j.castSucc.1 + 1, hjBound⟩ : Fin (h + 1)) =
        Fin.last h := by
      apply Fin.ext
      simpa using heq
    rw [hindex] at hjZero
    exact hlast hjZero
  refine ⟨hjLower, ⟨hjPrefixBound, ?_⟩⟩
  have hindex :
      (⟨j.castSucc.1 + 1, hjBound⟩ : Fin (h + 1)) =
        (⟨j.1 + 1, hjPrefixBound⟩ : Fin h).castSucc := by
    apply Fin.ext
    rfl
  rw [init_apply, ← hindex, hjZero]

/-- Append the exceptional pair `(1, 0)`. -/
def exceptionalExtension {h : Nat} (c : DecoCode h) (hh : 0 < h) :
    DecoCode (h + 2) :=
  (c.snoc ⟨1, by lia⟩).snoc 0

/-- A code whose final two entries are `(1, 0)` is recovered by exceptional
extension of its twice-truncated prefix. -/
theorem exceptionalExtension_init_init {h : Nat} (c : DecoCode (h + 2))
    (hh : 0 < h) (hpenultimate : c (Fin.last h).castSucc = 1)
    (hlast : c (Fin.last (h + 1)) = 0) :
    c.init.init.exceptionalExtension hh = c := by
  ext j
  cases j using Fin.lastCases with
  | last => simpa [exceptionalExtension] using hlast.symm
  | cast i =>
    cases i using Fin.lastCases with
    | last => simpa [exceptionalExtension] using hpenultimate.symm
    | cast k => simp [exceptionalExtension]

@[simp] theorem entryList_snoc {h : Nat} (c : DecoCode h)
    (r : Fin (h + 1)) :
    (c.snoc r).entryList = c.entryList ++ [(r : Nat)] := by
  rw [entryList, entryList, List.ofFn_succ']
  simp [snoc]

@[simp] theorem inverseWord_snoc {h : Nat} (c : DecoCode h)
    (r : Fin (h + 1)) :
    (c.snoc r).inverseWord = MinimumInsertionWord.step r c.inverseWord := by
  simp [inverseWord, entryList_snoc, MinimumInsertionWord.decode,
    MinimumInsertionWord.decodeFrom_append]

/-- Every admissible inverse word of length at least two begins with an
ascent. -/
theorem inverseWord_startsWithAscent {h : Nat} (c : DecoCode h)
    (hc : c.IsAdmissible) (hh : 2 ≤ h) :
    MinimumInsertionWord.StartsWithAscent c.inverseWord := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
      cases h with
      | zero => simp at hh
      | succ h =>
          let r : Fin (h + 1) :=
            ⟨c (Fin.last h), c.entry_lt (Fin.last h)⟩
          have hrOne : (r : Nat) ≠ 1 := by
            exact last_ne_one_of_isAdmissible hc
          have hcode : c.init.snoc r = c := snoc_init_last c
          rw [← hcode, inverseWord_snoc]
          by_cases hrZero : (r : Nat) = 0
          · have hword : c.init.inverseWord ≠ [] := by
              intro hempty
              have hlength := c.init.length_inverseWord
              rw [hempty] at hlength
              simp at hlength
              lia
            simpa [hrZero] using
              (MinimumInsertionWord.StartsWithAscent.step_zero hword
                c.init.inverseWord_isPositive)
          · have hrLower : 2 ≤ (r : Nat) := by lia
            have hhPrefix : 2 ≤ h := by
              have := r.isLt
              lia
            have hprefix := ih h (by lia) c.init
              (init_isAdmissible_of_last_ne_zero hc hrZero) hhPrefix
            obtain ⟨k, hk⟩ : ∃ k, (r : Nat) = k + 2 := by
              exact ⟨(r : Nat) - 2, by lia⟩
            rw [hk]
            exact hprefix.step_add_two k

/-- Appending an entry other than one preserves admissibility. -/
theorem snoc_isAdmissible {h : Nat} {c : DecoCode h}
    (hc : c.IsAdmissible) (r : Fin (h + 1)) (hr : (r : Nat) ≠ 1) :
    (c.snoc r).IsAdmissible := by
  intro j hj
  cases j using Fin.lastCases with
  | last =>
    simp only [snoc_apply_last] at hj
    exact (hr hj).elim
  | cast i =>
    have hiOne : c i = 1 := by simpa using hj
    rcases hc i hiOne with ⟨hiLower, hiBound, hiZero⟩
    have hiNewBound : i.castSucc.1 + 1 < h + 1 := by
      simp only [Fin.val_castSucc]
      lia
    refine ⟨hiLower, ⟨hiNewBound, ?_⟩⟩
    have hindex :
        (⟨i.castSucc.1 + 1, hiNewBound⟩ : Fin (h + 1)) =
          (⟨i.1 + 1, hiBound⟩ : Fin h).castSucc := by
      apply Fin.ext
      rfl
    rw [hindex, snoc_apply_castSucc, hiZero]

/-- Appending a nonexceptional entry retains exactly the old exceptional
starts. -/
theorem exceptionalStarts_snoc_of_ne_one {h : Nat} (c : DecoCode h)
    (r : Fin (h + 1)) (hr : (r : Nat) ≠ 1) :
    (c.snoc r).exceptionalStarts =
      c.exceptionalStarts.map Fin.castSuccEmb := by
  ext j
  cases j using Fin.lastCases with
  | last => simp [DecoCode.mem_exceptionalStarts, hr]
  | cast i => simp [DecoCode.mem_exceptionalStarts]

/-- Appending a nonexceptional entry is the normal extension of the extracted
exceptional history. -/
theorem exceptionalHistory_snoc {h : Nat} {c : DecoCode h}
    (hc : c.IsAdmissible) (hh : 2 ≤ h) (r : Fin (h + 1))
    (hr : (r : Nat) ≠ 1) :
    (c.snoc r).exceptionalHistory (snoc_isAdmissible hc r hr) (by lia) =
      DecoExceptionalHistory.normal (c.exceptionalHistory hc hh) := by
  apply DecoExceptionalHistory.ext
  change (c.snoc r).exceptionalStarts.map exceptionalStartHeightEmbedding =
    c.exceptionalStarts.map exceptionalStartHeightEmbedding
  rw [exceptionalStarts_snoc_of_ne_one c r hr]
  ext j
  simp [exceptionalStartHeightEmbedding]

@[simp] theorem entryList_exceptionalExtension {h : Nat} (c : DecoCode h)
    (hh : 0 < h) :
    (c.exceptionalExtension hh).entryList = c.entryList ++ [1, 0] := by
  simp [exceptionalExtension]

@[simp] theorem inverseWord_exceptionalExtension {h : Nat} (c : DecoCode h)
    (hh : 0 < h) :
    (c.exceptionalExtension hh).inverseWord =
      MinimumInsertionWord.step 0 (MinimumInsertionWord.step 1 c.inverseWord) := by
  simp [exceptionalExtension]

/-- Appending `(1, 0)` to a height-at-least-two admissible code preserves
admissibility. -/
theorem exceptionalExtension_isAdmissible {h : Nat} {c : DecoCode h}
    (hc : c.IsAdmissible) (hh : 2 ≤ h) :
    (c.exceptionalExtension (by lia)).IsAdmissible := by
  intro j hj
  cases j using Fin.lastCases with
  | last => simp [exceptionalExtension] at hj
  | cast i =>
    cases i using Fin.lastCases with
    | last =>
      have hnext : (Fin.last h).castSucc.1 + 1 < h + 2 := by simp
      refine ⟨by simpa using hh, ⟨hnext, ?_⟩⟩
      have hindex :
          (⟨(Fin.last h).castSucc.1 + 1, hnext⟩ : Fin (h + 2)) =
            Fin.last (h + 1) := by
        apply Fin.ext
        simp
      rw [hindex]
      simp [exceptionalExtension]
    | cast k =>
      have hkOne : c k = 1 := by
        simpa [exceptionalExtension] using hj
      rcases hc k hkOne with ⟨hkLower, hkBound, hkZero⟩
      have hkNewBound : k.castSucc.castSucc.1 + 1 < h + 2 := by
        simp only [Fin.val_castSucc]
        lia
      refine ⟨hkLower, ⟨hkNewBound, ?_⟩⟩
      have hindex :
          (⟨k.castSucc.castSucc.1 + 1, hkNewBound⟩ : Fin (h + 2)) =
            ((⟨k.1 + 1, hkBound⟩ : Fin h).castSucc).castSucc := by
        apply Fin.ext
        rfl
      rw [hindex]
      change ((c.snoc ⟨1, by lia⟩).snoc 0)
        ((⟨k.1 + 1, hkBound⟩ : Fin h).castSucc).castSucc = 0
      rw [snoc_apply_castSucc, snoc_apply_castSucc, hkZero]

/-- Appending `(1, 0)` retains the old exceptional starts and adds the first
new position. -/
theorem exceptionalStarts_exceptionalExtension {h : Nat} (c : DecoCode h)
    (hh : 0 < h) :
    (c.exceptionalExtension hh).exceptionalStarts =
      (c.exceptionalStarts.map Fin.castSuccEmb).map Fin.castSuccEmb ∪
        {(Fin.last h).castSucc} := by
  ext j
  cases j using Fin.lastCases with
  | last =>
    constructor
    · intro hmem
      rw [mem_exceptionalStarts] at hmem
      simp [exceptionalExtension] at hmem
    · intro hmem
      exfalso
      rw [Finset.mem_union, Finset.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · rw [Finset.mem_map] at hmem
        obtain ⟨i, hi, hilast⟩ := hmem
        exact Fin.castSucc_ne_last i hilast
      · exact (Fin.castSucc_ne_last (Fin.last h)) hmem.symm
  | cast i =>
    cases i using Fin.lastCases with
    | last => simp [DecoCode.mem_exceptionalStarts, exceptionalExtension]
    | cast k => simp [DecoCode.mem_exceptionalStarts, exceptionalExtension]

/-- Appending `(1, 0)` is the exceptional extension of the extracted
exceptional history. -/
theorem exceptionalHistory_exceptionalExtension {h : Nat} {c : DecoCode h}
    (hc : c.IsAdmissible) (hh : 2 ≤ h) :
    (c.exceptionalExtension (by lia)).exceptionalHistory
        (exceptionalExtension_isAdmissible hc hh) (by lia) =
      DecoExceptionalHistory.exceptional (c.exceptionalHistory hc hh) := by
  apply DecoExceptionalHistory.ext
  change (c.exceptionalExtension (by lia)).exceptionalStarts.map
      exceptionalStartHeightEmbedding =
    insert (h + 1) (c.exceptionalStarts.map exceptionalStartHeightEmbedding)
  rw [exceptionalStarts_exceptionalExtension c (by lia)]
  ext j
  simp [exceptionalStartHeightEmbedding]

end RealRooted.Applications.OEIS.DecoCode
