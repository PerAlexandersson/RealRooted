import RealRooted.ThresholdMatrix.Basic

/-!
# Gustafsson--Solus threshold recursion

The `0`/`1` threshold-entry classification and the finite-indexed and
paper-shaped forms of Gustafsson--Solus Lemma 3.4.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Gustafsson--Solus Lemma 3.4 -/

namespace GustafssonSolus

/-! ### Finite-entry shape helpers -/

private lemma interl_gs_X_X : Interl (X : ℝ[X]) X :=
  Interl.refl fun _ => isRealRooted_X.2

private lemma interl_gs_one_one : Interl (1 : ℝ[X]) 1 := by
  simpa using interl_C_C (1 : ℝ) (1 : ℝ)

private def GS2x2EntryShape (a b c d : ℝ[X]) : Prop :=
  Threshold2x2EntryTuple a b c d 0 0 0 0 ∨
  Threshold2x2EntryTuple a b c d 0 0 X X ∨
  Threshold2x2EntryTuple a b c d 0 1 0 1 ∨
  Threshold2x2EntryTuple a b c d 0 1 X 0 ∨
  Threshold2x2EntryTuple a b c d 0 1 X 1 ∨
  Threshold2x2EntryTuple a b c d 0 1 X X ∨
  Threshold2x2EntryTuple a b c d 1 1 0 0 ∨
  Threshold2x2EntryTuple a b c d 1 1 0 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 1 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 X 0 ∨
  Threshold2x2EntryTuple a b c d 1 1 X 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 X X ∨
  Threshold2x2EntryTuple a b c d X 0 X 0 ∨
  Threshold2x2EntryTuple a b c d X 0 X X ∨
  Threshold2x2EntryTuple a b c d X 1 X 0 ∨
  Threshold2x2EntryTuple a b c d X 1 X 1 ∨
  Threshold2x2EntryTuple a b c d X 1 X X ∨
  Threshold2x2EntryTuple a b c d X X X X

private lemma GS2x2EntryShape.has2x2 {a b c d : ℝ[X]}
    (h : GS2x2EntryShape a b c d) :
    Has2x2InterlacingProperty0 a b c d := by
  intro s t hs ht
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
  · simpa using interl_zero_zero
  · simpa using interl_gs_X_X
  · simpa using (interl_zero_right (C s * X + C t + 1 : ℝ[X]))
  · simpa using interl_affine_X hs ht
  · simpa using interl_affine_add_one_X hs ht
  · simpa using interl_affine_add_X_X hs ht
  · simpa using interl_affine_self hs
  · simpa using interl_affine_add_one_affine hs
  · simpa using interl_affine_add_one_self hs
  · simpa using interl_affine_affine_add_X hs ht
  · simpa using interl_affine_add_one_affine_add_X hs ht
  · simpa using interl_affine_add_X_self hs
  · simpa using (interl_zero_left (((C s * X + C t) * X + X : ℝ[X])))
  · simpa using interl_X_affine_mul_X_add_X hs ht
  · simpa using interl_affine_affine_mul_X_add_X hs ht
  · simpa using interl_affine_add_one_affine_mul_X_add_X hs ht
  · simpa using interl_affine_add_X_affine_mul_X_add_X hs ht
  · simpa using interl_affine_mul_X_add_X_self hs

private lemma gsEntry_shape
    {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 0 ∨ α₁ = 1)
    (hα₂ : α₂ = 0 ∨ α₂ = 1)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 0 → α₂ = 0) :
    GS2x2EntryShape
      (thresholdEntry t₁ α₁ j₁) (thresholdEntry t₁ α₁ j₂)
      (thresholdEntry t₂ α₂ j₁) (thresholdEntry t₂ α₂ j₂) := by
  rcases hα₁ with rfl | rfl <;> rcases hα₂ with rfl | rfl <;>
    simp at hcompat <;>
    unfold GS2x2EntryShape Threshold2x2EntryTuple <;>
    simp only [thresholdEntry] <;>
    split_ifs <;>
    lia

/-- Validity data for the Gustafsson--Solus recursion rows.

The marker `1` encodes the row `g_i`, while marker `0` encodes
`g_i - f_{phi i}`.  The compatibility condition is the global form of the
paper's no-immediate-switch condition within an equal-threshold block. -/
structure RowData (rows : List (ℕ × ℝ[X])) : Prop where
  /-- Every diagonal marker is `0` or `1`. -/
  alpha_mem : ∀ p ∈ rows, p.2 = 0 ∨ p.2 = 1
  /-- Thresholds are nondecreasing down the rows. -/
  thresh_mono : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 ≤ (rows.get j).1
  /-- Once a row with a fixed threshold deletes the diagonal term, later rows
  with the same threshold also delete it. -/
  compat : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 = (rows.get j).1 →
    (rows.get i).2 = 0 → (rows.get j).2 = 0

lemma RowData.alpha_nonneg {rows : List (ℕ × ℝ[X])} (h : RowData rows) :
    ∀ p ∈ rows, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases h.alpha_mem p hp with hα | hα <;> rw [hα]
  · exact hasNonnegCoeffs_zero
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one

/-! ### Paper-shaped row-choice wrapper -/

/-- Boolean encoding of the two Gustafsson--Solus row choices.

`false` means the row is `g_i`; `true` means the diagonal term is deleted, so
the row is `g_i - f_{phi i}`. -/
def choiceMarker (delete : Bool) : ℝ[X] :=
  if delete then 0 else 1

@[simp] lemma choiceMarker_false :
    choiceMarker false = (1 : ℝ[X]) := rfl

@[simp] lemma choiceMarker_true :
    choiceMarker true = (0 : ℝ[X]) := rfl

@[simp] lemma choiceMarker_eq_zero {delete : Bool} :
    choiceMarker delete = (0 : ℝ[X]) ↔ delete = true := by
  cases delete <;> simp

/-- Gustafsson--Solus row data using a threshold and a Boolean deletion flag. -/
def choiceRows (choices : List (ℕ × Bool)) : List (ℕ × ℝ[X]) :=
  choices.map (fun p => (p.1, choiceMarker p.2))

/-- Matrix associated to Gustafsson--Solus threshold choices. -/
abbrev choiceMatrix (q : ℕ) (choices : List (ℕ × Bool)) : List (List ℝ[X]) :=
  thresholdMatrix q (choiceRows choices)

@[simp] lemma length_choiceRows (choices : List (ℕ × Bool)) :
    (choiceRows choices).length = choices.length := by
  simp [choiceRows]

@[simp] lemma length_choiceMatrix (q : ℕ) (choices : List (ℕ × Bool)) :
    (choiceMatrix q choices).length = choices.length := by
  simp [choiceMatrix]

lemma choiceRows_rowData {choices : List (ℕ × Bool)}
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true) :
    RowData (choiceRows choices) := by
  constructor
  · intro p hp
    simp only [choiceRows, List.mem_map] at hp
    obtain ⟨p, _, rfl⟩ := hp
    cases p.2 <;> simp [choiceMarker]
  · intro i j hij
    dsimp only [choiceRows] at i j ⊢
    let i' : Fin choices.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin choices.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have hkey := hmono i' j' hij'
    simpa [choiceRows, List.get_eq_getElem, i', j'] using hkey
  · intro i j hij heq hdel
    dsimp only [choiceRows] at i j heq hdel ⊢
    let i' : Fin choices.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin choices.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have heq' : (choices.get i').1 = (choices.get j').1 := by
      simpa [choiceRows, List.get_eq_getElem, i', j'] using heq
    have hdel_marker : choiceMarker (choices.get i').2 = 0 := by
      simpa [choiceRows, List.get_eq_getElem, i'] using hdel
    have hdel' : (choices.get i').2 = true := by simpa using hdel_marker
    have hdelj := hdelete i' j' hij' heq' hdel'
    simpa [choiceRows, List.get_eq_getElem, j', hdelj]

lemma delete_eq_true_of_local {choices : List (ℕ × Bool)}
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true) :
    ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true := by
  intro i j hij heq hdel
  have hconst : ∀ k (hik : i.1 ≤ k) (hkj : k ≤ j.1),
      (choices.get ⟨k, Nat.lt_of_le_of_lt hkj j.2⟩).1 =
        (choices.get i).1 := by
    intro k hik hkj
    let k' : Fin choices.length := ⟨k, Nat.lt_of_le_of_lt hkj j.2⟩
    have hik' : i ≤ k' := hik
    have hkj' : k' ≤ j := hkj
    have hle1 : (choices.get i).1 ≤ (choices.get k').1 := hmono i k' hik'
    have hle2 : (choices.get k').1 ≤ (choices.get i).1 := by
      have hkj_le : (choices.get k').1 ≤ (choices.get j).1 := hmono k' j hkj'
      rw [← heq] at hkj_le
      exact hkj_le
    exact le_antisymm hle2 hle1
  have hmain := Nat.le_induction (m := i.1)
    (P := fun n _ => ∀ hnj : n ≤ j.1,
      (choices.get ⟨n, Nat.lt_of_le_of_lt hnj j.2⟩).2 = true)
    (by
      intro _
      simpa using hdel)
    (by
      intro n hin ih hsuccj
      have hnle : n ≤ j.1 := Nat.le_of_succ_le hsuccj
      have hsucc_len : n + 1 < choices.length := Nat.lt_of_le_of_lt hsuccj j.2
      have hdeln : (choices.get ⟨n, Nat.lt_of_le_of_lt hnle j.2⟩).2 = true :=
        ih hnle
      have heq_step :
          (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hsucc_len⟩).1 =
            (choices.get ⟨n + 1, hsucc_len⟩).1 := by
        have hn_eq := hconst n hin hnle
        have hisucc : i.1 ≤ n + 1 := Nat.le_trans hin (Nat.le_succ n)
        have hsucc_eq := hconst (n + 1) hisucc hsuccj
        simpa using hn_eq.trans hsucc_eq.symm
      have hdeln' :
          (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hsucc_len⟩).2 =
            true := by
        simpa using hdeln
      exact hlocal n hsucc_len heq_step hdeln')
    j.1 hij
  simpa using hmain le_rfl

/-- The finite entrywise Gustafsson--Solus `2 x 2` threshold check. -/
theorem has2x2InterlacingProperty0_thresholdEntry {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 0 ∨ α₁ = 1) (hα₂ : α₂ = 0 ∨ α₂ = 1)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂) (hcompat : t₁ = t₂ → α₁ = 0 → α₂ = 0) :
    Has2x2InterlacingProperty0
      (thresholdEntry t₁ α₁ j₁) (thresholdEntry t₁ α₁ j₂)
      (thresholdEntry t₂ α₂ j₁) (thresholdEntry t₂ α₂ j₂) :=
  (gsEntry_shape hα₁ hα₂ ht hj hcompat).has2x2

lemma RowData.entry_has2x2 {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hrows : RowData rows) :
    ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1) := by
  intro i₁ i₂ j₁ j₂ hi hj
  exact has2x2InterlacingProperty0_thresholdEntry
    (hrows.alpha_mem (rows.get i₁) (List.get_mem rows i₁))
    (hrows.alpha_mem (rows.get i₂) (List.get_mem rows i₂))
    (hrows.thresh_mono i₁ i₂ hi)
    hj
    (hrows.compat i₁ i₂ hi)

/-- Gustafsson--Solus threshold recursion: threshold matrices preserve
nonnegative interlacing sequences. -/
theorem isInterlacingSeq0Nonneg_matPolyAction
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : RowData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry rows
    hrows.alpha_nonneg hrows.entry_has2x2 fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : RowData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (thresholdMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry_weak rows
    hrows.alpha_nonneg hrows.entry_has2x2 fs hfs_len hfs hfs_real

theorem isInterlacingSeq0Nonneg_choiceMatrix
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (choiceMatrix q choices) fs) :=
  isInterlacingSeq0Nonneg_matPolyAction (choiceRows choices)
    (choiceRows_rowData hmono hdelete) fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (choiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (choiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_matPolyAction_and_realRooted (choiceRows choices)
    (choiceRows_rowData hmono hdelete) fs hfs_len hfs hfs_real

theorem isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted_of_interlacing
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (choiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (choiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  have hfs_weak := weakData_of_isInterlacingSeqNonneg hfs
  exact isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted
    choices hmono hdelete fs hfs_len hfs_weak.1 hfs_weak.2

theorem isInterlacingSeq0Nonneg_choiceMatrix_of_local
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (choiceMatrix q choices) fs) :=
  isInterlacingSeq0Nonneg_choiceMatrix choices hmono
    (delete_eq_true_of_local hmono hlocal) fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted_of_local
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (choiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (choiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted choices hmono
    (delete_eq_true_of_local hmono hlocal) fs hfs_len hfs hfs_real

theorem isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted_of_local_of_interlacing
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (choiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (choiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted_of_interlacing choices hmono
    (delete_eq_true_of_local hmono hlocal) fs hfs_len hfs

/-- Paper-shaped finite-indexed Gustafsson--Solus row choices.

For `i : Fin (m + 1)`, `phi i` is the row threshold and `delete i` chooses
between `g_i` and `g_i - f_{phi i}`. -/
def finChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) : List (ℕ × Bool) :=
  List.ofFn fun i => (phi i, delete i)

/-- The Gustafsson--Solus row polynomial attached to a single threshold and
row choice.  The Boolean convention is that `false` gives the row `g_i`, while
`true` gives the row `g_i - f_{phi i}`. -/
def rowPolynomial (q t : ℕ) (delete : Bool) (fs : List ℝ[X]) : ℝ[X] :=
  ((thresholdRow q t (choiceMarker delete)).zipWith (· * ·) fs).sum

/-- The paper-shaped list of Gustafsson--Solus row polynomials. -/
def rowPolynomials (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) : List ℝ[X] :=
  List.ofFn fun i => rowPolynomial q (phi i) (delete i) fs

@[simp] lemma length_finChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) :
    (finChoices m phi delete).length = m + 1 := by
  simp [finChoices]

@[simp] lemma length_rowPolynomials (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) :
    (rowPolynomials q m phi delete fs).length = m + 1 := by
  simp [rowPolynomials]

lemma get_finChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool)
    (i : Fin (finChoices m phi delete).length) :
    (finChoices m phi delete).get i =
      (phi (Fin.cast (length_finChoices m phi delete) i),
        delete (Fin.cast (length_finChoices m phi delete) i)) := by
  simpa [finChoices] using
    (List.get_ofFn (fun i : Fin (m + 1) => (phi i, delete i)) i)

@[simp] lemma matPolyAction_choiceMatrix_finChoices
    (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) :
  matPolyAction (choiceMatrix q (finChoices m phi delete)) fs =
      rowPolynomials q m phi delete fs := by
  simp [choiceMatrix, choiceRows, finChoices, rowPolynomials,
    rowPolynomial, thresholdMatrix, matPolyAction, Function.comp_def]

private lemma fin_mono_of_adjacent {m : ℕ} {phi : Fin (m + 1) → ℕ}
    (hstep : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ) :
    ∀ i j : Fin (m + 1), i ≤ j → phi i ≤ phi j := by
  intro i j hij
  have hmain := Nat.le_induction (m := i.1)
    (P := fun n _ => ∀ hn : n < m + 1, phi i ≤ phi ⟨n, hn⟩)
    (by
      intro hn
      have hidx : (⟨i.1, hn⟩ : Fin (m + 1)) = i := by ext; rfl
      simp [hidx])
    (by
      intro n hin ih hsucc
      have hn : n < m + 1 := Nat.lt_of_succ_lt hsucc
      have hn_m : n < m := by lia
      have hle := ih hn
      have hstepn := hstep ⟨n, hn_m⟩
      have hleft : (⟨n, hn_m⟩ : Fin m).castSucc =
          (⟨n, hn⟩ : Fin (m + 1)) := by
        ext
        rfl
      have hright : (⟨n, hn_m⟩ : Fin m).succ =
          (⟨n + 1, hsucc⟩ : Fin (m + 1)) := by
        ext
        rfl
      rw [hleft, hright] at hstepn
      exact le_trans hle hstepn)
    j.1 hij
  exact hmain j.2

private lemma finChoices_mono_of_adjacent {m : ℕ}
    {phi : Fin (m + 1) → ℕ} {delete : Fin (m + 1) → Bool}
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ) :
    ∀ i j : Fin (finChoices m phi delete).length, i ≤ j →
      ((finChoices m phi delete).get i).1 ≤
        ((finChoices m phi delete).get j).1 := by
  intro i j hij
  have hi := get_finChoices m phi delete i
  have hj := get_finChoices m phi delete j
  let i' : Fin (m + 1) := Fin.cast (length_finChoices m phi delete) i
  let j' : Fin (m + 1) := Fin.cast (length_finChoices m phi delete) j
  have hij' : i' ≤ j' := hij
  have hmonoFin : phi i' ≤ phi j' :=
    fin_mono_of_adjacent hphi i' j' hij'
  calc
    ((finChoices m phi delete).get i).1 = phi i' := by rw [hi]
    _ ≤ phi j' := hmonoFin
    _ = ((finChoices m phi delete).get j).1 := by rw [hj]

private lemma finChoices_local_of_fin {m : ℕ}
    {phi : Fin (m + 1) → ℕ} {delete : Fin (m + 1) → Bool}
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true) :
    ∀ n (hn : n + 1 < (finChoices m phi delete).length),
      ((finChoices m phi delete).get
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        ((finChoices m phi delete).get ⟨n + 1, hn⟩).1 →
      ((finChoices m phi delete).get
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      ((finChoices m phi delete).get ⟨n + 1, hn⟩).2 = true := by
  intro n hn heq hdel
  have hn_m : n < m := by simpa [length_finChoices] using hn
  let i : Fin m := ⟨n, hn_m⟩
  have hleft : (i.castSucc : Fin (m + 1)) =
      Fin.cast (length_finChoices m phi delete)
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩ := by
    ext
    rfl
  have hright : (i.succ : Fin (m + 1)) =
      Fin.cast (length_finChoices m phi delete) ⟨n + 1, hn⟩ := by
    ext
    rfl
  have hget_left := get_finChoices m phi delete
    ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩
  have hget_right := get_finChoices m phi delete ⟨n + 1, hn⟩
  have heq' : phi i.castSucc = phi i.succ := by
    rw [hget_left, hget_right] at heq
    rwa [hleft, hright]
  have hdel' : delete i.castSucc = true := by
    rw [hget_left] at hdel
    rwa [hleft]
  have hnext := hlocal i heq' hdel'
  rw [hget_right]
  rwa [hright] at hnext

/-- Gustafsson--Solus Lemma 3.4 in finite-indexed row-choice form.

The function `delete` uses the same convention as `choiceMarker`: `false`
selects the row `g_i`, and `true` selects `g_i - f_{phi i}`. -/
theorem isInterlacingSeq0Nonneg_choiceMatrix_finChoices
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (choiceMatrix q (finChoices m phi delete)) fs) :=
  isInterlacingSeq0Nonneg_choiceMatrix_of_local (finChoices m phi delete)
    (finChoices_mono_of_adjacent hphi)
    (finChoices_local_of_fin hlocal) fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_choiceMatrix_finChoices_and_realRooted
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (choiceMatrix q (finChoices m phi delete)) fs) ∧
      ∀ f ∈ matPolyAction (choiceMatrix q (finChoices m phi delete)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted_of_local
    (finChoices m phi delete)
    (finChoices_mono_of_adjacent hphi)
    (finChoices_local_of_fin hlocal) fs hfs_len hfs hfs_real

theorem isInterlacingSeq0Nonneg_choiceMatrix_finChoices_and_realRooted_of_interlacing
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (choiceMatrix q (finChoices m phi delete)) fs) ∧
      ∀ f ∈ matPolyAction (choiceMatrix q (finChoices m phi delete)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_choiceMatrix_and_realRooted_of_local_of_interlacing
    (finChoices m phi delete)
    (finChoices_mono_of_adjacent hphi)
    (finChoices_local_of_fin hlocal) fs hfs_len hfs

/-- Real-rootedness projection of the finite-indexed Gustafsson--Solus
row-choice form. -/
theorem realRooted_of_mem_choiceMatrix_finChoices
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ matPolyAction (choiceMatrix q (finChoices m phi delete)) fs,
      f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  (isInterlacingSeq0Nonneg_choiceMatrix_finChoices_and_realRooted_of_interlacing
    phi delete hphi hlocal fs hfs_len hfs).2

theorem isInterlacingSeq0Nonneg_rowPolynomials_and_realRooted
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (rowPolynomials q m phi delete fs) ∧
      ∀ f ∈ rowPolynomials q m phi delete fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simpa using
    isInterlacingSeq0Nonneg_choiceMatrix_finChoices_and_realRooted
      phi delete hphi hlocal fs hfs_len hfs hfs_real

theorem isInterlacingSeq0Nonneg_rowPolynomials_and_realRooted_of_interlacing
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (rowPolynomials q m phi delete fs) ∧
      ∀ f ∈ rowPolynomials q m phi delete fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simpa using
    isInterlacingSeq0Nonneg_choiceMatrix_finChoices_and_realRooted_of_interlacing
      phi delete hphi hlocal fs hfs_len hfs

/-- Interlacing projection of the paper-shaped Gustafsson--Solus polynomial-list
recursion. -/
theorem isInterlacingSeq0Nonneg_rowPolynomials
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (rowPolynomials q m phi delete fs) :=
  by
    simpa using
      GustafssonSolus.isInterlacingSeq0Nonneg_choiceMatrix_finChoices
        phi delete hphi hlocal fs hfs_len hfs

/-- Real-rootedness projection of the paper-shaped Gustafsson--Solus
polynomial-list recursion. -/
theorem realRooted_of_mem_rowPolynomials
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ rowPolynomials q m phi delete fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  by
    simpa using
      realRooted_of_mem_choiceMatrix_finChoices
        phi delete hphi hlocal fs hfs_len hfs

end GustafssonSolus

end RealRooted
