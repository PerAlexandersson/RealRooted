import RealRooted.ThresholdMatrix.Basic

/-!
# Gustafsson--Solus threshold recursion

The `0`/`1` threshold-entry classification and the finite-indexed and
paper-shaped forms of Gustafsson--Solus Lemma 3.4.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Gustafsson--Solus Lemma 3.4 backend -/

namespace GustafssonSolus

/-! ### Finite-entry shape helpers -/

private lemma prec0_gs_quadratic_self {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t) * X + X) ((C s * X + C t) * X + X) :=
  prec0_refl_of_realRooted (isRealRooted_affine_mul_X_add_X hs)

private lemma prec0_gs_X_quadratic {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 X ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  simpa using
    prec0_affine_to_X_mul_affine
      (u := s) (v := t + 1) (U := 1) (V := 0)
      hs zero_lt_one (by nlinarith) (by positivity) le_rfl

private lemma prec0_gs_affine_add_X_quadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_to_X_mul_affine
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [hs, ht]) (by positivity) ht.le

private lemma prec0_gs_affine_quadratic {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  exact
    prec0_affine_to_X_mul_affine
      (u := s) (v := t + 1) (U := s) (V := t)
      hs hs (by nlinarith [hs]) (by positivity) ht.le

private lemma prec0_gs_affine_add_one_quadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact
    prec0_affine_to_X_mul_affine
      (u := s) (v := t + 1) (U := s) (V := t + 1)
      hs hs le_rfl (by nlinarith) (by nlinarith)

private lemma prec0_gs_affine_add_X_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) X := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  simpa using
    prec0_affine_linear_affine_linear_of_cross
      (u := s + 1) (v := t) (U := 1) (V := 0)
      (by positivity) zero_lt_one (by nlinarith [ht])

private lemma prec0_gs_affine_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) X := by
  simpa using
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t) (U := 1) (V := 0)
      hs zero_lt_one (by nlinarith [ht])

private lemma prec0_gs_affine_add_one_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) X := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  simpa using
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := 1) (V := 0)
      hs zero_lt_one (by nlinarith [ht])

private lemma prec0_gs_affine_add_X_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + X) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_refl_of_realRooted
      (isRealRooted_affine_factor (s := s + 1) (t := t) (by positivity))

private lemma prec0_gs_affine_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t) (C s * X + C t) :=
  prec0_refl_of_realRooted (isRealRooted_affine_factor (s := s) (t := t) hs)

private lemma prec0_gs_affine_add_one_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + 1) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact
    prec0_refl_of_realRooted
      (isRealRooted_affine_factor (s := s) (t := t + 1) hs)

private lemma prec0_gs_X_X : Prec0 (X : ℝ[X]) X :=
  prec0_refl_of_realRooted isRealRooted_X

private lemma prec0_gs_one_one : Prec0 (1 : ℝ[X]) 1 := by
  simpa using prec0_C_C (1 : ℝ) (1 : ℝ)

private lemma prec0_gs_affine_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [ht])

private lemma prec0_gs_affine_add_one_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + X) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [hs, ht])

private lemma prec0_gs_affine_add_one_affine {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) (C s * X + C t) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s) (V := t)
      hs hs (by nlinarith [hs])

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
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
  · simpa using prec0_zero_zero
  · simpa using prec0_gs_X_X
  · simpa using (prec0_zero_right (C s * X + C t + 1 : ℝ[X]))
  · simpa using prec0_gs_affine_X hs ht
  · simpa using prec0_gs_affine_add_one_X hs ht
  · simpa using prec0_gs_affine_add_X_X hs ht
  · simpa using prec0_gs_affine_self hs
  · simpa using prec0_gs_affine_add_one_affine hs
  · simpa using prec0_gs_affine_add_one_self hs
  · simpa using prec0_gs_affine_affine_add_X hs ht
  · simpa using prec0_gs_affine_add_one_affine_add_X hs ht
  · simpa using prec0_gs_affine_add_X_self hs
  · simpa using (prec0_zero_left (((C s * X + C t) * X + X : ℝ[X])))
  · simpa using prec0_gs_X_quadratic hs ht
  · simpa using prec0_gs_affine_quadratic hs ht
  · simpa using prec0_gs_affine_add_one_quadratic hs ht
  · simpa using prec0_gs_affine_add_X_quadratic hs ht
  · simpa using prec0_gs_quadratic_self hs

private lemma gsEntry_shape
    {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 0 ∨ α₁ = 1)
    (hα₂ : α₂ = 0 ∨ α₂ = 1)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 0 → α₂ = 0) :
    GS2x2EntryShape
      (thresholdEntry t₁ α₁ j₁) (thresholdEntry t₁ α₁ j₂)
      (thresholdEntry t₂ α₂ j₁) (thresholdEntry t₂ α₂ j₂) := by
  rcases hα₁ with rfl | rfl <;> rcases hα₂ with rfl | rfl
  all_goals
    simp at hcompat
    unfold GS2x2EntryShape Threshold2x2EntryTuple
    simp only [thresholdEntry]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    all_goals try lia

/-- Validity data for the Gustafsson--Solus recursion rows.

The marker `1` encodes the row `g_i`, while marker `0` encodes
`g_i - f_{phi i}`.  The compatibility condition is the global form of the
paper's no-immediate-switch condition within an equal-threshold block. -/
structure GSData (rows : List (ℕ × ℝ[X])) : Prop where
  /-- Every diagonal marker is `0` or `1`. -/
  alpha_mem : ∀ p ∈ rows, p.2 = 0 ∨ p.2 = 1
  /-- Thresholds are nondecreasing down the rows. -/
  thresh_mono : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 ≤ (rows.get j).1
  /-- Once a row with a fixed threshold deletes the diagonal term, later rows
  with the same threshold also delete it. -/
  compat : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 = (rows.get j).1 →
    (rows.get i).2 = 0 → (rows.get j).2 = 0

lemma GSData.alpha_nonneg {rows : List (ℕ × ℝ[X])} (h : GSData rows) :
    ∀ p ∈ rows, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases h.alpha_mem p hp with hα | hα <;> rw [hα]
  · exact hasNonnegCoeffs_zero
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one

/-! ### Paper-shaped row-choice wrapper -/

/-- Boolean encoding of the two Gustafsson--Solus row choices.

`false` means the row is `g_i`; `true` means the diagonal term is deleted, so
the row is `g_i - f_{phi i}`. -/
def gsChoiceMarker (delete : Bool) : ℝ[X] :=
  if delete then 0 else 1

@[simp] lemma gsChoiceMarker_false :
    gsChoiceMarker false = (1 : ℝ[X]) := rfl

@[simp] lemma gsChoiceMarker_true :
    gsChoiceMarker true = (0 : ℝ[X]) := rfl

@[simp] lemma gsChoiceMarker_eq_zero {delete : Bool} :
    gsChoiceMarker delete = (0 : ℝ[X]) ↔ delete = true := by
  cases delete <;> simp

/-- Gustafsson--Solus row data using a threshold and a Boolean deletion flag. -/
def gsChoiceRows (choices : List (ℕ × Bool)) : List (ℕ × ℝ[X]) :=
  choices.map (fun p => (p.1, gsChoiceMarker p.2))

/-- Matrix associated to Gustafsson--Solus threshold choices. -/
abbrev gsChoiceMatrix (q : ℕ) (choices : List (ℕ × Bool)) : List (List ℝ[X]) :=
  thresholdMatrix q (gsChoiceRows choices)

@[simp] lemma length_gsChoiceRows (choices : List (ℕ × Bool)) :
    (gsChoiceRows choices).length = choices.length := by
  simp [gsChoiceRows]

@[simp] lemma length_gsChoiceMatrix (q : ℕ) (choices : List (ℕ × Bool)) :
    (gsChoiceMatrix q choices).length = choices.length := by
  simp [gsChoiceMatrix]

lemma gsChoiceRows_data {choices : List (ℕ × Bool)}
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true) :
    GSData (gsChoiceRows choices) := by
  constructor
  · intro p hp
    simp only [gsChoiceRows, List.mem_map] at hp
    obtain ⟨p, _, rfl⟩ := hp
    cases p.2 <;> simp [gsChoiceMarker]
  · intro i j hij
    let i' : Fin choices.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin choices.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have hkey := hmono i' j' hij'
    simpa [gsChoiceRows, List.get_eq_getElem, i', j'] using hkey
  · intro i j hij heq hdel
    let i' : Fin choices.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin choices.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have heq' : (choices.get i').1 = (choices.get j').1 := by
      simpa [gsChoiceRows, List.get_eq_getElem, i', j'] using heq
    have hdel_marker : gsChoiceMarker (choices.get i').2 = 0 := by
      simpa [gsChoiceRows, List.get_eq_getElem, i'] using hdel
    have hdel' : (choices.get i').2 = true := by simpa using hdel_marker
    have hdelj := hdelete i' j' hij' heq' hdel'
    simpa [gsChoiceRows, List.get_eq_getElem, j', hdelj]

lemma gsChoice_delete_global_of_local {choices : List (ℕ × Bool)}
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
def GSEntryHas2x2Statement : Prop :=
  ∀ {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]},
    (α₁ = 0 ∨ α₁ = 1) →
    (α₂ = 0 ∨ α₂ = 1) →
    t₁ ≤ t₂ → j₁ ≤ j₂ →
    (t₁ = t₂ → α₁ = 0 → α₂ = 0) →
    Has2x2InterlacingProperty0
      (thresholdEntry t₁ α₁ j₁) (thresholdEntry t₁ α₁ j₂)
      (thresholdEntry t₂ α₂ j₁) (thresholdEntry t₂ α₂ j₂)

theorem gsEntry_has2x2 : GSEntryHas2x2Statement := by
  intro t₁ t₂ j₁ j₂ α₁ α₂ hα₁ hα₂ ht hj hcompat
  exact (gsEntry_shape hα₁ hα₂ ht hj hcompat).has2x2

lemma GSData.entry_has2x2 {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hrows : GSData rows) (hentry : GSEntryHas2x2Statement) :
    ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1) := by
  intro i₁ i₂ j₁ j₂ hi hj
  exact hentry
    (hrows.alpha_mem (rows.get i₁) (List.get_mem rows i₁))
    (hrows.alpha_mem (rows.get i₂) (List.get_mem rows i₂))
    (hrows.thresh_mono i₁ i₂ hi)
    hj
    (hrows.compat i₁ i₂ hi)

/-- Gustafsson--Solus threshold-recursion backend, reduced to the finite
entrywise `2 x 2` threshold check. -/
theorem gustafsson_solus_interlacing_recursion_backend
    (hentry : GSEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) :=
  gustafsson_solus_interlacing_recursion_backend gsEntry_has2x2
    rows hrows fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_backend_weak
    (hentry : GSEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (thresholdMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry_weak rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_weak
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (thresholdMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_backend_weak gsEntry_has2x2
    rows hrows fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_choices
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) :=
  gustafsson_solus_interlacing_recursion (gsChoiceRows choices)
    (gsChoiceRows_data hmono hdelete) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_choices_weak
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_weak (gsChoiceRows choices)
    (gsChoiceRows_data hmono hdelete) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_choices_weak_of_interlacing
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  have hfs_weak := weakData_of_isInterlacingSeqNonneg hfs
  exact gustafsson_solus_interlacing_recursion_choices_weak
    choices hmono hdelete fs hfs_len hfs_weak.1 hfs_weak.2

theorem gustafsson_solus_interlacing_recursion_local_choices
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) :=
  gustafsson_solus_interlacing_recursion_choices choices hmono
    (gsChoice_delete_global_of_local hmono hlocal) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_local_choices_weak
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
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_choices_weak choices hmono
    (gsChoice_delete_global_of_local hmono hlocal) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_local_choices_weak_of_interlacing
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_choices_weak_of_interlacing choices hmono
    (gsChoice_delete_global_of_local hmono hlocal) fs hfs_len hfs

/-- Paper-shaped finite-indexed Gustafsson--Solus row choices.

For `i : Fin (m + 1)`, `phi i` is the row threshold and `delete i` chooses
between `g_i` and `g_i - f_{phi i}`. -/
def gsPaperChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) : List (ℕ × Bool) :=
  List.ofFn fun i => (phi i, delete i)

/-- The Gustafsson--Solus row polynomial attached to a single threshold and
row choice.  The Boolean convention is that `false` gives the row `g_i`, while
`true` gives the row `g_i - f_{phi i}`. -/
def gsRowPolynomial (q t : ℕ) (delete : Bool) (fs : List ℝ[X]) : ℝ[X] :=
  ((thresholdRow q t (gsChoiceMarker delete)).zipWith (· * ·) fs).sum

/-- The paper-shaped list of Gustafsson--Solus row polynomials. -/
def gsPaperPolynomials (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) : List ℝ[X] :=
  List.ofFn fun i => gsRowPolynomial q (phi i) (delete i) fs

@[simp] lemma length_gsPaperChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) :
    (gsPaperChoices m phi delete).length = m + 1 := by
  simp [gsPaperChoices]

@[simp] lemma length_gsPaperPolynomials (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) :
    (gsPaperPolynomials q m phi delete fs).length = m + 1 := by
  simp [gsPaperPolynomials]

lemma get_gsPaperChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool)
    (i : Fin (gsPaperChoices m phi delete).length) :
    (gsPaperChoices m phi delete).get i =
      (phi (Fin.cast (length_gsPaperChoices m phi delete) i),
        delete (Fin.cast (length_gsPaperChoices m phi delete) i)) := by
  simpa [gsPaperChoices] using
    (List.get_ofFn (fun i : Fin (m + 1) => (phi i, delete i)) i)

@[simp] lemma matPolyAction_gsChoiceMatrix_gsPaperChoices
    (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) :
  matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs =
      gsPaperPolynomials q m phi delete fs := by
  simp [gsChoiceMatrix, gsChoiceRows, gsPaperChoices, gsPaperPolynomials,
    gsRowPolynomial, thresholdMatrix, matPolyAction, Function.comp_def]

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

private lemma gsPaperChoices_mono_of_adjacent {m : ℕ}
    {phi : Fin (m + 1) → ℕ} {delete : Fin (m + 1) → Bool}
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ) :
    ∀ i j : Fin (gsPaperChoices m phi delete).length, i ≤ j →
      ((gsPaperChoices m phi delete).get i).1 ≤
        ((gsPaperChoices m phi delete).get j).1 := by
  intro i j hij
  have hi := get_gsPaperChoices m phi delete i
  have hj := get_gsPaperChoices m phi delete j
  let i' : Fin (m + 1) := Fin.cast (length_gsPaperChoices m phi delete) i
  let j' : Fin (m + 1) := Fin.cast (length_gsPaperChoices m phi delete) j
  have hij' : i' ≤ j' := hij
  have hmonoFin : phi i' ≤ phi j' :=
    fin_mono_of_adjacent hphi i' j' hij'
  calc
    ((gsPaperChoices m phi delete).get i).1 = phi i' := by rw [hi]
    _ ≤ phi j' := hmonoFin
    _ = ((gsPaperChoices m phi delete).get j).1 := by rw [hj]

private lemma gsPaperChoices_local_of_fin {m : ℕ}
    {phi : Fin (m + 1) → ℕ} {delete : Fin (m + 1) → Bool}
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true) :
    ∀ n (hn : n + 1 < (gsPaperChoices m phi delete).length),
      ((gsPaperChoices m phi delete).get
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        ((gsPaperChoices m phi delete).get ⟨n + 1, hn⟩).1 →
      ((gsPaperChoices m phi delete).get
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      ((gsPaperChoices m phi delete).get ⟨n + 1, hn⟩).2 = true := by
  intro n hn heq hdel
  have hn_m : n < m := by simpa [length_gsPaperChoices] using hn
  let i : Fin m := ⟨n, hn_m⟩
  have hleft : (i.castSucc : Fin (m + 1)) =
      Fin.cast (length_gsPaperChoices m phi delete)
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩ := by
    ext
    rfl
  have hright : (i.succ : Fin (m + 1)) =
      Fin.cast (length_gsPaperChoices m phi delete) ⟨n + 1, hn⟩ := by
    ext
    rfl
  have hget_left := get_gsPaperChoices m phi delete
    ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩
  have hget_right := get_gsPaperChoices m phi delete ⟨n + 1, hn⟩
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

The function `delete` uses the same convention as `gsChoiceMarker`: `false`
selects the row `g_i`, and `true` selects `g_i - f_{phi i}`. -/
theorem gustafsson_solus_interlacing_recursion_fin_choices
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) :=
  gustafsson_solus_interlacing_recursion_local_choices (gsPaperChoices m phi delete)
    (gsPaperChoices_mono_of_adjacent hphi)
    (gsPaperChoices_local_of_fin hlocal) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_fin_choices_weak
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_local_choices_weak
    (gsPaperChoices m phi delete)
    (gsPaperChoices_mono_of_adjacent hphi)
    (gsPaperChoices_local_of_fin hlocal) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_local_choices_weak_of_interlacing
    (gsPaperChoices m phi delete)
    (gsPaperChoices_mono_of_adjacent hphi)
    (gsPaperChoices_local_of_fin hlocal) fs hfs_len hfs

/-- Interlacing projection of the finite-indexed Gustafsson--Solus row-choice
form. -/
theorem gustafsson_solus_interlacing_recursion_fin_choices_interlaces
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) :=
  (gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
    phi delete hphi hlocal fs hfs_len hfs).1

/-- Real-rootedness projection of the finite-indexed Gustafsson--Solus
row-choice form. -/
theorem gustafsson_solus_interlacing_recursion_fin_choices_realRooted
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs,
      f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  (gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
    phi delete hphi hlocal fs hfs_len hfs).2

theorem gustafsson_solus_interlacing_recursion_fin_polynomials_weak
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) ∧
      ∀ f ∈ gsPaperPolynomials q m phi delete fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simpa using
    gustafsson_solus_interlacing_recursion_fin_choices_weak
      phi delete hphi hlocal fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_fin_polynomials_weak_of_interlacing
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) ∧
      ∀ f ∈ gsPaperPolynomials q m phi delete fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simpa using
    gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
      phi delete hphi hlocal fs hfs_len hfs

/-- Interlacing projection of the paper-shaped Gustafsson--Solus polynomial-list
recursion. -/
theorem gustafsson_solus_interlacing_recursion_fin_polynomials_interlaces
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) :=
  by
    simpa using
      gustafsson_solus_interlacing_recursion_fin_choices_interlaces
        phi delete hphi hlocal fs hfs_len hfs

/-- Gustafsson--Solus Lemma 3.4 in paper-shaped finite-indexed polynomial-list
form.  The output list has entries `g_i` or `g_i - f_{phi i}` according to
`delete`. -/
theorem gustafsson_solus_interlacing_recursion_fin_polynomials
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) :=
  gustafsson_solus_interlacing_recursion_fin_polynomials_interlaces
    phi delete hphi hlocal fs hfs_len hfs

/-- Real-rootedness projection of the paper-shaped Gustafsson--Solus
polynomial-list recursion. -/
theorem gustafsson_solus_interlacing_recursion_fin_polynomials_realRooted
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ gsPaperPolynomials q m phi delete fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  by
    simpa using
      gustafsson_solus_interlacing_recursion_fin_choices_realRooted
        phi delete hphi hlocal fs hfs_len hfs

end GustafssonSolus

end RealRooted
