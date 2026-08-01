import RealRooted.ThresholdMatrix

/-!
# Gustafsson--Solus interlacing recursion

This module packages the row-threshold matrix underlying Lemma 3.4 of
N. Gustafsson and L. Solus, *Derangements, Ehrhart Theory, and Local
h-polynomials*, arXiv:1807.05246v2.

For a threshold `phi i`, a row has entry `X` in columns `j < phi i`, entry `1`
in columns `j >= phi i`, and optionally deletes the pivot entry `j = phi i`.
Thus multiplying the row against a sequence `(f_j)` gives

`X * sum_{j < phi i} f_j + sum_{j >= phi i} f_j`

or the same expression with `f_{phi i}` removed.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## The row-threshold matrix -/

/-- One entry in the Gustafsson--Solus recursion matrix. -/
def gustafssonSolusEntry {n : ℕ} (phi : Fin n) (dropPivot : Bool)
    (j : Fin n) : ℝ[X] :=
  if j < phi then X else if dropPivot ∧ j = phi then 0 else 1

/-- One row in the Gustafsson--Solus recursion matrix. -/
def gustafssonSolusRow {n : ℕ} (phi : Fin n) (dropPivot : Bool) : List ℝ[X] :=
  List.ofFn fun j : Fin n => gustafssonSolusEntry phi dropPivot j

/-- The Gustafsson--Solus recursion matrix attached to a threshold map and
pivot-deletion choices. -/
def gustafssonSolusMatrix {m n : ℕ} (phi : Fin m → Fin n)
    (dropPivot : Fin m → Bool) : List (List ℝ[X]) :=
  List.ofFn fun i : Fin m => gustafssonSolusRow (phi i) (dropPivot i)

/-- Matrix-action form of the Gustafsson--Solus recursion. -/
def gustafssonSolusAction {m n : ℕ} (phi : Fin m → Fin n)
    (dropPivot : Fin m → Bool) (fs : List ℝ[X]) : List ℝ[X] :=
  matPolyAction (gustafssonSolusMatrix phi dropPivot) fs

@[simp] theorem length_gustafssonSolusRow {n : ℕ} (phi : Fin n) (dropPivot : Bool) :
    (gustafssonSolusRow phi dropPivot).length = n := by
  simp [gustafssonSolusRow]

@[simp] theorem get_gustafssonSolusRow {n : ℕ} (phi : Fin n) (dropPivot : Bool)
    (j : Fin n) :
    (gustafssonSolusRow phi dropPivot).get
        ⟨j.1, by simp [length_gustafssonSolusRow]⟩ =
      gustafssonSolusEntry phi dropPivot j := by
  simp [gustafssonSolusRow]

@[simp] theorem length_gustafssonSolusMatrix {m n : ℕ}
    (phi : Fin m → Fin n) (dropPivot : Fin m → Bool) :
    (gustafssonSolusMatrix phi dropPivot).length = m := by
  simp [gustafssonSolusMatrix]

@[simp] theorem get_gustafssonSolusMatrix {m n : ℕ}
    (phi : Fin m → Fin n) (dropPivot : Fin m → Bool) (i : Fin m) :
    (gustafssonSolusMatrix phi dropPivot).get
        ⟨i.1, by simp [length_gustafssonSolusMatrix]⟩ =
      gustafssonSolusRow (phi i) (dropPivot i) := by
  simp [gustafssonSolusMatrix]

theorem gustafssonSolusMatrix_rect {m n : ℕ}
    (phi : Fin m → Fin n) (dropPivot : Fin m → Bool) :
    ∀ row ∈ gustafssonSolusMatrix phi dropPivot, row.length = n := by
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hrow
  simp [gustafssonSolusMatrix, gustafssonSolusRow]

theorem isNonnegLinearForm_gustafssonSolusEntry {n : ℕ}
    (phi : Fin n) (dropPivot : Bool) (j : Fin n) :
    IsNonnegLinearForm (gustafssonSolusEntry phi dropPivot j) := by
  unfold gustafssonSolusEntry
  split_ifs <;>
    simp [isNonnegLinearForm_X, isNonnegLinearForm_zero, isNonnegLinearForm_one]

/-- Each Gustafsson--Solus row is a row-threshold row with threshold `phi`. -/
theorem hasRowThreshold_gustafssonSolusRow {n : ℕ}
    (phi : Fin n) (dropPivot : Bool) :
    HasRowThreshold (gustafssonSolusRow phi dropPivot) phi.1 := by
  constructor
  · simp [gustafssonSolusRow]
  · intro j
    let j' : Fin n := ⟨j.1, by simpa [length_gustafssonSolusRow] using j.2⟩
    have hget :
        (gustafssonSolusRow phi dropPivot).get j =
          gustafssonSolusEntry phi dropPivot j' := by
      simp [j', gustafssonSolusRow]
    rw [hget]
    refine ⟨isNonnegLinearForm_gustafssonSolusEntry phi dropPivot j', ?_, ?_⟩
    · intro hcoeff
      unfold gustafssonSolusEntry at hcoeff
      split_ifs at hcoeff with hlt hdrop
      · simpa [j'] using (show j'.1 < phi.1 from hlt)
      · rw [Polynomial.coeff_zero] at hcoeff
        exact False.elim ((lt_irrefl (0 : ℝ)) hcoeff)
      · rw [Polynomial.coeff_one] at hcoeff
        simp at hcoeff
    · intro hcoeff
      unfold gustafssonSolusEntry at hcoeff
      split_ifs at hcoeff with hlt hdrop
      · simp at hcoeff
      · rw [Polynomial.coeff_zero] at hcoeff
        exact False.elim ((lt_irrefl (0 : ℝ)) hcoeff)
      · have hnot : ¬ j'.1 < phi.1 := by
          intro hjlt
          exact hlt (show j' < phi from hjlt)
        simpa [j'] using le_of_not_gt hnot

/-- Weak monotonicity of the threshold map, in the zero-based `Fin` indexing
used by the matrix package. -/
def GustafssonSolusWeaklyIncreasing {m n : ℕ} (phi : Fin m → Fin n) : Prop :=
  ∀ ⦃i j : Fin m⦄, i ≤ j → phi i ≤ phi j

/-- The transitive form of the no-immediate-switch condition from
Gustafsson--Solus Lemma 3.4.  This is the condition needed for arbitrary
two-row minors with equal thresholds; the paper's adjacent formulation implies
this under weakly increasing thresholds. -/
def GustafssonSolusNoSwitchAfterDrop {m n : ℕ}
    (phi : Fin m → Fin n) (dropPivot : Fin m → Bool) : Prop :=
  ∀ ⦃i j : Fin m⦄, i ≤ j → phi i = phi j → dropPivot i = true →
    dropPivot j = true

theorem hasRowThresholdLinearStructure_gustafssonSolusMatrix {m n : ℕ}
    {phi : Fin m → Fin n} {dropPivot : Fin m → Bool}
    (hphi : GustafssonSolusWeaklyIncreasing phi) :
    HasRowThresholdLinearStructure (gustafssonSolusMatrix phi dropPivot) := by
  refine ⟨fun i => (phi ⟨i.1, by simpa [gustafssonSolusMatrix] using i.2⟩).1,
    ?_, ?_⟩
  · intro i
    let i' : Fin m := ⟨i.1, by simpa [gustafssonSolusMatrix] using i.2⟩
    have hget :
        (gustafssonSolusMatrix phi dropPivot).get i =
          gustafssonSolusRow (phi i') (dropPivot i') := by
      simp [i', gustafssonSolusMatrix]
    rw [hget]
    exact hasRowThreshold_gustafssonSolusRow (phi i') (dropPivot i')
  · intro i j hij
    let i' : Fin m := ⟨i.1, by simpa [gustafssonSolusMatrix] using i.2⟩
    let j' : Fin m := ⟨j.1, by simpa [gustafssonSolusMatrix] using j.2⟩
    have hij' : i' ≤ j' := by simpa [i', j'] using hij
    simpa [i', j'] using hphi hij'

/-! ## Preservation theorem -/

/-- The finite `2 × 2` affine-minor condition for the concrete
Gustafsson--Solus matrix. -/
def GustafssonSolusHas2x2 {m n : ℕ}
    (phi : Fin m → Fin n) (dropPivot : Fin m → Bool) : Prop :=
  ∀ (i₁ i₂ : Fin (gustafssonSolusMatrix phi dropPivot).length) (j₁ j₂ : Fin n),
    i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (((gustafssonSolusMatrix phi dropPivot).get i₁).get
          ⟨j₁.1, by simp [gustafssonSolusMatrix, gustafssonSolusRow]⟩)
        (((gustafssonSolusMatrix phi dropPivot).get i₁).get
          ⟨j₂.1, by simp [gustafssonSolusMatrix, gustafssonSolusRow]⟩)
        (((gustafssonSolusMatrix phi dropPivot).get i₂).get
          ⟨j₁.1, by simp [gustafssonSolusMatrix, gustafssonSolusRow]⟩)
        (((gustafssonSolusMatrix phi dropPivot).get i₂).get
          ⟨j₂.1, by simp [gustafssonSolusMatrix, gustafssonSolusRow]⟩)

/-- Gustafsson--Solus Lemma 3.4 in matrix-preserver form: once the concrete
finite `2 × 2` affine checks are available, the row-threshold matrix sends a
nonnegative interlacing input sequence to a zero-aware nonnegative interlacing
output sequence. -/
theorem gustafssonSolus_preserves_interlacingSeq0Nonneg_of_2x2 {m n : ℕ}
    {phi : Fin m → Fin n} {dropPivot : Fin m → Bool}
    (hphi : GustafssonSolusWeaklyIncreasing phi)
    (h2x2 : GustafssonSolusHas2x2 phi dropPivot)
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gustafssonSolusAction phi dropPivot fs) := by
  exact
    rowThreshold_matrix_preserves_interlacing_seq0_of_2x2
      (G := gustafssonSolusMatrix phi dropPivot)
      (hG_rect := gustafssonSolusMatrix_rect phi dropPivot)
      (hG_threshold := hasRowThresholdLinearStructure_gustafssonSolusMatrix hphi)
      (hG_affine := h2x2)
      fs hfs_len hfs

/-- Named finite target: the monotone-threshold and no-switch hypotheses from
Gustafsson--Solus Lemma 3.4 should imply the concrete `2 × 2` affine-minor
condition for this matrix. -/
def GustafssonSolus2x2FromNoSwitchStatement : Prop :=
  ∀ {m n : ℕ} (phi : Fin m → Fin n) (dropPivot : Fin m → Bool),
    GustafssonSolusWeaklyIncreasing phi →
    GustafssonSolusNoSwitchAfterDrop phi dropPivot →
      GustafssonSolusHas2x2 phi dropPivot

/-- A concrete Gustafsson--Solus entry is the generic threshold entry with
marker `0` when the pivot is dropped and marker `1` otherwise. -/
theorem gustafssonSolusEntry_eq_thresholdEntry {n : ℕ}
    (phi j : Fin n) (dropPivot : Bool) :
    gustafssonSolusEntry phi dropPivot j =
      thresholdEntry phi.1 (GustafssonSolus.gsChoiceMarker dropPivot) j.1 := by
  unfold gustafssonSolusEntry thresholdEntry GustafssonSolus.gsChoiceMarker
  split_ifs <;> grind

/-- Monotone thresholds and the no-switch condition discharge every concrete
Gustafsson--Solus `2 x 2` affine-minor check. -/
theorem gustafssonSolus2x2_of_noSwitch :
    GustafssonSolus2x2FromNoSwitchStatement := by
  intro m n phi dropPivot hphi hdrop i₁ i₂ j₁ j₂ hi hj
  let i₁' : Fin m := ⟨i₁.1, by simpa [gustafssonSolusMatrix] using i₁.2⟩
  let i₂' : Fin m := ⟨i₂.1, by simpa [gustafssonSolusMatrix] using i₂.2⟩
  have hi' : i₁' ≤ i₂' := by simpa [i₁', i₂'] using hi
  let α₁ := GustafssonSolus.gsChoiceMarker (dropPivot i₁')
  let α₂ := GustafssonSolus.gsChoiceMarker (dropPivot i₂')
  have hα₁ : α₁ = 0 ∨ α₁ = 1 := by
    cases h : dropPivot i₁' <;> simp [α₁, GustafssonSolus.gsChoiceMarker, h]
  have hα₂ : α₂ = 0 ∨ α₂ = 1 := by
    cases h : dropPivot i₂' <;> simp [α₂, GustafssonSolus.gsChoiceMarker, h]
  have ht : (phi i₁').1 ≤ (phi i₂').1 := hphi hi'
  have hcompat : (phi i₁').1 = (phi i₂').1 → α₁ = 0 → α₂ = 0 := by
    intro hphiVal hα₁zero
    have hphiEq : phi i₁' = phi i₂' := Fin.ext hphiVal
    have hdrop₁ : dropPivot i₁' = true := by
      cases h : dropPivot i₁' <;>
        simp [α₁, GustafssonSolus.gsChoiceMarker, h] at hα₁zero ⊢
    have hdrop₂ : dropPivot i₂' = true := hdrop hi' hphiEq hdrop₁
    simp [α₂, GustafssonSolus.gsChoiceMarker, hdrop₂]
  have hentry := GustafssonSolus.gsEntry_has2x2 hα₁ hα₂ ht hj hcompat
  simpa [gustafssonSolusMatrix, gustafssonSolusRow, i₁', i₂', α₁, α₂,
    gustafssonSolusEntry_eq_thresholdEntry] using hentry

/-- Named Lean-facing target for Gustafsson--Solus Lemma 3.4 in the
zero-aware output convention used by this library. -/
def GustafssonSolusLemma34Statement : Prop :=
  ∀ {m n : ℕ} (phi : Fin m → Fin n) (dropPivot : Fin m → Bool),
    GustafssonSolusWeaklyIncreasing phi →
    GustafssonSolusNoSwitchAfterDrop phi dropPivot →
    ∀ fs : List ℝ[X], fs.length = n → IsInterlacingSeqNonneg fs →
      IsInterlacingSeq0Nonneg (gustafssonSolusAction phi dropPivot fs)

/-- Checked reduction of Gustafsson--Solus Lemma 3.4 to the finite `2 × 2`
affine-minor condition. -/
def GustafssonSolusLemma34Of2x2Statement : Prop :=
  ∀ {m n : ℕ} (phi : Fin m → Fin n) (dropPivot : Fin m → Bool),
    GustafssonSolusWeaklyIncreasing phi →
    GustafssonSolusHas2x2 phi dropPivot →
    ∀ fs : List ℝ[X], fs.length = n → IsInterlacingSeqNonneg fs →
      IsInterlacingSeq0Nonneg (gustafssonSolusAction phi dropPivot fs)

theorem gustafssonSolusLemma34_of_2x2 : GustafssonSolusLemma34Of2x2Statement := by
  intro m n phi dropPivot hphi h2x2 fs hfs_len hfs
  exact gustafssonSolus_preserves_interlacingSeq0Nonneg_of_2x2 hphi h2x2 fs hfs_len hfs

/-- Gustafsson--Solus Lemma 3.4 for the concrete row-threshold matrix. -/
theorem gustafssonSolusLemma34 : GustafssonSolusLemma34Statement := by
  intro m n phi dropPivot hphi hdrop fs hfs_len hfs
  exact gustafssonSolus_preserves_interlacingSeq0Nonneg_of_2x2 hphi
    (gustafssonSolus2x2_of_noSwitch phi dropPivot hphi hdrop) fs hfs_len hfs

end RealRooted
