/-
# Row-threshold matrices of nonnegative linear forms

This module records the public `RealRooted` interface for the row-threshold
linear-form structure appearing in Branden's Corollary 8.7.
-/
import RealRooted.MatrixInterlacing

open Polynomial

noncomputable section

namespace RealRooted

/-- A polynomial is a nonnegative linear form if it can be written as `a + bX`
with `a, b ≥ 0`. -/
def IsNonnegLinearForm (p : ℝ[X]) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ p = C a + C b * X

lemma isNonnegLinearForm_zero : IsNonnegLinearForm (0 : ℝ[X]) :=
  ⟨0, 0, le_rfl, le_rfl, by simp⟩

lemma isNonnegLinearForm_one : IsNonnegLinearForm (1 : ℝ[X]) :=
  ⟨1, 0, by simp, le_rfl, by simp⟩

lemma isNonnegLinearForm_X : IsNonnegLinearForm (X : ℝ[X]) :=
  ⟨0, 1, le_rfl, by simp, by simp⟩

/-- Zero-based row-threshold condition: the `X`-coefficient can be positive
only before position `p`, and the constant term can be positive only from
position `p` onward. -/
def HasRowThreshold (row : List ℝ[X]) (p : ℕ) : Prop :=
  p ≤ row.length ∧
  ∀ j : Fin row.length,
    IsNonnegLinearForm (row.get j) ∧
      (0 < (row.get j).coeff 1 → j.1 < p) ∧
      (0 < (row.get j).coeff 0 → p ≤ j.1)

/-- List-matrix formulation of the row-threshold hypothesis. The threshold
function is weakly increasing down the rows. -/
def HasRowThresholdLinearStructure (G : List (List ℝ[X])) : Prop :=
  ∃ p : Fin G.length → ℕ,
    (∀ i, HasRowThreshold (G.get i) (p i)) ∧
    ∀ ⦃i j : Fin G.length⦄, i ≤ j → p i ≤ p j

/-- Named target for the specialized Branden row-threshold corollary in the
strict nonzero `IsInterlacingSeqNonneg` convention used by this library.  The
fully zero-aware theorem should ultimately prove this under the extra
nonvanishing hypotheses needed to remove zero output rows. -/
def RowThresholdMatricesPreserveInterlacingSeqNonneg : Prop :=
  ∀ {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X]),
    G.length = n →
    (∀ row ∈ G, row.length = n) →
    HasRowThresholdLinearStructure G →
    fs.length = n →
    IsInterlacingSeqNonneg fs →
    IsInterlacingSeqNonneg (matPolyAction G fs)

lemma isNonnegLinearForm_hasNonnegCoeffs {p : ℝ[X]}
    (hp : IsNonnegLinearForm p) :
    HasNonnegCoeffs p := by
  rcases hp with ⟨a, b, ha, hb, rfl⟩
  rintro (_ | _ | n) <;> simp [ha, hb]

lemma hasRowThreshold_nonneg {row : List ℝ[X]} {p : ℕ}
    (hrow : HasRowThreshold row p) :
    ∀ q ∈ row, HasNonnegCoeffs q := by
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hq
  exact isNonnegLinearForm_hasNonnegCoeffs (hrow.2 j).1

lemma hasRowThresholdLinearStructure_nonneg {G : List (List ℝ[X])}
    (hG : HasRowThresholdLinearStructure G) :
    ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p := by
  rcases hG with ⟨_, hrows, _⟩
  intro row hrow p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hrow
  exact hasRowThreshold_nonneg (hrows i) p hp

/-- The row-threshold structure plus the strict Branden 2x2 affine-minor
condition preserves interlacing sequences. This is the part that follows
directly from the existing `matrix_preserves_interlacing_seq` theorem.

The rook matrix does not satisfy the strict 2x2 condition because of zero
entries above the diagonal; it needs the zero-aware row-threshold corollary
targeted by `RowThresholdMatricesPreserveInterlacingSeqNonneg`. -/
theorem rowThreshold_matrix_preserves_interlacing_seq_of_2x2
    (hn : 0 < n)
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) :=
  matrix_preserves_interlacing_seq hn G hG_rect
    (hasRowThresholdLinearStructure_nonneg hG_threshold)
    hG_affine fs hfs_len hfs

/-- Public weak zero-aware row-threshold wrapper. The row-threshold structure
supplies entrywise nonnegative coefficients, and the weak 2×2 affine-minor
condition is enough to preserve interlacing into the zero-aware target family. -/
theorem rowThreshold_matrix_preserves_interlacing_seq0_of_2x2
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) :=
  matrix_preserves_interlacing_seq0_of_2x2 G hG_rect
    (hasRowThresholdLinearStructure_nonneg hG_threshold)
    hG_affine fs hfs_len hfs

end RealRooted
