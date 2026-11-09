module

import RealRooted.Linear
import RealRooted.WagnerX.NonnegativeRoots
public import RealRooted.MatrixInterlacing.TotallyNonnegative

/-!
# Affine steps `(A + b X J) f` preserve ordered interlacing

Let `A` be a square real matrix with nonnegative entries and nonnegative ordered `2 × 2`
minors (`Matrix.IsTP2`) whose columns are weakly decreasing, and let `J = 𝟙 e₁ᵀ`, so that
`(J f)ᵢ = f₁`. If `f = (f₁, …, f_d)` is an interlacing sequence with nonnegative
coefficients, then so is `(A + b X J) f` for every `b ≥ 0`, and in addition the first
coordinate `f₁` of the input is interlaced by every coordinate of the output.

The proof applies Brändén's constant-matrix theorem (`Matrix.IsTP2.map_interlacingSeq0`,
arXiv:1410.6601, Corollary 8.6) to the augmented vector `(f₁, …, f_d, X f₁)` and the constant
matrix with the row `e₁ᵀ` (which reproduces `f₁`) followed by the rows `[A | b𝟙]`. The new
`2 × 2` minors of `[A | b𝟙]` are `b (A_{ij} - A_{kj})`, nonnegative because the columns of
`A` decrease, and Wagner's `X`-multiplication transport gives `f_j ≪ X f₁`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- The constant `(d + 1) × (d + 1)` matrix (with `d = n + 1`) whose first row selects the
first coordinate and whose remaining rows are the rows of `[A | b𝟙]`. -/
def tp2StepMatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  Matrix.of fun i j =>
    Fin.cases (if j = 0 then 1 else 0)
      (fun i' => Fin.lastCases b (fun j' => A i' j') j) i

@[simp] lemma tp2StepMatrix_zero_left (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (j : Fin (n + 2)) : tp2StepMatrix A b 0 j = if j = 0 then 1 else 0 := by
  simp [tp2StepMatrix]

@[simp] lemma tp2StepMatrix_succ_castSucc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (i j : Fin (n + 1)) : tp2StepMatrix A b i.succ j.castSucc = A i j := by
  simp [tp2StepMatrix]

@[simp] lemma tp2StepMatrix_succ_last (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (i : Fin (n + 1)) : tp2StepMatrix A b i.succ (Fin.last (n + 1)) = b := by
  simp [tp2StepMatrix]

/-- The step matrix is `TP2` when `A` is `TP2`, the columns of `A` weakly decrease and
`b ≥ 0`. -/
lemma _root_.Matrix.IsTP2.tp2StepMatrix {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    {b : ℝ} (hb : 0 ≤ b) : (RealRooted.tp2StepMatrix A b).IsTP2 := by
  refine ⟨fun i j => ?_, fun i₁ i₂ j₁ j₂ hi hj => ?_⟩
  · induction i using Fin.cases with
    | zero => simp only [tp2StepMatrix_zero_left]; split_ifs <;> norm_num
    | succ i =>
      induction j using Fin.lastCases with
      | last => simpa using hb
      | cast j => simpa using hA.nonneg i j
  · induction i₂ using Fin.cases with
    | zero => exact absurd hi (not_lt_of_ge (Fin.zero_le _))
    | succ i₂ =>
      induction i₁ using Fin.cases with
      | zero =>
        have hj₂ : j₂ ≠ 0 := (lt_of_le_of_lt (Fin.zero_le _) hj).ne'
        have hj₁ : 0 ≤ RealRooted.tp2StepMatrix A b i₂.succ j₂ := by
          induction j₂ using Fin.lastCases with
          | last => simpa using hb
          | cast j => simpa using hA.nonneg i₂ j
        simp only [tp2StepMatrix_zero_left, hj₂, ite_false, zero_mul, sub_zero]
        split_ifs <;> simp [hj₁]
      | succ i₁ =>
        have hi' : i₁ < i₂ := Fin.succ_lt_succ_iff.mp hi
        obtain ⟨j₁', rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hj)
        induction j₂ using Fin.lastCases with
        | last =>
          simp only [tp2StepMatrix_succ_castSucc, tp2StepMatrix_succ_last]
          nlinarith [mul_nonneg hb (sub_nonneg.mpr (hcol hi'.le (j := j₁')))]
        | cast j₂' =>
          have hj' : j₁' < j₂' := Fin.castSucc_lt_castSucc_iff.mp hj
          simpa using hA.minor_nonneg hi' hj'

/-- The augmented vector `(f₁, …, f_d, X f₁)`. -/
def tp2AugmentedVector (f : Fin (n + 1) → ℝ[X]) : Fin (n + 2) → ℝ[X] :=
  Fin.lastCases (X * f 0) f

@[simp] lemma tp2AugmentedVector_castSucc (f : Fin (n + 1) → ℝ[X]) (j : Fin (n + 1)) :
    tp2AugmentedVector f j.castSucc = f j := by
  simp [tp2AugmentedVector]

@[simp] lemma tp2AugmentedVector_last (f : Fin (n + 1) → ℝ[X]) :
    tp2AugmentedVector f (Fin.last (n + 1)) = X * f 0 := by
  simp [tp2AugmentedVector]

/-- The affine step `i ↦ ∑ j, A i j f j + b X f₁`, i.e. the vector `(A + b X J) f`. -/
def tp2AffineStep (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (f : Fin (n + 1) → ℝ[X]) : Fin (n + 1) → ℝ[X] :=
  fun i => ∑ j, A i j • f j + C b * X * f 0

/-- The augmented vector of an interlacing sequence with nonnegative coefficients is again
such a sequence: `f₁ ≪ f_j` gives `f_j ≪ X f₁` by Wagner's `X`-transport. -/
lemma IsInterlacingSeqNonneg.tp2AugmentedVector {f : Fin (n + 1) → ℝ[X]}
    (hf : IsInterlacingSeqNonneg (List.ofFn f)) :
    IsInterlacingSeqNonneg (List.ofFn (tp2AugmentedVector f)) := by
  have hmem : ∀ j, (f j ≠ 0 ∧ (f j).Splits) ∧ HasNonnegCoeffs (f j) :=
    fun j => hf.1 _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hpair : ∀ ⦃i j⦄, i < j → StrictInterl (f i) (f j) :=
    List.pairwise_ofFn.mp (isInterlacingSeq_iff_pairwise.mp hf.2)
  refine ⟨?_, isInterlacingSeq_iff_pairwise.mpr (List.pairwise_ofFn.mpr ?_)⟩
  · intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    induction j using Fin.lastCases with
    | last =>
      simp only [tp2AugmentedVector_last]
      exact ⟨isRealRooted_X_mul (hmem 0).1.1 (hmem 0).1.2,
        (hasNonnegCoeffs_X.mul (hmem 0).2)⟩
    | cast j => simpa using hmem j
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hij)
      simp only [tp2AugmentedVector_castSucc, tp2AugmentedVector_last]
      have h0 : StrictInterl (f 0) (f i) := by
        rcases eq_or_ne i 0 with rfl | hi
        · exact StrictInterl.refl (hmem 0).1.1 (hmem 0).1.2
        · exact hpair (Fin.pos_iff_ne_zero.mpr hi)
      exact strictInterl_mul_X_of_strictInterl_of_nonneg h0 (hmem 0).2 (hmem i).2
    | cast j =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hij)
      simpa using hpair (Fin.castSucc_lt_castSucc_iff.mp hij)

private lemma tnnMatrixAction_ofFn {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ)
    (f : Fin k → ℝ[X]) :
    tnnMatrixAction A (List.ofFn f) = List.ofFn ((A.map C).mulVec f) :=
  matPolyAction_ofFn (A.map C) f

private lemma tp2StepMatrix_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (f : Fin (n + 1) → ℝ[X]) :
    ((tp2StepMatrix A b).map C).mulVec (tp2AugmentedVector f) =
      Fin.cons (f 0) (tp2AffineStep A b f) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, tp2StepMatrix_zero_left,
      Fin.cons_zero]
    rw [Finset.sum_eq_single 0]
    · simp [show tp2AugmentedVector f 0 = f 0 from tp2AugmentedVector_castSucc f 0]
    · intro j _ hj
      simp [hj]
    · simp
  | succ i =>
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fin.cons_succ, tp2AffineStep,
      Fin.sum_univ_castSucc, tp2StepMatrix_succ_castSucc, tp2StepMatrix_succ_last,
      tp2AugmentedVector_castSucc, tp2AugmentedVector_last, Polynomial.smul_eq_C_mul]
    ring

/-- **Affine steps preserve ordered interlacing** (zero-aware form).

If `A` is `TP2` with weakly decreasing columns, `b ≥ 0`, and `f` is an interlacing sequence
with nonnegative coefficients, then the sequence `f₁, (A + b X J) f` (the first coordinate of
the input followed by all coordinates of the output) is a weak interlacing sequence with
nonnegative coefficients, and every nonzero entry is real-rooted. -/
theorem _root_.Matrix.IsTP2.interlacingSeq0NonnegRealRooted_cons_tp2AffineStep
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) {b : ℝ} (hb : 0 ≤ b)
    {f : Fin (n + 1) → ℝ[X]} (hf : IsInterlacingSeqNonneg (List.ofFn f)) :
    IsInterlacingSeq0NonnegRealRooted (f 0 :: List.ofFn (tp2AffineStep A b f)) := by
  have h := (hA.tp2StepMatrix hcol hb).map_interlacingSeq0_realRooted
    (List.ofFn (tp2AugmentedVector f)) (by simp) hf.tp2AugmentedVector
  rw [tnnMatrixAction_ofFn, tp2StepMatrix_mulVec, List.ofFn_succ] at h
  simpa only [Fin.cons_zero, Fin.cons_succ] using h

/-- **Affine steps preserve ordered interlacing**: if all coordinates of `(A + b X J) f` are
nonzero, then `f₁, (A + b X J) f` is an interlacing sequence with nonnegative coefficients. In
particular the outputs are pairwise interlacing and each is interlaced by `f₁`. -/
theorem _root_.Matrix.IsTP2.interlacingSeqNonneg_cons_tp2AffineStep
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) {b : ℝ} (hb : 0 ≤ b)
    {f : Fin (n + 1) → ℝ[X]} (hf : IsInterlacingSeqNonneg (List.ofFn f))
    (hne : ∀ i, tp2AffineStep A b f i ≠ 0) :
    IsInterlacingSeqNonneg (f 0 :: List.ofFn (tp2AffineStep A b f)) := by
  refine (hA.interlacingSeq0NonnegRealRooted_cons_tp2AffineStep hcol hb hf).sublist_of_ne
    (List.Sublist.refl _) ?_
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact (hf.realRooted _ (List.mem_ofFn.mpr ⟨0, rfl⟩)).1
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hne i

end RealRooted
