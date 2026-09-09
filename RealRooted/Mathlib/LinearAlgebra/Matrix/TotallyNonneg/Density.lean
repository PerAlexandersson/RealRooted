import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum

/-!
# Nonsingular approximation of totally nonnegative matrices

This file constructs a sequence of nonsingular totally nonnegative matrices
converging entrywise to any finite totally nonnegative matrix. Each active step
first applies a small Gaussian smoothing and then a small northwest-corner
update, strictly raising rank. Once full rank is reached, the step is the
identity.
-/

open Filter Topology
open scoped Topology

namespace Matrix

/-- Gaussian sandwiching remains asymptotic to the identity when its matrix
argument also varies convergently. -/
theorem tendsto_gaussianSandwich_nat_of_tendsto {n : ℕ}
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hA : Tendsto A atTop (𝓝 A₀)) :
    Tendsto (fun k => gaussianSandwich (A k) ((k : ℝ) + 1)) atTop
      (𝓝 A₀) := by
  have hparam : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hG : Tendsto (fun k : ℕ => gaussianMatrix n ((k : ℝ) + 1)) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    (tendsto_gaussianMatrix_atTop n).comp hparam
  simpa [gaussianSandwich] using (hG.mul hA).mul hG

/-- One asymptotically trivial rank-raising step. It is the identity on a
full-rank matrix. -/
noncomputable def tnRankStep {n : ℕ} (k : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  if A.rank < n + 1 then
    gaussianSandwich A ((k : ℝ) + 1) +
      Matrix.single 0 0 (1 / ((k : ℝ) + 1))
  else A

/-- The conditional rank-raising step tends to the identity even when applied
to a convergent matrix sequence. -/
theorem tendsto_tnRankStep_of_tendsto {n : ℕ}
    {A : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Tendsto A atTop (𝓝 A₀)) :
    Tendsto (fun k => tnRankStep k (A k)) atTop (𝓝 A₀) := by
  have hsingle : Tendsto
      (fun k : ℕ => Matrix.single (0 : Fin (n + 1)) 0
        (1 / ((k : ℝ) + 1))) atTop
      (𝓝 (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    by_cases h : 0 = i ∧ 0 = j
    · rcases h with ⟨rfl, rfl⟩
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · simp [h]
  have hop := (tendsto_gaussianSandwich_nat_of_tendsto hA).add hsingle
  have hop' : Tendsto
      (fun k => gaussianSandwich (A k) ((k : ℝ) + 1) +
        Matrix.single 0 0 (1 / ((k : ℝ) + 1))) atTop (𝓝 A₀) := by
    simpa using hop
  simpa [tnRankStep] using hop'.if' hA

/-- Every conditional rank step preserves total nonnegativity. -/
theorem IsTotallyNonneg.tnRankStep {n k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) : (Matrix.tnRankStep k A).IsTotallyNonneg := by
  unfold Matrix.tnRankStep
  split_ifs
  · exact (hA.gaussianSandwich_isTotallyNonneg (by positivity)).add_single_zero_zero
      (by positivity)
  · exact hA

/-- An active conditional rank step strictly raises rank. -/
theorem IsTotallyNonneg.rank_lt_tnRankStep {n k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hrank : A.rank < n + 1) :
    A.rank < (Matrix.tnRankStep k A).rank := by
  simp only [Matrix.tnRankStep, if_pos hrank]
  exact hA.rank_lt_rank_gaussianSandwich_add_single_zero_zero hrank
    (by positivity) (by positivity)

/-- Iterate the same asymptotically trivial rank step a fixed number of times. -/
noncomputable def tnRankIter {n : ℕ} :
    ℕ → ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
  | 0, _, A => A
  | s + 1, k, A => tnRankStep k (tnRankIter s k A)

/-- Any fixed finite number of conditional rank steps tends to the identity. -/
theorem tendsto_tnRankIter {n s : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Tendsto (fun k => tnRankIter s k A) atTop (𝓝 A) := by
  induction s with
  | zero => simp [tnRankIter]
  | succ s ih =>
      simpa [tnRankIter] using tendsto_tnRankStep_of_tendsto ih

/-- Finite iteration of conditional rank steps preserves total
nonnegativity. -/
theorem IsTotallyNonneg.tnRankIter {n s k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) : (Matrix.tnRankIter s k A).IsTotallyNonneg := by
  induction s with
  | zero => simpa [Matrix.tnRankIter] using hA
  | succ s ih =>
      simpa [Matrix.tnRankIter] using ih.tnRankStep

/-- Before the ambient dimension is reached, `s` conditional steps raise rank
by at least `s`. -/
theorem IsTotallyNonneg.rank_add_le_rank_tnRankIter {n s k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hs : A.rank + s ≤ n + 1) :
    A.rank + s ≤ (Matrix.tnRankIter s k A).rank := by
  induction s with
  | zero => simp [Matrix.tnRankIter]
  | succ s ih =>
      have hs' : A.rank + s ≤ n + 1 := by lia
      have hrank := ih hs'
      let B := Matrix.tnRankIter s k A
      have hB : B.IsTotallyNonneg := hA.tnRankIter
      by_cases hdef : B.rank < n + 1
      · have hinc := hB.rank_lt_tnRankStep (k := k) hdef
        simpa [Matrix.tnRankIter, B] using
          (show A.rank + (s + 1) ≤ (Matrix.tnRankStep k B).rank by lia)
      · have hfull : B.rank = n + 1 := by
          have hle := B.rank_le_width
          lia
        have hstep : Matrix.tnRankStep k B = B := by
          simp [Matrix.tnRankStep, hdef]
        simp only [Matrix.tnRankIter]
        rw [hstep, hfull]
        exact hs

/-- A canonical nonsingular approximation obtained by iterating exactly the
rank deficiency many conditional steps. -/
noncomputable def nonsingularTNApprox {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  tnRankIter (n + 1 - A.rank) k A

/-- The canonical nonsingular approximants converge entrywise to the original
matrix. -/
theorem tendsto_nonsingularTNApprox {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Tendsto (nonsingularTNApprox A) atTop (𝓝 A) :=
  tendsto_tnRankIter A

/-- Every canonical approximant of a totally nonnegative matrix remains
totally nonnegative. -/
theorem IsTotallyNonneg.nonsingularTNApprox {n k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) :
    (Matrix.nonsingularTNApprox A k).IsTotallyNonneg :=
  hA.tnRankIter

/-- Every canonical approximant of a totally nonnegative matrix has full
rank. -/
theorem IsTotallyNonneg.rank_nonsingularTNApprox {n k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) :
    (Matrix.nonsingularTNApprox A k).rank = n + 1 := by
  have hle : A.rank ≤ n + 1 := by
    simpa using A.rank_le_width
  have hsum : A.rank + (n + 1 - A.rank) = n + 1 :=
    Nat.add_sub_of_le hle
  have hlower := hA.rank_add_le_rank_tnRankIter
    (k := k) (s := n + 1 - A.rank) (by rw [hsum])
  rw [hsum] at hlower
  change n + 1 ≤ (Matrix.nonsingularTNApprox A k).rank at hlower
  exact le_antisymm (Matrix.nonsingularTNApprox A k).rank_le_width hlower

/-- A square real matrix with full rank has nonzero determinant. -/
theorem det_ne_zero_of_rank_eq_card {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hrank : A.rank = n) : A.det ≠ 0 := by
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hrank
  have hsurj : Function.Surjective A.mulVecLin :=
    LinearMap.range_eq_top.mp hrange
  have hinj : Function.Injective A.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.mulVecLin) rfl).mpr hsurj
  have hinj' : Function.Injective A.mulVec := by
    rw [← Matrix.coe_mulVecLin]
    exact hinj
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj'
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  exact hunit

/-- Every canonical totally nonnegative approximant is nonsingular. -/
theorem IsTotallyNonneg.det_nonsingularTNApprox_ne_zero {n k : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) : (Matrix.nonsingularTNApprox A k).det ≠ 0 :=
  det_ne_zero_of_rank_eq_card hA.rank_nonsingularTNApprox

end Matrix
