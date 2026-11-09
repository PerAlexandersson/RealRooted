module

public import RealRooted.MatrixInterlacing.TP2Step
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Vector recursions `f_{k+1} = (M_k + X J) f_k` with `TP2` matrices

Let `M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ` be a sequence of matrices, each `TP2`
(`Matrix.IsTP2`) with weakly decreasing columns, and let `J = 𝟙 e₁ᵀ`. The vector
`affineVector M k` is `f_0 = 𝟙`, `f_{k+1} = (M_k + X J) f_k`.

Every coordinate of `f_k` is monic of degree `k` (`affineVector_monic_natDegree`), the vector is an
interlacing sequence with nonnegative coefficients (`isInterlacingSeqNonneg_affineVector`), and
its first coordinate is interlaced by every coordinate of the next vector
(`affineVector_invariant`), in particular `f_{k,1} ≪ f_{k+1,1}`
(`strictInterl_affineVector_zero`). The proof iterates Brändén's constant-matrix theorem
through the affine step `Matrix.IsTP2.interlacingSeqNonneg_cons_tp2AffineStep`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- The vector `f_{k+1} = (M_k + X J) f_k`, `f_0 = 𝟙`, `J = 𝟙 e₁ᵀ`. -/
def affineVector (M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℕ → Fin (n + 1) → ℝ[X]
  | 0 => fun _ => 1
  | k + 1 => tp2AffineStep (M k) 1 (affineVector M k)

/-- Every coordinate of `f_k` is monic of degree `k`. -/
lemma affineVector_monic_natDegree (M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ)
    (i : Fin (n + 1)) : (affineVector M k i).Monic ∧ (affineVector M k i).natDegree = k := by
  induction k generalizing i with
  | zero => simp [affineVector]
  | succ k ih =>
    have hX : (X * affineVector M k 0).Monic := monic_X.mul (ih 0).1
    have hXdeg : (X * affineVector M k 0).natDegree = k + 1 := by
      rw [natDegree_mul' (by simp [(ih 0).1.leadingCoeff]), natDegree_X, (ih 0).2]
      lia
    have hsum : (∑ j, M k i j • affineVector M k j).natDegree ≤ k :=
      natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_smul_le _ _).trans (ih j).2.le
    have hlt : (∑ j, M k i j • affineVector M k j).degree < (X * affineVector M k 0).degree :=
      degree_lt_degree (by lia)
    have hstep : affineVector M (k + 1) i =
        ∑ j, M k i j • affineVector M k j + X * affineVector M k 0 := by
      simp [affineVector, tp2AffineStep]
    rw [hstep]
    exact ⟨hX.add_of_right hlt, by rw [natDegree_add_eq_right_of_degree_lt hlt, hXdeg]⟩

lemma affineVector_ne_zero (M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ)
    (i : Fin (n + 1)) : affineVector M k i ≠ 0 :=
  (affineVector_monic_natDegree M k i).1.ne_zero

/-- The invariant of the vector recursion: the stage-`k` vector is an interlacing sequence with
nonnegative coefficients, and its first coordinate is interlaced by every coordinate of the
stage-`k + 1` vector. -/
lemma affineVector_invariant {M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : ∀ k, (M k).IsTP2) (hcol : ∀ k ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → M k i' j ≤ M k i j)
    (k : ℕ) :
    IsInterlacingSeqNonneg (List.ofFn (affineVector M k)) ∧
      IsInterlacingSeqNonneg (affineVector M k 0 :: List.ofFn (affineVector M (k + 1))) := by
  have hstep : ∀ k, IsInterlacingSeqNonneg (List.ofFn (affineVector M k)) →
      IsInterlacingSeqNonneg (affineVector M k 0 :: List.ofFn (affineVector M (k + 1))) :=
    fun k hk => (hM k).interlacingSeqNonneg_cons_tp2AffineStep (hcol k) zero_le_one hk fun i => by
      simpa [affineVector] using affineVector_ne_zero M (k + 1) i
  induction k with
  | zero =>
    have h0 : IsInterlacingSeqNonneg (List.ofFn (affineVector M 0)) := by
      refine ⟨fun p hp => ?_, isInterlacingSeq_iff_pairwise.mpr (List.pairwise_ofFn.mpr ?_)⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
        exact ⟨⟨one_ne_zero, Splits.one⟩, hasNonnegCoeffs_one⟩
      · intro i j _
        exact StrictInterl.refl one_ne_zero Splits.one
    exact ⟨h0, hstep 0 h0⟩
  | succ k ih =>
    have h1 : IsInterlacingSeqNonneg (List.ofFn (affineVector M (k + 1))) :=
      ih.2.sublist (List.sublist_cons_self _ _)
    exact ⟨h1, hstep (k + 1) h1⟩

/-- **The vector recursion preserves ordered interlacing**: every stage is an interlacing
sequence with nonnegative coefficients. -/
theorem isInterlacingSeqNonneg_affineVector {M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : ∀ k, (M k).IsTP2) (hcol : ∀ k ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → M k i' j ≤ M k i j)
    (k : ℕ) : IsInterlacingSeqNonneg (List.ofFn (affineVector M k)) :=
  (affineVector_invariant hM hcol k).1

/-- The first coordinates of consecutive stages interlace: `f_{k,1} ≪ f_{k+1,1}`. -/
theorem strictInterl_affineVector_zero {M : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : ∀ k, (M k).IsTP2) (hcol : ∀ k ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → M k i' j ≤ M k i j)
    (k : ℕ) : StrictInterl (affineVector M k 0) (affineVector M (k + 1) 0) := by
  have h := (affineVector_invariant hM hcol k).2.2
  rw [isInterlacingSeq_iff_pairwise, List.pairwise_cons] at h
  exact h.1 _ (List.mem_ofFn.mpr ⟨0, rfl⟩)

end RealRooted
