import RealRooted.GeneralizedSnakePosets.Statements
import RealRooted.MatrixInterlacing

/-!
# Braun-Jal matrix-induction step

This module isolates the local two-row matrix step used in Braun-Jal's proof
of Theorem 4.1.  The theorem statements stay close to the paper recurrence:
the matrix with rows `[P_{m-1}, G_{m-1}]` and `[P_m, G_m]` acts on the
induction pair `[f, X * g]`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The two-row matrix for one Braun-Jal Theorem 4.1 induction step. -/
def theorem41StepMatrix (P G : ℕ → ℝ[X]) (m : ℕ) : List (List ℝ[X]) :=
  [[P (m - 1), G (m - 1)], [P m, G m]]

@[simp] theorem theorem41StepMatrix_length (P G : ℕ → ℝ[X]) (m : ℕ) :
    (theorem41StepMatrix P G m).length = 2 := by
  simp [theorem41StepMatrix]

/-- Each row of the Braun-Jal step matrix has length two. -/
theorem theorem41StepMatrix_rect (P G : ℕ → ℝ[X]) (m : ℕ) :
    ∀ row ∈ theorem41StepMatrix P G m, row.length = 2 := by
  intro row hrow
  have hrow' :
      row = [P (m - 1), G (m - 1)] ∨ row = [P m, G m] := by
    simpa [theorem41StepMatrix] using hrow
  rcases hrow' with rfl | rfl <;> simp

/-- Entrywise nonnegativity for the Braun-Jal step matrix. -/
theorem theorem41StepMatrix_entry_nonneg {P G : ℕ → ℝ[X]} {m : ℕ}
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n)) :
    ∀ row ∈ theorem41StepMatrix P G m, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  have hrow' :
      row = [P (m - 1), G (m - 1)] ∨ row = [P m, G m] := by
    simpa [theorem41StepMatrix] using hrow
  rcases hrow' with rfl | rfl
  · have hp' : p = P (m - 1) ∨ p = G (m - 1) := by
      simpa using hp
    rcases hp' with rfl | rfl
    · exact hP_nonneg (m - 1)
    · exact hG_nonneg (m - 1)
  · have hp' : p = P m ∨ p = G m := by
      simpa using hp
    rcases hp' with rfl | rfl
    · exact hP_nonneg m
    · exact hG_nonneg m

/-- The step matrix action gives the two recurrence sums appearing in the
nonconstant induction step. -/
theorem theorem41StepMatrix_action_pair
    (P G : ℕ → ℝ[X]) (m : ℕ) (f g : ℝ[X]) :
    matPolyAction (theorem41StepMatrix P G m) [f, X * g] =
      [f * P (m - 1) + X * g * G (m - 1), f * P m + X * g * G m] := by
  simp [theorem41StepMatrix, matPolyAction, mul_comm, mul_left_comm]

/-- The induction hypothesis `g << f` makes `[f, X * g]` a nonnegative
interlacing input sequence. -/
theorem theorem41InputPair_interlacingSeqNonneg {f g : ℝ[X]}
    (hgf : Prec g f) (hf_nonneg : HasNonnegCoeffs f)
    (hg_nonneg : HasNonnegCoeffs g) :
    IsInterlacingSeqNonneg [f, X * g] := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp' : p = f ∨ p = X * g := by
      simpa using hp
    rcases hp' with rfl | rfl
    · exact ⟨⟨hgf.2.1.1, hgf.2.1.2⟩, hf_nonneg⟩
    · exact ⟨isRealRooted_X_mul hgf.1.1 hgf.1.2, hg_nonneg.X_mul⟩
  · rw [isInterlacingSeq_iff_pairwise]
    simp [prec_mul_X_of_prec_of_nonneg hgf hg_nonneg hf_nonneg]

/-- Claim `(7)` supplies the nontrivial cross `2 x 2` affine test for the
Braun-Jal step matrix. -/
theorem theorem41StepMatrix_cross_has2x2_of_claim7
    {P G : ℕ → ℝ[X]} (hclaim : Theorem41Claim7Statement P G)
    {m : ℕ} (hm : 2 ≤ m) :
    Has2x2InterlacingProperty (P (m - 1)) (G (m - 1)) (P m) (G m) := by
  intro s t hs ht
  exact hclaim (m := m) (lam := s) (nu := t) hm hs.le (by linarith)

/-- Claim `(7)`, the column interlacings, and the induction pair propagate
proper position through one nonconstant recurrence step. -/
theorem theorem41Step_prec_of_claim7
    {P G : ℕ → ℝ[X]} {m : ℕ} {f g : ℝ[X]}
    (hclaim : Theorem41Claim7Statement P G) (hm : 2 ≤ m)
    (hP : Prec (P (m - 1)) (P m)) (hG : Prec (G (m - 1)) (G m))
    (hgf : Prec g f)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g) :
    Prec (f * P (m - 1) + X * g * G (m - 1))
      (f * P m + X * g * G m) := by
  have hinput : Prec f (X * g) :=
    prec_mul_X_of_prec_of_nonneg hgf hg_nonneg hf_nonneg
  have hpair := prec_add_mul_pair_of_2x2
    (p₁ := P (m - 1)) (q₁ := G (m - 1)) (p₂ := P m) (q₂ := G m)
    (u := f) (v := X * g)
    hP hG (theorem41StepMatrix_cross_has2x2_of_claim7 hclaim hm) hinput
    (hP_nonneg (m - 1)) (hG_nonneg (m - 1))
    (hP_nonneg m) (hG_nonneg m) hf_nonneg hg_nonneg.X_mul
  simpa [mul_comm, mul_left_comm] using hpair

/-- Matrix Claim `(6)` gives the same recurrence-step proper-position result
via the existing Claim `(6)`/Claim `(7)` reindexing. -/
theorem theorem41Step_prec_of_matrixClaim
    {P G : ℕ → ℝ[X]} {m : ℕ} {f g : ℝ[X]}
    (hclaim : Theorem41MatrixClaimStatement P G) (hm : 2 ≤ m)
    (hP : Prec (P (m - 1)) (P m)) (hG : Prec (G (m - 1)) (G m))
    (hgf : Prec g f)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g) :
    Prec (f * P (m - 1) + X * g * G (m - 1))
      (f * P m + X * g * G m) :=
  theorem41Step_prec_of_claim7
    ((theorem41MatrixClaim_iff_claim7 P G).mp hclaim) hm
    hP hG hgf hP_nonneg hG_nonneg hf_nonneg hg_nonneg

end GeneralizedSnakePosets
end RealRooted
