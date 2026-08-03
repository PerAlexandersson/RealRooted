import RealRooted.GeneralizedSnakePosets.Statements
import RealRooted.MatrixInterlacing
import RealRooted.PFPolynomial

/-!
# Braun-Jal matrix-induction step

This module isolates the local two-row matrix step used in Braun--Jal's proof
of Theorem 4.1 (arXiv:2607.00922v1, p. 10).  The source matrix has rows
`[P_{m-1}, G_{m-1}]` and `[Q_m, H_m]`, where `Q_m = P_m - P_{m-1}` and
`H_m = G_m - G_{m-1}`, and acts on the induction pair `[f, X * g]`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The two-row matrix for one Braun-Jal Theorem 4.1 induction step. -/
def theorem41StepMatrix (P G : ℕ → ℝ[X]) (m : ℕ) : List (List ℝ[X]) :=
  [[P (m - 1), G (m - 1)],
    [narayanaDifference P m, auxiliaryDifference G m]]

@[simp] theorem theorem41StepMatrix_length (P G : ℕ → ℝ[X]) (m : ℕ) :
    (theorem41StepMatrix P G m).length = 2 := by
  simp [theorem41StepMatrix]

/-- Each row of the Braun-Jal step matrix has length two. -/
theorem theorem41StepMatrix_rect (P G : ℕ → ℝ[X]) (m : ℕ) :
    ∀ row ∈ theorem41StepMatrix P G m, row.length = 2 := by
  intro row hrow
  have hrow' :
      row = [P (m - 1), G (m - 1)] ∨
        row = [narayanaDifference P m, auxiliaryDifference G m] := by
    simpa [theorem41StepMatrix] using hrow
  rcases hrow' with rfl | rfl <;> simp

/-- Entrywise nonnegativity for the Braun-Jal step matrix. -/
theorem theorem41StepMatrix_entry_nonneg {P G : ℕ → ℝ[X]} {m : ℕ}
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : HasNonnegCoeffs (auxiliaryDifference G m)) :
    ∀ row ∈ theorem41StepMatrix P G m, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  have hrow' :
      row = [P (m - 1), G (m - 1)] ∨
        row = [narayanaDifference P m, auxiliaryDifference G m] := by
    simpa [theorem41StepMatrix] using hrow
  rcases hrow' with rfl | rfl
  · have hp' : p = P (m - 1) ∨ p = G (m - 1) := by
      simpa using hp
    rcases hp' with rfl | rfl
    · exact hP_nonneg (m - 1)
    · exact hG_nonneg (m - 1)
  · have hp' :
        p = narayanaDifference P m ∨ p = auxiliaryDifference G m := by
      simpa using hp
    rcases hp' with rfl | rfl
    · exact hQ_nonneg
    · exact hH_nonneg

/-- The step matrix action gives the two recurrence sums appearing in the
nonconstant induction step. -/
theorem theorem41StepMatrix_action_pair
    (P G : ℕ → ℝ[X]) (m : ℕ) (f g : ℝ[X]) :
    matPolyAction (theorem41StepMatrix P G m) [f, X * g] =
      [f * P (m - 1) + X * g * G (m - 1),
        f * narayanaDifference P m + X * g * auxiliaryDifference G m] := by
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

/-- Claim `(6)` is exactly the cross `2 x 2` affine test for the source matrix
in Braun--Jal's proof of Theorem 4.1. -/
theorem theorem41StepMatrix_cross_has2x2_of_matrixClaim
    {P G : ℕ → ℝ[X]} (hclaim : Theorem41MatrixClaimStatement P G)
    {m : ℕ} (hm : 2 ≤ m) :
    Has2x2InterlacingProperty (P (m - 1)) (G (m - 1))
      (narayanaDifference P m) (auxiliaryDifference G m) := by
  intro s t hs ht
  exact hclaim hm hs.le ht.le

/-- Claim `(6)` and the source matrix send the induction pair to a proper-position
pair.  Repeated column indices use the real-rootedness already contained in the
same Claim `(6)` instance. -/
theorem theorem41Step_difference_prec_of_matrixClaim
    {P G : ℕ → ℝ[X]} {m : ℕ} {f g : ℝ[X]}
    (hclaim : Theorem41MatrixClaimStatement P G) (hm : 2 ≤ m)
    (hP_ne : P (m - 1) ≠ 0)
    (hQ_ne : narayanaDifference P m ≠ 0)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : HasNonnegCoeffs (auxiliaryDifference G m))
    (hgf : Prec g f)
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g) :
    Prec (f * P (m - 1) + X * g * G (m - 1))
      (f * narayanaDifference P m + X * g * auxiliaryDifference G m) := by
  have hpair := prec_zipWith_sum_pair_of_2x2
    (n := 2) (row₁ := [P (m - 1), G (m - 1)])
    (row₂ := [narayanaDifference P m, auxiliaryDifference G m])
    (fs := [f, X * g])
    (hn := by decide)
    (hrow₁_len := by simp)
    (hrow₂_len := by simp)
    (hrow₁_head_ne := by simpa using hP_ne)
    (hrow₂_head_ne := by simpa using hQ_ne)
    (hrow₁_nonneg := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hP_nonneg (m - 1)
      · exact hG_nonneg (m - 1))
    (hrow₂_nonneg := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hQ_nonneg
      · exact hH_nonneg)
    (h2x2 := by
      intro j₁ j₂ hj
      fin_cases j₁ <;> fin_cases j₂
      · intro s t hs ht
        have hcross := hclaim (m := m) (lam := s) (mu := t) hm hs.le ht.le
        simpa using prec_refl hcross.2.1.1 hcross.2.1.2
      · simpa using theorem41StepMatrix_cross_has2x2_of_matrixClaim hclaim hm
      · simp at hj
      · intro s t hs ht
        have hcross := hclaim (m := m) (lam := s) (mu := t) hm hs.le ht.le
        simpa using prec_refl hcross.1.1 hcross.1.2)
    (hfs_len := by simp)
    (hfs := theorem41InputPair_interlacingSeqNonneg hgf hf_nonneg hg_nonneg)
  simpa [mul_comm, mul_left_comm] using hpair

/-- Claim `(7)` supplies the cross affine test for the stronger consecutive-row
matrix with rows `[P_{m-1}, G_{m-1}]` and `[P_m, G_m]`.  This is an auxiliary
route, not the matrix displayed in Braun--Jal's proof. -/
theorem theorem41ConsecutiveMatrix_cross_has2x2_of_claim7
    {P G : ℕ → ℝ[X]} (hclaim : Theorem41Claim7Statement P G)
    {m : ℕ} (hm : 2 ≤ m) :
    Has2x2InterlacingProperty (P (m - 1)) (G (m - 1)) (P m) (G m) := by
  intro s t hs ht
  exact hclaim (m := m) (lam := s) (nu := t) hm hs.le (by linarith)

/-- A stronger alternative to the source matrix step: Claim `(7)` plus proper
position in both consecutive columns propagates the induction pair directly.
The paper instead applies Claim `(6)` to `theorem41StepMatrix` and then uses
Lemma 2.6. -/
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
    hP hG (theorem41ConsecutiveMatrix_cross_has2x2_of_claim7 hclaim hm) hinput
    (hP_nonneg (m - 1)) (hG_nonneg (m - 1))
    (hP_nonneg m) (hG_nonneg m) hf_nonneg hg_nonneg.X_mul
  simpa [mul_comm, mul_left_comm] using hpair

/-- Nonconstant word-level recurrence step for Braun-Jal Theorem 4.1.

If the last-change index survives deleting the final letter, Theorem 3.5
expresses both `M w` and `M w.deleteFinal` with the same prefix polynomials
and adjacent suffix parameter.  The matrix step then propagates the induction
hypothesis on the prefix pair to `Prec (M w.deleteFinal) (M w)`. -/
theorem theorem41NonconstantStep_prec_of_claim7
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]} {w : SnakeWord} {k : ℕ}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41Claim7Statement P G)
    (hlast : w.IsLastChangeIndex k)
    (hk : k + 1 < w.deleteFinal.length)
    (hP : ∀ {m : ℕ}, 2 ≤ m → Prec (P (m - 1)) (P m))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hprefix : Prec (M (w.takePrefix k)) (M (w.takePrefix (k + 1))))
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ u, HasNonnegCoeffs (M u)) :
    Prec (M w.deleteFinal) (M w) := by
  let f : ℝ[X] := M (w.takePrefix (k + 1))
  let g : ℝ[X] := M (w.takePrefix k)
  let m : ℕ := w.length - (k + 1)
  have hm : 2 ≤ m := by
    dsimp [m]
    rw [SnakeWord.length_deleteFinal] at hk
    lia
  have hkp1_le : k + 1 ≤ w.deleteFinal.length := le_of_lt hk
  have hk_le : k ≤ w.deleteFinal.length := by
    lia
  have hrec_w :
      M w = f * P m + X * g * G m := by
    dsimp [f, g, m]
    exact hrec hlast.not_isConstant hlast
  have hlast_del : w.deleteFinal.IsLastChangeIndex k :=
    hlast.deleteFinal hk
  have hrec_del :
      M w.deleteFinal = f * P (m - 1) + X * g * G (m - 1) := by
    have hbase := hrec hlast_del.not_isConstant hlast_del
    dsimp [f, g, m]
    rw [hbase]
    rw [SnakeWord.takePrefix_deleteFinal_eq_takePrefix_of_le hkp1_le]
    rw [SnakeWord.takePrefix_deleteFinal_eq_takePrefix_of_le hk_le]
    rw [SnakeWord.length_deleteFinal_sub_eq]
  have hstep := theorem41Step_prec_of_claim7
    (P := P) (G := G) (m := m) (f := f) (g := g)
    hclaim hm (hP hm) (hG hm) hprefix hP_nonneg hG_nonneg
    (hM_nonneg (w.takePrefix (k + 1))) (hM_nonneg (w.takePrefix k))
  rwa [hrec_del, hrec_w]

/-- The nonconstant Braun--Jal induction step through the source
`[P, G; Q, H]` matrix.  Unlike the consecutive-row shortcut above, this is the
argument on p. 10 of the paper and requires no adjacent-`G` proper position. -/
theorem theorem41NonconstantStep_prec_of_matrixClaim
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]} {w : SnakeWord} {k : ℕ}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41MatrixClaimStatement P G)
    (hlast : w.IsLastChangeIndex k)
    (hk : k + 1 < w.deleteFinal.length)
    (hP_ne : ∀ n, P n ≠ 0)
    (hQ_ne : ∀ {m : ℕ}, 2 ≤ m → narayanaDifference P m ≠ 0)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (auxiliaryDifference G m))
    (hprefix : Prec (M (w.takePrefix k)) (M (w.takePrefix (k + 1))))
    (hM_nonneg : ∀ u, HasNonnegCoeffs (M u)) :
    Prec (M w.deleteFinal) (M w) := by
  let f : ℝ[X] := M (w.takePrefix (k + 1))
  let g : ℝ[X] := M (w.takePrefix k)
  let m : ℕ := w.length - (k + 1)
  have hm : 2 ≤ m := by
    dsimp [m]
    rw [SnakeWord.length_deleteFinal] at hk
    lia
  have hkp1_le : k + 1 ≤ w.deleteFinal.length := le_of_lt hk
  have hk_le : k ≤ w.deleteFinal.length := by lia
  have hrec_w : M w = f * P m + X * g * G m := by
    dsimp [f, g, m]
    exact hrec hlast.not_isConstant hlast
  have hlast_del : w.deleteFinal.IsLastChangeIndex k := hlast.deleteFinal hk
  have hrec_del :
      M w.deleteFinal = f * P (m - 1) + X * g * G (m - 1) := by
    have hbase := hrec hlast_del.not_isConstant hlast_del
    dsimp [f, g, m]
    rw [hbase]
    rw [SnakeWord.takePrefix_deleteFinal_eq_takePrefix_of_le hkp1_le]
    rw [SnakeWord.takePrefix_deleteFinal_eq_takePrefix_of_le hk_le]
    rw [SnakeWord.length_deleteFinal_sub_eq]
  have hrec_diff :
      M w - M w.deleteFinal =
        f * narayanaDifference P m + X * g * auxiliaryDifference G m := by
    rw [hrec_w, hrec_del]
    unfold narayanaDifference auxiliaryDifference
    ring
  have hf_nonneg : HasNonnegCoeffs f := hM_nonneg _
  have hg_nonneg : HasNonnegCoeffs g := hM_nonneg _
  have hdiff_nonneg : HasNonnegCoeffs (M w - M w.deleteFinal) := by
    rw [hrec_diff]
    exact (hf_nonneg.mul (hQ_nonneg hm)).add
      (hg_nonneg.X_mul.mul (hH_nonneg hm))
  have hstep : Prec (M w.deleteFinal) (M w - M w.deleteFinal) := by
    rw [hrec_del, hrec_diff]
    exact theorem41Step_difference_prec_of_matrixClaim
      hclaim hm (hP_ne (m - 1)) (hQ_ne hm) hP_nonneg hG_nonneg
      (hQ_nonneg hm) (hH_nonneg hm) hprefix hf_nonneg hg_nonneg
  have hsum0 : Prec0 (M w.deleteFinal)
      (M w.deleteFinal + (M w - M w.deleteFinal)) :=
    prec0_add_right_of_common_left_of_nonneg
      (prec_refl hstep.1.1 hstep.1.2).toPrec0 hstep.toPrec0
      (hM_nonneg w.deleteFinal) hdiff_nonneg
  have hsum_ne : M w.deleteFinal + (M w - M w.deleteFinal) ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      (hM_nonneg w.deleteFinal) hdiff_nonneg hstep.2.1.1
  have hfinal := hsum0.toPrec_of_ne hstep.1.1 hsum_ne
  convert hfinal using 1 <;> ring

/-- Polynomial form of the exceptional `m = 1` Braun-Jal step.

If `g ≪ f` and both polynomials have nonnegative coefficients, then
`f ≪ (1 + X) f + X g`. -/
theorem theorem41StepOne_prec_of_prec_nonneg {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g) :
    Prec f ((1 + X) * f + X * g) := by
  have hf_Xg : Prec f (X * g) :=
    prec_mul_X_of_prec_of_nonneg hgf hg_nonneg hf_nonneg
  have hsum_nonneg : HasNonnegCoeffs (f + X * g) :=
    hf_nonneg.add hg_nonneg.X_mul
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + (f + X * g)) ≠ 0 ∧
          (((C s * X + C t) * f) + (f + X * g)).Splits) := by
    intro s t hs ht
    have ht_one : 0 < t + 1 := by linarith
    have hbase :=
      isRealRooted_affine_combo_of_prec_nonneg
        hf_Xg hf_nonneg hg_nonneg.X_mul hs ht_one
    have hrew :
        ((C s * X + C t) * f + (f + X * g)) =
          ((C s * X + C (t + 1)) * f + X * g) := by
      simp only [map_add, map_one]
      ring
    rwa [hrew]
  have hshift :=
    prec_shifted_pair_of_affine_family_nonneg
      (f := f) (g := f + X * g) hgf.2.1.1 hf_nonneg hsum_nonneg haff
  simpa [left_distrib, right_distrib, mul_assoc, add_assoc, add_left_comm,
    add_comm] using hshift

/-- Word-level form of the exceptional `m = 1` Braun-Jal recurrence step.

When the final constant suffix has length one, Theorem 3.5 rewrites `M w` as
`(1 + X) f + X g`, while `w.deleteFinal` is the prefix carrying `f`. -/
theorem theorem41StepOne_prec_of_recurrence
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]} {w : SnakeWord} {k : ℕ}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hlast : w.IsLastChangeIndex k)
    (hsuffix : w.length - (k + 1) = 1)
    (hprefix : Prec (M (w.takePrefix k)) (M (w.takePrefix (k + 1))))
    (hM_nonneg : ∀ u, HasNonnegCoeffs (M u)) :
    Prec (M w.deleteFinal) (M w) := by
  let f : ℝ[X] := M (w.takePrefix (k + 1))
  let g : ℝ[X] := M (w.takePrefix k)
  have hdel : w.deleteFinal = w.takePrefix (k + 1) :=
    SnakeWord.deleteFinal_eq_takePrefix_succ_of_length_sub_eq_one hsuffix
  have hrec_w : M w = (1 + X) * f + X * g := by
    dsimp [f, g]
    rw [hrec hlast.not_isConstant hlast, hsuffix, hP_one, hG_one]
    ring
  have hstep := theorem41StepOne_prec_of_prec_nonneg
    (f := f) (g := g) hprefix
    (hM_nonneg (w.takePrefix (k + 1))) (hM_nonneg (w.takePrefix k))
  rwa [hdel, hrec_w]

/-- Length-induction skeleton for Braun-Jal Theorem 4.1.

If every nonconstant word step turns the prefix induction hypothesis into
`Prec (M w.deleteFinal) (M w)`, then constant words and the degree bridge
finish the full deletion-interlacing statement. -/
theorem theorem41_of_prec_step
    {M : SnakeWord → ℝ[X]}
    (hstep :
      ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
        Prec (M (w.takePrefix k)) (M (w.takePrefix (k + 1))) →
          Prec (M w.deleteFinal) (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w)) :
    Theorem41NonNestingRookStatement M := by
  have hmain :
      ∀ n, ∀ w : SnakeWord, w.length = n → 1 ≤ w.length →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro w hlen hw
        by_cases hconstw : w.IsConstant
        · exact hconst hw hconstw
        · rcases SnakeWord.exists_isLastChangeIndex_of_not_isConstant hconstw with ⟨k, hlast⟩
          have hprefix_result :
              (M (w.takePrefix (k + 1)) ≠ 0 ∧
                  (M (w.takePrefix (k + 1))).Splits) ∧
                Interlaces
                  (M (w.takePrefix (k + 1)).deleteFinal)
                  (M (w.takePrefix (k + 1))) := by
            refine ih (w.takePrefix (k + 1)).length ?_ (w.takePrefix (k + 1)) rfl ?_
            · rw [← hlen, hlast.takePrefix_succ_length]
              exact hlast.succ_lt_length
            · rw [hlast.takePrefix_succ_length]
              lia
          have hprefix_prec :
              Prec (M (w.takePrefix k)) (M (w.takePrefix (k + 1))) := by
            rw [← SnakeWord.deleteFinal_takePrefix_succ_of_lt hlast.index_lt_length]
            exact hprefix_result.2.toPrec
          have hprec := hstep hconstw hlast hprefix_prec
          have hinter : Interlaces (M w.deleteFinal) (M w) :=
            hprec.toInterlaces (hdeg hw)
          exact ⟨hinter.1, hinter⟩
  intro w hw
  exact hmain w.length w rfl hw

/-- Length-induction route from Claim `(7)` to Braun-Jal Theorem 4.1.

The remaining hypotheses expose the parts not proved by the matrix step:
constant words, the infinite `m = 1` final-suffix family, and the degree bridge
used to turn `Prec` into `Interlaces`. -/
theorem theorem41_of_claim7_of_base_cases
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41Claim7Statement P G)
    (hP : ∀ {m : ℕ}, 2 ≤ m → Prec (P (m - 1)) (P m))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w))
    (hstepOne :
      ∀ {w : SnakeWord} {k : ℕ}, 1 ≤ w.length → ¬ w.IsConstant →
        w.IsLastChangeIndex k → w.length - (k + 1) = 1 →
          (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w)) :
    Theorem41NonNestingRookStatement M := by
  refine theorem41_of_prec_step (M := M) ?_ hdeg hconst
  intro w k hconstw hlast hprefix_prec
  by_cases hk : k + 1 < w.deleteFinal.length
  · exact theorem41NonconstantStep_prec_of_claim7
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hclaim hlast hk hP hG hprefix_prec hP_nonneg hG_nonneg hM_nonneg
  · have hw : 1 ≤ w.length :=
      Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le k) hlast.index_lt_length)
    have hsuffix : w.length - (k + 1) = 1 := by
      rw [SnakeWord.length_deleteFinal] at hk
      have hlast_suffix := hlast.succ_lt_length
      lia
    exact (hstepOne hw hconstw hlast hsuffix).2.toPrec

/-- Constant-word branch from a length-model identity.

If constant words evaluate to the family `P` at their length, then consecutive
interlacing for `P` proves the whole positive-length constant-word branch of
Theorem 4.1. -/
theorem theorem41_constant_of_matches_length
    {M : SnakeWord → ℝ[X]} {P : ℕ → ℝ[X]}
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P w.length)
    (hP_interlaces : ∀ {n : ℕ}, 1 ≤ n → Interlaces (P (n - 1)) (P n)) :
    ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
      (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) := by
  intro w hw hconstw
  have hdel_const : w.deleteFinal.IsConstant := hconstw.deleteFinal
  have hlen_del : w.deleteFinal.length = w.length - 1 :=
    SnakeWord.length_deleteFinal w
  have hinter : Interlaces (P (w.length - 1)) (P w.length) :=
    hP_interlaces hw
  have hright : M w ≠ 0 ∧ (M w).Splits := by
    simpa [hM_const (w := w) hconstw] using hinter.1
  have hinter_M : Interlaces (M w.deleteFinal) (M w) := by
    rw [hM_const (w := w) hconstw]
    rw [hM_const (w := w.deleteFinal) hdel_const]
    rw [hlen_del]
    exact hinter
  exact ⟨hright, hinter_M⟩

/-- Constant-word branch from a successor-length model identity.

This is the indexing used by the concrete Braun--Jal snake boards: the empty
word already gives the first modified Narayana polynomial, so a constant word
of list length `n` evaluates to `P (n + 1)`. -/
theorem theorem41_constant_of_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P : ℕ → ℝ[X]}
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P (w.length + 1))
    (hP_interlaces : ∀ n : ℕ, Interlaces (P n) (P (n + 1))) :
    ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
      (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) := by
  intro w hw hconstw
  have hdel_const : w.deleteFinal.IsConstant := hconstw.deleteFinal
  have hlen_del : w.deleteFinal.length + 1 = w.length := by
    rw [SnakeWord.length_deleteFinal]
    exact Nat.sub_add_cancel hw
  have hinter : Interlaces (P w.length) (P (w.length + 1)) :=
    hP_interlaces w.length
  have hright : M w ≠ 0 ∧ (M w).Splits := by
    simpa [hM_const (w := w) hconstw] using hinter.1
  have hinter_M : Interlaces (M w.deleteFinal) (M w) := by
    rw [hM_const (w := w) hconstw]
    rw [hM_const (w := w.deleteFinal) hdel_const]
    rw [hlen_del]
    exact hinter
  exact ⟨hright, hinter_M⟩

/-- Length-induction route from Claim `(7)` to Braun-Jal Theorem 4.1 with the
`m = 1` recurrence branch discharged.

The only remaining word-level base family is the positive-length constant-word
case.  The short final suffix is handled by Theorem 3.5 together with
`P_1 = 1 + X`, `G_1 = 1`, and the induction hypothesis on the prefix ending at
the last-change index. -/
theorem theorem41_of_claim7_of_constant_cases
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41Claim7Statement P G)
    (hP : ∀ {m : ℕ}, 2 ≤ m → Prec (P (m - 1)) (P m))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w)) :
    Theorem41NonNestingRookStatement M := by
  refine theorem41_of_prec_step (M := M) ?_ hdeg hconst
  intro w k _hconstw hlast hprefix_prec
  by_cases hk : k + 1 < w.deleteFinal.length
  · exact theorem41NonconstantStep_prec_of_claim7
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hclaim hlast hk hP hG hprefix_prec hP_nonneg hG_nonneg hM_nonneg
  · have hsuffix : w.length - (k + 1) = 1 := by
      rw [SnakeWord.length_deleteFinal] at hk
      have hlast_suffix := hlast.succ_lt_length
      lia
    exact theorem41StepOne_prec_of_recurrence
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hP_one hG_one hlast hsuffix hprefix_prec hM_nonneg

/-- Source-matrix length induction from Claim `(6)` to Braun--Jal Theorem 4.1.

The long-suffix branch uses the displayed `[P, G; Q, H]` matrix, while the
suffix-one branch uses `P_1 = 1 + X` and `G_1 = 1`.  In particular, no
adjacent-`G` proper-position hypothesis occurs. -/
theorem theorem41_of_matrixClaim_of_constant_cases
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41MatrixClaimStatement P G)
    (hP_ne : ∀ n, P n ≠ 0)
    (hQ_ne : ∀ {m : ℕ}, 2 ≤ m → narayanaDifference P m ≠ 0)
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (auxiliaryDifference G m))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w)) :
    Theorem41NonNestingRookStatement M := by
  refine theorem41_of_prec_step (M := M) ?_ hdeg hconst
  intro w k _hconstw hlast hprefix_prec
  by_cases hk : k + 1 < w.deleteFinal.length
  · exact theorem41NonconstantStep_prec_of_matrixClaim
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hclaim hlast hk hP_ne hQ_ne hP_nonneg hG_nonneg
      hQ_nonneg hH_nonneg hprefix_prec hM_nonneg
  · have hsuffix : w.length - (k + 1) = 1 := by
      rw [SnakeWord.length_deleteFinal] at hk
      have hlast_suffix := hlast.succ_lt_length
      lia
    exact theorem41StepOne_prec_of_recurrence
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hP_one hG_one hlast hsuffix hprefix_prec hM_nonneg

/-- Source-matrix induction with the constant branch reduced to the concrete
successor-length identity `M w = P (w.length + 1)`. -/
theorem theorem41_of_matrixClaim_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41MatrixClaimStatement P G)
    (hP_ne : ∀ n, P n ≠ 0)
    (hQ_ne : ∀ {m : ℕ}, 2 ≤ m → narayanaDifference P m ≠ 0)
    (hP_interlaces : ∀ n : ℕ, Interlaces (P n) (P (n + 1)))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (auxiliaryDifference G m))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant →
      M w = P (w.length + 1)) :
    Theorem41NonNestingRookStatement M := by
  have hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) :=
    theorem41_constant_of_matches_succ_length
      (M := M) (P := P) hM_const hP_interlaces
  exact theorem41_of_matrixClaim_of_constant_cases
    (M := M) (P := P) (G := G) hrec hclaim hP_ne hQ_ne hP_one hG_one
    hP_nonneg hG_nonneg hQ_nonneg hH_nonneg hM_nonneg hdeg hconst

/-- The deletion degree bridge follows from the length-indexed degree formula
for the whole snake-word family. -/
theorem theorem41_degree_bridge_of_natDegree_length
    {M : SnakeWord → ℝ[X]}
    (hdegM : ∀ w : SnakeWord, (M w).natDegree = w.length) :
    ∀ {w : SnakeWord}, 1 ≤ w.length →
      (M w.deleteFinal).natDegree + 1 = (M w).natDegree := by
  intro w hw
  rw [hdegM w.deleteFinal, hdegM w, SnakeWord.length_deleteFinal]
  lia

/-- The deletion degree bridge follows from the successor-length degree formula
for the whole snake-word family. -/
theorem theorem41_degree_bridge_of_natDegree_succ_length
    {M : SnakeWord → ℝ[X]}
    (hdegM : ∀ w : SnakeWord, (M w).natDegree = w.length + 1) :
    ∀ {w : SnakeWord}, 1 ≤ w.length →
      (M w.deleteFinal).natDegree + 1 = (M w).natDegree := by
  intro w hw
  rw [hdegM w.deleteFinal, hdegM w, SnakeWord.length_deleteFinal]
  lia

/-- Length-induction route from Claim `(7)` to Braun-Jal Theorem 4.1 with the
constant-word branch reduced to a length-model identity.

This leaves only standard family hypotheses: the Theorem 3.5 recurrence,
Claim `(7)`, adjacent `P`/`G` proper-position statements, the `m = 1`
normalizations, nonnegative coefficients, the degree bridge, consecutive
interlacing of `P`, and the identity `M w = P w.length` on constant words. -/
theorem theorem41_of_claim7_of_constant_matches_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41Claim7Statement P G)
    (hP_interlaces : ∀ {m : ℕ}, 1 ≤ m → Interlaces (P (m - 1)) (P m))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P w.length) :
    Theorem41NonNestingRookStatement M := by
  have hP : ∀ {m : ℕ}, 2 ≤ m → Prec (P (m - 1)) (P m) := by
    intro m hm
    exact (hP_interlaces (m := m)
      (Nat.le_trans (by decide : 1 ≤ 2) hm)).toPrec
  have hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) :=
    theorem41_constant_of_matches_length
      (M := M) (P := P) hM_const hP_interlaces
  intro w hw
  exact theorem41_of_claim7_of_constant_cases
    (M := M) (P := P) (G := G)
    (hrec := hrec) (hclaim := hclaim) (hP := hP) (hG := hG)
    (hP_one := hP_one) (hG_one := hG_one)
    (hP_nonneg := hP_nonneg) (hG_nonneg := hG_nonneg)
    (hM_nonneg := hM_nonneg) (hdeg := hdeg) (hconst := hconst)
    (w := w) hw

/-- Length-induction route from Claim `(7)` to Braun-Jal Theorem 4.1 with the
constant-word branch reduced to a successor-length model identity.

This is the concrete Braun--Jal indexing: a constant word of list length `n`
matches `P (n + 1)`, while final-letter deletion gives the adjacent pair
`P n`, `P (n + 1)`. -/
theorem theorem41_of_claim7_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G)
    (hclaim : Theorem41Claim7Statement P G)
    (hP_interlaces : ∀ n : ℕ, Interlaces (P n) (P (n + 1)))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P (w.length + 1)) :
    Theorem41NonNestingRookStatement M := by
  have hP : ∀ {m : ℕ}, 2 ≤ m → Prec (P (m - 1)) (P m) := by
    intro m hm
    have hm_pos : 1 ≤ m := Nat.le_trans (by decide : 1 ≤ 2) hm
    simpa [Nat.sub_add_cancel hm_pos] using (hP_interlaces (m - 1)).toPrec
  have hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) :=
    theorem41_constant_of_matches_succ_length
      (M := M) (P := P) hM_const hP_interlaces
  intro w hw
  exact theorem41_of_claim7_of_constant_cases
    (M := M) (P := P) (G := G)
    (hrec := hrec) (hclaim := hclaim) (hP := hP) (hG := hG)
    (hP_one := hP_one) (hG_one := hG_one)
    (hP_nonneg := hP_nonneg) (hG_nonneg := hG_nonneg)
    (hM_nonneg := hM_nonneg) (hdeg := hdeg) (hconst := hconst)
    (w := w) hw

/-- Package the Claim `(7)` induction theorem as the abstract route predicate,
with the constant-word branch reduced to a length-model identity. -/
theorem theorem41InductionRoute_of_claim7_of_constant_matches_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hclaim_of_inputs :
      Lemma33AuxiliaryGInterlacesStatement P G →
        Lemma34ModifiedNarayanaInterlacingStatement P →
          Theorem41Claim7Statement P G)
    (hP_interlaces : ∀ {m : ℕ}, 1 ≤ m → Interlaces (P (m - 1)) (P m))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P w.length) :
    Theorem41InductionRouteStatement M P G := by
  intro h33 h34 hrec
  exact theorem41_of_claim7_of_constant_matches_length
    (M := M) (P := P) (G := G)
    (hrec := hrec) (hclaim := hclaim_of_inputs h33 h34)
    (hP_interlaces := hP_interlaces) (hG := hG)
    (hP_one := hP_one) (hG_one := hG_one)
    (hP_nonneg := hP_nonneg) (hG_nonneg := hG_nonneg)
    (hM_nonneg := hM_nonneg) (hdeg := hdeg) (hM_const := hM_const)

/-- Package the Claim `(7)` induction theorem as the abstract route predicate,
with the constant-word branch reduced to the concrete successor-length identity. -/
theorem theorem41InductionRoute_of_claim7_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hclaim_of_inputs :
      Lemma33AuxiliaryGInterlacesStatement P G →
        Lemma34ModifiedNarayanaInterlacingStatement P →
          Theorem41Claim7Statement P G)
    (hP_interlaces : ∀ n : ℕ, Interlaces (P n) (P (n + 1)))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P (w.length + 1)) :
    Theorem41InductionRouteStatement M P G := by
  intro h33 h34 hrec
  exact theorem41_of_claim7_of_constant_matches_succ_length
    (M := M) (P := P) (G := G)
    (hrec := hrec) (hclaim := hclaim_of_inputs h33 h34)
    (hP_interlaces := hP_interlaces) (hG := hG)
    (hP_one := hP_one) (hG_one := hG_one)
    (hP_nonneg := hP_nonneg) (hG_nonneg := hG_nonneg)
    (hM_nonneg := hM_nonneg) (hdeg := hdeg) (hM_const := hM_const)

/-- Section 3 equation `(2)` plus the local Claim `(7)` side conditions give
the abstract induction route, using the concrete successor-length indexing for
constant words.

Claim `(7)` itself uses equation `(2)`, Lemma 3.4, and the bundled side
conditions; Lemma 3.3 remains part of the route interface but is not consumed by
this Claim `(7)` assembly theorem. -/
theorem theorem41InductionRoute_of_section3_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement P G)
    (hside : Theorem41Claim7SideConditions P G)
    (hP_interlaces : ∀ n : ℕ, Interlaces (P n) (P (n + 1)))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P (w.length + 1)) :
    Theorem41InductionRouteStatement M P G :=
  theorem41InductionRoute_of_claim7_of_constant_matches_succ_length
    (M := M) (P := P) (G := G)
    (fun _h33 h34 => theorem41Claim7_of_section3_sideConditions hrec2 h34 hside)
    hP_interlaces hG hP_one hG_one hP_nonneg hG_nonneg hM_nonneg hdeg
    hM_const

/-- Root-sum version of the Section 3 induction route.

This uses the endpoint-compatible Claim `(7)` assembly theorem in place of the
older strict-root-bound route. -/
theorem theorem41InductionRoute_of_section3_rootSum_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement P G)
    (hside : Theorem41Claim7RootSumSideConditions P G)
    (hP_interlaces : ∀ n : ℕ, Interlaces (P n) (P (n + 1)))
    (hG : ∀ {m : ℕ}, 2 ≤ m → Prec (G (m - 1)) (G m))
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant → M w = P (w.length + 1)) :
    Theorem41InductionRouteStatement M P G :=
  theorem41InductionRoute_of_claim7_of_constant_matches_succ_length
    (M := M) (P := P) (G := G)
    (fun _h33 h34 =>
      theorem41Claim7_of_section3_rootSumSideConditions hrec2 h34 hside)
    hP_interlaces hG hP_one hG_one hP_nonneg hG_nonneg hM_nonneg hdeg
    hM_const

end GeneralizedSnakePosets
end RealRooted
