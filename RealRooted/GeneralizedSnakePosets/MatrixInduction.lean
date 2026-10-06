import RealRooted.GeneralizedSnakePosets.Statements
import RealRooted.MatrixInterlacing
import RealRooted.PFPolynomial

/-!
# Braun-Jal matrix-induction step

This module isolates the local two-row matrix step used in Braun--Jal's proof
of the snake interlacing theorem (arXiv:2607.00922v1, p. 10).  The source matrix has rows
`[P_{m-1}, G_{m-1}]` and `[Q_m, H_m]`, where `Q_m = P_m - P_{m-1}` and
`H_m = G_m - G_{m-1}`, and acts on the induction pair `[f, X * g]`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The two-row matrix for one snake-interlacing induction step. -/
def snakeInterlacingStepMatrix (P G : ℕ → ℝ[X]) (m : ℕ) : List (List ℝ[X]) :=
  [[P (m - 1), G (m - 1)],
    [narayanaDifference P m, auxiliaryDifference G m]]

@[simp] theorem snakeInterlacingStepMatrix_length (P G : ℕ → ℝ[X]) (m : ℕ) :
    (snakeInterlacingStepMatrix P G m).length = 2 := by
  simp [snakeInterlacingStepMatrix]

/-- Each row of the Braun-Jal step matrix has length two. -/
theorem snakeInterlacingStepMatrix_rect (P G : ℕ → ℝ[X]) (m : ℕ) :
    ∀ row ∈ snakeInterlacingStepMatrix P G m, row.length = 2 := by
  intro row hrow
  have hrow' :
      row = [P (m - 1), G (m - 1)] ∨
        row = [narayanaDifference P m, auxiliaryDifference G m] := by
    simpa [snakeInterlacingStepMatrix] using hrow
  rcases hrow' with rfl | rfl <;> simp

/-- Entrywise nonnegativity for the Braun-Jal step matrix. -/
theorem snakeInterlacingStepMatrix_entry_nonneg {P G : ℕ → ℝ[X]} {m : ℕ}
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : HasNonnegCoeffs (auxiliaryDifference G m)) :
    ∀ row ∈ snakeInterlacingStepMatrix P G m, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  have hrow' :
      row = [P (m - 1), G (m - 1)] ∨
        row = [narayanaDifference P m, auxiliaryDifference G m] := by
    simpa [snakeInterlacingStepMatrix] using hrow
  rcases hrow' with rfl | rfl
  · have hp' : p = P (m - 1) ∨ p = G (m - 1) := by simpa using hp
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
theorem snakeInterlacingStepMatrix_action_pair
    (P G : ℕ → ℝ[X]) (m : ℕ) (f g : ℝ[X]) :
    matPolyAction (snakeInterlacingStepMatrix P G m) [f, X * g] =
      [f * P (m - 1) + X * g * G (m - 1),
        f * narayanaDifference P m + X * g * auxiliaryDifference G m] := by
  simp [snakeInterlacingStepMatrix, matPolyAction, mul_comm, mul_left_comm]

/-- The induction hypothesis `g << f` makes `[f, X * g]` a nonnegative
interlacing input sequence. -/
theorem snakeInterlacingInputPair_interlacingSeqNonneg {f g : ℝ[X]}
    (hgf : StrictInterl g f) (hf_nonneg : HasNonnegCoeffs f)
    (hg_nonneg : HasNonnegCoeffs g) :
    IsInterlacingSeqNonneg [f, X * g] := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp' : p = f ∨ p = X * g := by simpa using hp
    rcases hp' with rfl | rfl
    · exact ⟨⟨hgf.2.1.1, hgf.2.1.2⟩, hf_nonneg⟩
    · exact ⟨isRealRooted_X_mul hgf.1.1 hgf.1.2, hg_nonneg.X_mul⟩
  · rw [isInterlacingSeq_iff_pairwise]
    simp [strictInterl_mul_X_of_strictInterl_of_nonneg hgf hg_nonneg hf_nonneg]

/-- The difference interlacing claim is exactly the cross `2 x 2` affine test for the source matrix
in Braun--Jal's proof of the snake interlacing theorem. -/
theorem snakeInterlacingStepMatrix_cross_has2x2_of_differenceInterlacing
    {P G : ℕ → ℝ[X]} (hclaim : SnakeDifferenceInterlacing P G)
    {m : ℕ} (hm : 2 ≤ m) :
    Has2x2InterlacingProperty (P (m - 1)) (G (m - 1))
      (narayanaDifference P m) (auxiliaryDifference G m) := by
  intro s t hs ht
  exact hclaim hm hs.le ht.le

/-- The difference interlacing claim and the source matrix send the induction pair to a interlacing
pair.  Repeated column indices use the real-rootedness already contained in the
same difference-interlacing instance. -/
theorem snakeInterlacingStep_difference_strictInterl_of_differenceInterlacing
    {P G : ℕ → ℝ[X]} {m : ℕ} {f g : ℝ[X]}
    (hclaim : SnakeDifferenceInterlacing P G) (hm : 2 ≤ m)
    (hP_ne : P (m - 1) ≠ 0)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : HasNonnegCoeffs (auxiliaryDifference G m))
    (hgf : StrictInterl g f)
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g) :
    StrictInterl (f * P (m - 1) + X * g * G (m - 1))
      (f * narayanaDifference P m + X * g * auxiliaryDifference G m) := by
  have hQ_ne : narayanaDifference P m ≠ 0 := by
    have hzero := hclaim (m := m) (lam := 0) (mu := 0) hm (by norm_num) (by norm_num)
    simpa using hzero.2.1.1
  have hpair := strictInterl_zipWith_sum_pair_of_2x2
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
        simpa using StrictInterl.refl hcross.2.1.1 hcross.2.1.2
      · simpa using snakeInterlacingStepMatrix_cross_has2x2_of_differenceInterlacing hclaim hm
      · simp at hj
      · intro s t hs ht
        have hcross := hclaim (m := m) (lam := s) (mu := t) hm hs.le ht.le
        simpa using StrictInterl.refl hcross.1.1 hcross.1.2)
    (hfs_len := by simp)
    (hfs := snakeInterlacingInputPair_interlacingSeqNonneg hgf hf_nonneg hg_nonneg)
  simpa [mul_comm, mul_left_comm] using hpair

/-- The nonconstant Braun--Jal induction step through the source
`[P, G; Q, H]` matrix.  This is the argument on p. 10 of the paper and
requires no adjacent-`G` interlacing. -/
theorem snakeInterlacingNonconstantStep_strictInterl_of_differenceInterlacing
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]} {w : SnakeWord} {k : ℕ}
    (hrec : GeneralizedSnakeRecurrence M P G)
    (hclaim : SnakeDifferenceInterlacing P G)
    (hlast : w.IsLastChangeIndex k)
    (hk : k + 1 < w.deleteFinal.length)
    (hP_ne : ∀ n, P n ≠ 0)
    (hP_nonneg : ∀ n, HasNonnegCoeffs (P n))
    (hG_nonneg : ∀ n, HasNonnegCoeffs (G n))
    (hQ_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (narayanaDifference P m))
    (hH_nonneg : ∀ {m : ℕ}, 2 ≤ m →
      HasNonnegCoeffs (auxiliaryDifference G m))
    (hprefix : StrictInterl (M (w.takePrefix k)) (M (w.takePrefix (k + 1))))
    (hM_nonneg : ∀ u, HasNonnegCoeffs (M u)) :
    StrictInterl (M w.deleteFinal) (M w) := by
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
  have hstep : StrictInterl (M w.deleteFinal) (M w - M w.deleteFinal) := by
    have hstep_raw := snakeInterlacingStep_difference_strictInterl_of_differenceInterlacing
      hclaim hm (hP_ne (m - 1)) hP_nonneg hG_nonneg
      (hQ_nonneg hm) (hH_nonneg hm) hprefix hf_nonneg hg_nonneg
    rw [← hrec_del, ← hrec_diff] at hstep_raw
    exact hstep_raw
  have hsum0 : Interl (M w.deleteFinal)
      (M w.deleteFinal + (M w - M w.deleteFinal)) :=
    interl_add_right_of_common_left_of_nonneg
      (Interl.refl fun _ => hstep.1.2) hstep.toInterl
      (hM_nonneg w.deleteFinal) hdiff_nonneg
  have hsum_ne : M w.deleteFinal + (M w - M w.deleteFinal) ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      (hM_nonneg w.deleteFinal) hdiff_nonneg hstep.2.1.1
  have hfinal := hsum0.toStrictInterl_of_ne hstep.1.1 hsum_ne
  have hsum_eq : M w.deleteFinal + (M w - M w.deleteFinal) = M w := by ring
  rw [hsum_eq] at hfinal
  exact hfinal

/-- Polynomial form of the exceptional `m = 1` Braun-Jal step.

If `g ≪ f` and both polynomials have nonnegative coefficients, then
`f ≪ (1 + X) f + X g`. -/
theorem snakeInterlacingStepOne_strictInterl_of_strictInterl_nonneg {f g : ℝ[X]}
    (hgf : StrictInterl g f)
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g) :
    StrictInterl f ((1 + X) * f + X * g) := by
  have hf_Xg : StrictInterl f (X * g) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hgf hg_nonneg hf_nonneg
  have hsum_nonneg : HasNonnegCoeffs (f + X * g) :=
    hf_nonneg.add hg_nonneg.X_mul
  have haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + (f + X * g)) ≠ 0 ∧
          (((C s * X + C t) * f) + (f + X * g)).Splits) := by
    intro s t hs ht
    have ht_one : 0 < t + 1 := by linarith
    have hbase :=
      isRealRooted_affine_combo_of_strictInterl_nonneg
        hf_Xg hf_nonneg hg_nonneg.X_mul hs ht_one
    have hrew :
        ((C s * X + C t) * f + (f + X * g)) =
          ((C s * X + C (t + 1)) * f + X * g) := by
      simp only [map_add, map_one]
      ring
    rwa [hrew]
  have hshift :=
    strictInterl_shifted_pair_of_affine_family_nonneg
      (f := f) (g := f + X * g) hgf.2.1.1 hf_nonneg hsum_nonneg haff
  simpa [left_distrib, right_distrib, mul_assoc, add_assoc, add_left_comm,
    add_comm] using hshift

/-- Word-level form of the exceptional `m = 1` Braun-Jal recurrence step.

When the final constant suffix has length one, the snake recurrence rewrites `M w` as
`(1 + X) f + X g`, while `w.deleteFinal` is the prefix carrying `f`. -/
theorem snakeInterlacingStepOne_strictInterl_of_recurrence
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]} {w : SnakeWord} {k : ℕ}
    (hrec : GeneralizedSnakeRecurrence M P G)
    (hP_one : P 1 = 1 + X) (hG_one : G 1 = 1)
    (hlast : w.IsLastChangeIndex k)
    (hsuffix : w.length - (k + 1) = 1)
    (hprefix : StrictInterl (M (w.takePrefix k)) (M (w.takePrefix (k + 1))))
    (hM_nonneg : ∀ u, HasNonnegCoeffs (M u)) :
    StrictInterl (M w.deleteFinal) (M w) := by
  let f : ℝ[X] := M (w.takePrefix (k + 1))
  let g : ℝ[X] := M (w.takePrefix k)
  have hdel : w.deleteFinal = w.takePrefix (k + 1) :=
    SnakeWord.deleteFinal_eq_takePrefix_succ_of_length_sub_eq_one hsuffix
  have hrec_w : M w = (1 + X) * f + X * g := by
    dsimp [f, g]
    rw [hrec hlast.not_isConstant hlast, hsuffix, hP_one, hG_one]
    ring
  have hstep := snakeInterlacingStepOne_strictInterl_of_strictInterl_nonneg
    (f := f) (g := g) hprefix
    (hM_nonneg (w.takePrefix (k + 1))) (hM_nonneg (w.takePrefix k))
  rwa [hdel, hrec_w]

/-- Length-induction skeleton for the snake interlacing theorem.

If every nonconstant word step turns the prefix induction hypothesis into
`StrictInterl (M w.deleteFinal) (M w)`, then constant words and the degree bridge
finish the full deletion-interlacing statement. -/
theorem snakeInterlacing_of_strictInterl_step
    {M : SnakeWord → ℝ[X]}
    (hstep :
      ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
        StrictInterl (M (w.takePrefix k)) (M (w.takePrefix (k + 1))) →
          StrictInterl (M w.deleteFinal) (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w)) :
    NonNestingRookInterlacing M := by
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
          have hprefix_strictInterl :
              StrictInterl (M (w.takePrefix k)) (M (w.takePrefix (k + 1))) := by
            rw [← SnakeWord.deleteFinal_takePrefix_succ_of_lt hlast.index_lt_length]
            exact hprefix_result.2.toStrictInterl
          have hstrictInterl := hstep hconstw hlast hprefix_strictInterl
          have hinter : Interlaces (M w.deleteFinal) (M w) :=
            hstrictInterl.toInterlaces (hdeg hw)
          exact ⟨hinter.1, hinter⟩
  intro w hw
  exact hmain w.length w rfl hw

/-- Constant-word branch from a successor-length model identity.

This is the indexing used by the concrete Braun--Jal snake boards: the empty
word already gives the first modified Narayana polynomial, so a constant word
of list length `n` evaluates to `P (n + 1)`. -/
theorem snakeInterlacing_constant_of_matches_succ_length
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
  have hright : M w ≠ 0 ∧ (M w).Splits := by simpa [hM_const (w := w) hconstw] using hinter.1
  have hinter_M : Interlaces (M w.deleteFinal) (M w) := by
    rw [hM_const (w := w) hconstw]
    rw [hM_const (w := w.deleteFinal) hdel_const]
    rw [hlen_del]
    exact hinter
  exact ⟨hright, hinter_M⟩

/-- Source-matrix length induction from the difference interlacing claim to the snake interlacing
theorem.

The long-suffix branch uses the displayed `[P, G; Q, H]` matrix, while the
suffix-one branch uses `P_1 = 1 + X` and `G_1 = 1`.  In particular, no
adjacent-`G` interlacing hypothesis occurs. -/
theorem snakeInterlacing_of_differenceInterlacing_of_constant_cases
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : GeneralizedSnakeRecurrence M P G)
    (hclaim : SnakeDifferenceInterlacing P G)
    (hP_ne : ∀ n, P n ≠ 0)
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
    NonNestingRookInterlacing M := by
  refine snakeInterlacing_of_strictInterl_step (M := M) ?_ hdeg hconst
  intro w k _hconstw hlast hprefix_strictInterl
  by_cases hk : k + 1 < w.deleteFinal.length
  · exact snakeInterlacingNonconstantStep_strictInterl_of_differenceInterlacing
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hclaim hlast hk hP_ne hP_nonneg hG_nonneg
      hQ_nonneg hH_nonneg hprefix_strictInterl hM_nonneg
  · have hsuffix : w.length - (k + 1) = 1 := by
      rw [SnakeWord.length_deleteFinal] at hk
      have hlast_suffix := hlast.succ_lt_length
      lia
    exact snakeInterlacingStepOne_strictInterl_of_recurrence
      (M := M) (P := P) (G := G) (w := w) (k := k)
      hrec hP_one hG_one hlast hsuffix hprefix_strictInterl hM_nonneg

/-- Source-matrix induction with the constant branch reduced to the concrete
successor-length identity `M w = P (w.length + 1)`. -/
theorem snakeInterlacing_of_differenceInterlacing_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : GeneralizedSnakeRecurrence M P G)
    (hclaim : SnakeDifferenceInterlacing P G)
    (hP_ne : ∀ n, P n ≠ 0)
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
    NonNestingRookInterlacing M := by
  have hconst :
      ∀ {w : SnakeWord}, 1 ≤ w.length → w.IsConstant →
        (M w ≠ 0 ∧ (M w).Splits) ∧ Interlaces (M w.deleteFinal) (M w) :=
    snakeInterlacing_constant_of_matches_succ_length
      (M := M) (P := P) hM_const hP_interlaces
  intro w hw
  exact snakeInterlacing_of_differenceInterlacing_of_constant_cases
    (M := M) (P := P) (G := G) hrec hclaim hP_ne hP_one hG_one
    hP_nonneg hG_nonneg hQ_nonneg hH_nonneg hM_nonneg hdeg hconst
    (w := w) hw

end GeneralizedSnakePosets
end RealRooted
