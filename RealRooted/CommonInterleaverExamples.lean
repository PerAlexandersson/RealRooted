import RealRooted.CommonInterleaverTwo

open Polynomial

noncomputable section

namespace RealRooted

namespace CommonInterleaverExamples

private lemma xAddOne_isRealRooted : ((X + 1 : ℝ[X]) ≠ 0 ∧ (X + 1 : ℝ[X]).Splits) := by
  simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-1 : ℝ)

private lemma xAddOne_hasNonnegCoeffs : HasNonnegCoeffs (X + 1 : ℝ[X]) :=
  hasNonnegCoeffs_X_add_one

private lemma xAddOne_hasPosLeadingCoeff : HasPosLeadingCoeff (X + 1 : ℝ[X]) := by
  simpa using hasPosLeadingCoeff_X_add_C (1 : ℝ)

private lemma xAddOne_natDegree :
    (X + 1 : ℝ[X]).natDegree = 1 := by
  simp

private lemma xAddTwo_natDegree :
    (X + 2 : ℝ[X]).natDegree = 1 := by
  change ((X + C (2 : ℝ) : ℝ[X]).natDegree = 1)
  simp

private lemma xAddTwo_isRealRooted : ((X + 2 : ℝ[X]) ≠ 0 ∧ (X + 2 : ℝ[X]).Splits) :=
  isRealRooted_of_degree_one xAddTwo_natDegree

private lemma xAddTwo_hasNonnegCoeffs : HasNonnegCoeffs (X + 2 : ℝ[X]) := by
  change HasNonnegCoeffs (X + C (2 : ℝ) : ℝ[X])
  exact hasNonnegCoeffs_X_add_C (by norm_num)

private lemma xAddOne_roots :
    (X + 1 : ℝ[X]).roots = {(-1 : ℝ)} := by
  simpa [sub_eq_add_neg, add_comm] using (roots_X_sub_C (-1 : ℝ))

private lemma xAddTwo_roots :
    (X + 2 : ℝ[X]).roots = {(-2 : ℝ)} := by
  change ((X + C (2 : ℝ) : ℝ[X]).roots = {(-2 : ℝ)})
  simp

private lemma xAddThree_natDegree :
    (X + 3 : ℝ[X]).natDegree = 1 := by
  change ((X + C (3 : ℝ) : ℝ[X]).natDegree = 1)
  simp

private lemma xAddThree_isRealRooted : ((X + 3 : ℝ[X]) ≠ 0 ∧ (X + 3 : ℝ[X]).Splits) := by
  change ((X + C (3 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (3 : ℝ) : ℝ[X]).Splits)
  simpa [sub_eq_add_neg, add_comm] using isRealRooted_X_sub_C (-3 : ℝ)

private lemma xAddThree_hasNonnegCoeffs : HasNonnegCoeffs (X + 3 : ℝ[X]) := by
  change HasNonnegCoeffs (X + C (3 : ℝ) : ℝ[X])
  exact hasNonnegCoeffs_X_add_C (by norm_num)

private lemma xAddThree_roots :
    (X + 3 : ℝ[X]).roots = {(-3 : ℝ)} := by
  change ((X + C (3 : ℝ) : ℝ[X]).roots = {(-3 : ℝ)})
  simp

private lemma xAddFiveHalves_isRealRooted :
    ((X + C (5 / 2 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (5 / 2 : ℝ) : ℝ[X]).Splits) := by
  simpa [sub_eq_add_neg, add_comm] using isRealRooted_X_sub_C (-(5 / 2 : ℝ))

private lemma xSq_add_fiveX_add_six_isRealRooted :
    ((((X + 2) * (X + 3)) : ℝ[X]) ≠ 0 ∧ (((X + 2) * (X + 3)) : ℝ[X]).Splits) :=
  isRealRooted_mul xAddTwo_isRealRooted.1 xAddTwo_isRealRooted.2
    xAddThree_isRealRooted.1 xAddThree_isRealRooted.2

private lemma xSq_add_fiveX_add_six_hasNonnegCoeffs :
    HasNonnegCoeffs (((X + 2) * (X + 3)) : ℝ[X]) :=
  xAddTwo_hasNonnegCoeffs.mul xAddThree_hasNonnegCoeffs

private lemma xSq_add_fiveX_add_six_hasPosLeadingCoeff :
    HasPosLeadingCoeff (((X + 2) * (X + 3)) : ℝ[X]) :=
  xSq_add_fiveX_add_six_hasNonnegCoeffs.pos_leadingCoeff
    xSq_add_fiveX_add_six_isRealRooted.1

private lemma xSq_add_fiveX_add_six_natDegree :
    (((X + 2) * (X + 3)) : ℝ[X]).natDegree = 2 := by
  simp [natDegree_mul xAddTwo_isRealRooted.1 xAddThree_isRealRooted.1, xAddTwo_natDegree,
    xAddThree_natDegree]

private lemma xSq_add_fiveX_add_six_roots :
    (((X + 2) * (X + 3)) : ℝ[X]).roots = {(-3 : ℝ)} + {(-2 : ℝ)} := by
  rw [roots_mul (mul_ne_zero xAddTwo_isRealRooted.1 xAddThree_isRealRooted.1),
    xAddTwo_roots, xAddThree_roots]
  grind

private lemma xAddFiveHalves_strictInterl_xAddOne :
    StrictInterl (X + C (5 / 2 : ℝ) : ℝ[X]) (X + 1) := by
  refine
    ⟨xAddFiveHalves_isRealRooted, xAddOne_isRealRooted, [(-(5 / 2 : ℝ))], [(-1 : ℝ)],
      List.pairwise_singleton _ _, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp
  · simpa using xAddOne_roots.symm
  · exact Or.inr ⟨by simp, by norm_num [ListAlternates, ListInterlaces]⟩

private lemma xAddFiveHalves_strictInterl_xSq_add_fiveX_add_six :
    StrictInterl (X + C (5 / 2 : ℝ) : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) := by
  refine
    ⟨xAddFiveHalves_isRealRooted, xSq_add_fiveX_add_six_isRealRooted, [(-(5 / 2 : ℝ))],
      [(-3 : ℝ), (-2 : ℝ)], List.pairwise_singleton _ _, ?_, ?_, ?_, ?_⟩
  · norm_num
  · simp
  · rw [xSq_add_fiveX_add_six_roots]
    rfl
  · exact Or.inl ⟨by simp, by norm_num [ListInterlaces]⟩

/-- The quadratic pair `(X + 1, (X + 2)(X + 3))` still satisfies the positive-
combination hypothesis: the common left interleaver `X + 5/2` witnesses the
restricted Obreschkoff condition directly. -/
lemma xAddOne_xSq_add_fiveX_add_six_posComboRealRooted :
    PosComboRealRooted (X + 1 : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) :=
  PosComboRealRooted.of_commonLeftInterleaver
    xAddFiveHalves_strictInterl_xAddOne
    xAddFiveHalves_strictInterl_xSq_add_fiveX_add_six
      xAddOne_hasPosLeadingCoeff
      xSq_add_fiveX_add_six_hasPosLeadingCoeff

private lemma xAddOne_xSq_add_fiveX_add_six_noCommon :
    ∀ r, (X + 1 : ℝ[X]).IsRoot r → ¬ (((X + 2) * (X + 3)) : ℝ[X]).IsRoot r := by
  intro r hroot1 hroot2
  simp_all
  grind

private lemma xAddOne_xSq_add_fiveX_add_six_not_strictInterl :
    ¬ StrictInterl (X + 1 : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) := by
  intro hstrictInterl
  rcases hstrictInterl with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_card : (X + 1 : ℝ[X]).roots.card = 1 := by
    simpa [xAddOne_natDegree] using card_roots_of_splits hf.2
  have hrs_card : (((X + 2) * (X + 3)) : ℝ[X]).roots.card = 2 := by
    simpa [xSq_add_fiveX_add_six_natDegree] using card_roots_of_splits hg.2
  have hss_len : ss.length = 1 := by rw [← Multiset.coe_card, hss_eq, hss_card]
  have hrs_len : rs.length = 2 := by rw [← Multiset.coe_card, hrs_eq, hrs_card]
  cases ss with
  | nil =>
      simp at hss_len
  | cons s ss' =>
      cases ss' with
      | nil =>
          cases rs with
          | nil =>
              simp at hrs_len
          | cons r₁ rs' =>
              cases rs' with
              | nil =>
                  simp at hrs_len
              | cons r₂ rs'' =>
                  cases rs'' with
                  | nil =>
                      have hs_eq : s = -1 := by
                        have hs_mem : (-1 : ℝ) ∈ (X + 1 : ℝ[X]).roots := by simp_all
                        have hs_mem' :
                            (-1 : ℝ) ∈ (([s] : List ℝ) : Multiset ℝ) := by
                          lia
                        have hs_mem'' : (-1 : ℝ) ∈ ([s] : List ℝ) :=
                          Multiset.mem_coe.mp hs_mem'
                        simp_all
                      have hr_negThree_mem :
                          (-3 : ℝ) ∈ (((X + 2) * (X + 3)) : ℝ[X]).roots := by
                        simp_all
                      have hr_negTwo_mem :
                          (-2 : ℝ) ∈ (((X + 2) * (X + 3)) : ℝ[X]).roots := by
                        simp_all
                      have hr_negThree_mem' :
                          (-3 : ℝ) ∈ (([r₁, r₂] : List ℝ) : Multiset ℝ) := by
                        lia
                      have hr_negTwo_mem' :
                          (-2 : ℝ) ∈ (([r₁, r₂] : List ℝ) : Multiset ℝ) := by
                        lia
                      have hr1_or_hr2_negThree : r₁ = -3 ∨ r₂ = -3 := by
                        have hr_negThree_mem'' : (-3 : ℝ) ∈ ([r₁, r₂] : List ℝ) :=
                          Multiset.mem_coe.mp hr_negThree_mem'
                        grind
                      have hr1_or_hr2_negTwo : r₁ = -2 ∨ r₂ = -2 := by
                        have hr_negTwo_mem'' : (-2 : ℝ) ∈ ([r₁, r₂] : List ℝ) :=
                          Multiset.mem_coe.mp hr_negTwo_mem'
                        grind
                      have hr1_le_r2 : r₁ ≤ r₂ := by simp_all
                      have hr1_eq : r₁ = -3 := by grind
                      have hr2_eq : r₂ = -2 := by simp_all
                      have hinter : ListInterlaces [s] [r₁, r₂] := by lia
                      have : False := by simp [hs_eq, hr1_eq, hr2_eq, ListInterlaces] at hinter
                      lia
                  | cons r₃ rs''' =>
                      simp at hrs_len
      | cons s₂ ss'' =>
          simp at hss_len

/-- The honest succ-degree orientation target is false as well: the pair
`X + 1, (X + 2)(X + 3)` satisfies the positive-combo/no-common hypotheses and
even has a concrete common interleaver `X + 5/2`, but both quadratic roots lie
strictly to the left of `-1`, so `StrictInterl (X + 1) ((X + 2)(X + 3))` fails. -/
lemma not_posComboNoCommonSuccDegreeOrientationNonnegStatement :
    ¬ PosComboNoCommonSuccDegreeOrientationNonnegStatement :=
  fun hsucc =>
    xAddOne_xSq_add_fiveX_add_six_not_strictInterl
      (hsucc
        xAddOne_hasPosLeadingCoeff
        xSq_add_fiveX_add_six_hasPosLeadingCoeff
        xAddOne_hasNonnegCoeffs
        xSq_add_fiveX_add_six_hasNonnegCoeffs
        xAddOne_xSq_add_fiveX_add_six_posComboRealRooted
        (by simp [xSq_add_fiveX_add_six_natDegree])
        xAddOne_xSq_add_fiveX_add_six_noCommon)

/-- The nonnegative-coefficient negative right-pencil target is false.  The
same pair `X + 1, (X + 2)(X + 3)` is compatible and has nonnegative
coefficients, but the negative pencil member at `μ = -1` is a quadratic with
negative discriminant. -/
lemma not_compatibleSuccDegreeNegativeRightFamilyNonnegStatement :
    ¬ CompatibleSuccDegreeNegativeRightFamilyNonnegStatement := by
  intro hneg
  have hcomp : Compatible (X + 1 : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) :=
    Compatible.of_posComboRealRooted
      xAddOne_xSq_add_fiveX_add_six_posComboRealRooted
      xAddOne_isRealRooted
      xSq_add_fiveX_add_six_isRealRooted
  have hsplits :
      ((X + 1 : ℝ[X]) + C (-1 : ℝ) * (((X + 2) * (X + 3)) : ℝ[X])).Splits :=
    hneg hcomp
      xAddOne_hasPosLeadingCoeff
      xSq_add_fiveX_add_six_hasPosLeadingCoeff
      xAddOne_hasNonnegCoeffs
      xSq_add_fiveX_add_six_hasNonnegCoeffs
      (by simp [xSq_add_fiveX_add_six_natDegree])
      xAddOne_isRealRooted.2
      (-1 : ℝ) (by norm_num)
  have hp_eq :
      ((X + 1 : ℝ[X]) + C (-1 : ℝ) * (((X + 2) * (X + 3)) : ℝ[X])) =
        C (-1 : ℝ) * X ^ 2 + C (-4 : ℝ) * X + C (-5 : ℝ) := by
    ext n
    cases n with
    | zero =>
        norm_num [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
    | succ n =>
        cases n with
        | zero =>
            norm_num [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
              coeff_X, coeff_one]
        | succ n =>
            cases n with
            | zero =>
                norm_num [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
                  coeff_X, coeff_one]
            | succ n =>
                norm_num [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
                  coeff_X, coeff_one]
  have hdeg :
      ((X + 1 : ℝ[X]) + C (-1 : ℝ) * (((X + 2) * (X + 3)) : ℝ[X])).natDegree = 2 := by
    rw [hp_eq]
    exact Polynomial.natDegree_quadratic (by norm_num : (-1 : ℝ) ≠ 0)
  have hdisc := quadratic_disc_coeff_le_of_splits_natDegree_two hdeg hsplits
  rw [hp_eq] at hdisc
  norm_num [coeff_X, pow_two] at hdisc

/-- The coefficient-free negative right-pencil shortcut is false, already for
the nonnegative-coefficient counterexample above. -/
lemma not_compatibleSuccDegreeNegativeRightFamilyStatement :
    ¬ CompatibleSuccDegreeNegativeRightFamilyStatement :=
  fun hneg =>
    not_compatibleSuccDegreeNegativeRightFamilyNonnegStatement
      (fun {f g} hcomp hf_pos hg_pos _ _ hdeg hf_split μ hμ =>
        hneg (f := f) (g := g) hcomp hf_pos hg_pos hdeg hf_split μ hμ)

/-- The coefficient-free all-combinations shortcut is false, because it would
imply the negative right-pencil shortcut. -/
lemma not_compatibleSuccDegreeAllComboStatement :
    ¬ CompatibleSuccDegreeAllComboStatement :=
  fun hall =>
    not_compatibleSuccDegreeNegativeRightFamilyStatement
      (compatibleSuccDegreeNegativeRightFamily_of_allCombo hall)

/-! ### The general no-common orientation statement is false

The named `PosComboNoCommonOrientationStatement` (with the weaker conclusion
`StrictInterl f g ∨ StrictInterl g f`, and no nonnegative-coefficient hypothesis) is also
false.  Witnesses: `f = (X - 1)(X + 1) = X^2 - 1` and
`g = (X - 2)(X + 2) = X^2 - 4`.  Every positive combination
`lambda * f + mu * g = (lambda + mu) * X^2 - (lambda + 4 * mu)` is
real-rooted; the pair has no common roots; but `g`'s roots strictly nest
`f`'s roots, so neither orientation holds. -/

/-! ### The residual succ-degree orientation target is false

The residual branch of the succ-degree no-common orientation problem
(`PosComboNoCommonSuccDegreeRootCountResidualStrictInterlStatement`) additionally
assumes `f.coeff 0 = 0` and `g.coeff 0 ≠ 0`.  It is false: take `f = X` and
`g = (X + 1)(X + 2)`.  A common left interleaver `X + 3/2` witnesses the
positive-combination condition, but `0`, the only root of `X`, lies strictly to
the right of both roots of `g`, so `StrictInterl X g` fails. -/

end CommonInterleaverExamples

end RealRooted
