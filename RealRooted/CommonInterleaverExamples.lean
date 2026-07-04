import RealRooted.CommonInterleaverTwo

open Polynomial

noncomputable section

namespace RealRooted

namespace CommonInterleaverExamples

/-- A tiny concrete family used to regression-test the finite-list
Chudnovsky--Seymour wrappers. All members are positive scalar multiples of the
same linear polynomial, so a common interleaver is completely explicit. -/
def scaledLinearFamily : List ℝ[X] :=
  [X + 1, C (2 : ℝ) * (X + 1), C (3 : ℝ) * (X + 1)]

private lemma xAddOne_isRealRooted : ((X + 1 : ℝ[X]) ≠ 0 ∧ (X + 1 : ℝ[X]).Splits) := by
  simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-1 : ℝ)

private lemma xAddOne_hasNonnegCoeffs : HasNonnegCoeffs (X + 1 : ℝ[X]) := by
  exact hasNonnegCoeffs_X_add_one

private lemma xAddOne_hasPosLeadingCoeff : HasPosLeadingCoeff (X + 1 : ℝ[X]) := by
  simpa using hasPosLeadingCoeff_X_add_C (1 : ℝ)

private lemma twoMul_xAddOne_isRealRooted :
    ((C (2 : ℝ) * (X + 1)) ≠ 0 ∧ (C (2 : ℝ) * (X + 1)).Splits) :=
  isRealRooted_C_mul xAddOne_isRealRooted.1 xAddOne_isRealRooted.2 (by simp)

private lemma threeMul_xAddOne_isRealRooted :
    ((C (3 : ℝ) * (X + 1)) ≠ 0 ∧ (C (3 : ℝ) * (X + 1)).Splits) :=
  isRealRooted_C_mul xAddOne_isRealRooted.1 xAddOne_isRealRooted.2 (by simp)

private lemma twoMul_xAddOne_hasPosLeadingCoeff :
    HasPosLeadingCoeff (C (2 : ℝ) * (X + 1)) :=
  hasPosLeadingCoeff_C_mul (by simp) xAddOne_hasPosLeadingCoeff

private lemma threeMul_xAddOne_hasPosLeadingCoeff :
    HasPosLeadingCoeff (C (3 : ℝ) * (X + 1)) :=
  hasPosLeadingCoeff_C_mul (by simp) xAddOne_hasPosLeadingCoeff

private lemma twoMul_xAddOne_hasNonnegCoeffs :
    HasNonnegCoeffs (C (2 : ℝ) * (X + 1)) :=
  nonnegCoeffs_C_mul (by simp) xAddOne_hasNonnegCoeffs

private lemma threeMul_xAddOne_hasNonnegCoeffs :
    HasNonnegCoeffs (C (3 : ℝ) * (X + 1)) :=
  nonnegCoeffs_C_mul (by simp) xAddOne_hasNonnegCoeffs

lemma scaledLinearFamily_isRealRooted :
    ∀ f ∈ scaledLinearFamily, (f ≠ 0 ∧ f.Splits) := by
  intro f hf
  simp only [scaledLinearFamily, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact xAddOne_isRealRooted
  · exact twoMul_xAddOne_isRealRooted
  · exact threeMul_xAddOne_isRealRooted

lemma scaledLinearFamily_hasPosLeadingCoeff :
    ∀ f ∈ scaledLinearFamily, HasPosLeadingCoeff f := by
  intro f hf
  simp only [scaledLinearFamily, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact xAddOne_hasPosLeadingCoeff
  · exact twoMul_xAddOne_hasPosLeadingCoeff
  · exact threeMul_xAddOne_hasPosLeadingCoeff

lemma scaledLinearFamily_hasNonnegCoeffs :
    ∀ f ∈ scaledLinearFamily, HasNonnegCoeffs f := by
  intro f hf
  simp only [scaledLinearFamily, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact xAddOne_hasNonnegCoeffs
  · exact twoMul_xAddOne_hasNonnegCoeffs
  · exact threeMul_xAddOne_hasNonnegCoeffs

/-- The common interleaver is just `X + 1` itself. -/
lemma scaledLinearFamily_commonInterleaver :
    HasCommonInterleaver scaledLinearFamily := by
  refine ⟨X + 1, ?_⟩
  intro f hf
  simp only [scaledLinearFamily, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact prec_refl xAddOne_isRealRooted.1 xAddOne_isRealRooted.2
  · exact prec_C_mul_self xAddOne_isRealRooted.1 xAddOne_isRealRooted.2 (by simp)
  · exact prec_C_mul_self xAddOne_isRealRooted.1 xAddOne_isRealRooted.2 (by simp)

lemma scaledLinearFamily_pairwiseCompatible :
    PairwiseCompatible scaledLinearFamily :=
  pairwiseCompatible_of_commonInterleaver
    scaledLinearFamily_commonInterleaver
    scaledLinearFamily_hasPosLeadingCoeff

lemma scaledLinearFamily_familyCompatible :
    FamilyCompatible scaledLinearFamily :=
  familyCompatible_of_commonInterleaver
    scaledLinearFamily_commonInterleaver
    scaledLinearFamily_hasPosLeadingCoeff

/-- Unconditional toy-family regression: this concrete family already has a
global common interleaver, so pairwise and full compatibility coincide without
needing the missing two-polynomial bridge. -/
lemma scaledLinearFamily_pairwiseCompatible_iff_familyCompatible :
    PairwiseCompatible scaledLinearFamily ↔ FamilyCompatible scaledLinearFamily :=
  ⟨fun _ => scaledLinearFamily_familyCompatible, fun _ => scaledLinearFamily_pairwiseCompatible⟩

/-- Concrete specialization of the packaged nonnegative `1 ↔ 4` direction.
Once the outstanding two-polynomial all-combinations bridge is discharged, this
family becomes an immediate end-to-end Chudnovsky--Seymour regression. -/
lemma scaledLinearFamily_pairwiseCompatible_iff_familyCompatible_of_allComboBridge
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible scaledLinearFamily ↔ FamilyCompatible scaledLinearFamily :=
  pairwiseCompatible_iff_familyCompatible_of_allComboBridge_and_nonnegCoeffs
    (fs := scaledLinearFamily)
    scaledLinearFamily_isRealRooted
    scaledLinearFamily_hasPosLeadingCoeff
    scaledLinearFamily_hasNonnegCoeffs
    hallBridge

private lemma xAddOne_natDegree :
    (X + 1 : ℝ[X]).natDegree = 1 := by
  simpa using
    (Polynomial.natDegree_linear (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp))

private lemma xAddTwo_natDegree :
    (X + 2 : ℝ[X]).natDegree = 1 := by
  change ((X + C (2 : ℝ) : ℝ[X]).natDegree = 1)
  simp

private lemma xAddTwo_isRealRooted : ((X + 2 : ℝ[X]) ≠ 0 ∧ (X + 2 : ℝ[X]).Splits) :=
  isRealRooted_of_degree_one xAddTwo_natDegree

private lemma xAddTwo_hasNonnegCoeffs : HasNonnegCoeffs (X + 2 : ℝ[X]) := by
  change HasNonnegCoeffs (X + C (2 : ℝ) : ℝ[X])
  exact hasNonnegCoeffs_X_add_C (by norm_num)

private lemma xAddTwo_hasPosLeadingCoeff : HasPosLeadingCoeff (X + 2 : ℝ[X]) := by
  change HasPosLeadingCoeff (X + C (2 : ℝ) : ℝ[X])
  exact hasPosLeadingCoeff_X_add_C (2 : ℝ)

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

private lemma xAddThree_hasPosLeadingCoeff : HasPosLeadingCoeff (X + 3 : ℝ[X]) := by
  change HasPosLeadingCoeff (X + C (3 : ℝ) : ℝ[X])
  exact hasPosLeadingCoeff_X_add_C (3 : ℝ)

private lemma xAddThree_roots :
    (X + 3 : ℝ[X]).roots = {(-3 : ℝ)} := by
  change ((X + C (3 : ℝ) : ℝ[X]).roots = {(-3 : ℝ)})
  simp

private lemma xAddFiveHalves_isRealRooted :
    ((X + C (5 / 2 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (5 / 2 : ℝ) : ℝ[X]).Splits) := by
  simpa [sub_eq_add_neg, add_comm] using isRealRooted_X_sub_C (-(5 / 2 : ℝ))

private lemma xAddFiveHalves_roots :
    (X + C (5 / 2 : ℝ) : ℝ[X]).roots = {(-(5 / 2 : ℝ))} := by
  simp

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
  rw [natDegree_mul xAddTwo_isRealRooted.1 xAddThree_isRealRooted.1]
  simp [xAddTwo_natDegree, xAddThree_natDegree]

private lemma xSq_add_fiveX_add_six_roots :
    (((X + 2) * (X + 3)) : ℝ[X]).roots = {(-3 : ℝ)} + {(-2 : ℝ)} := by
  rw [roots_mul (mul_ne_zero xAddTwo_isRealRooted.1 xAddThree_isRealRooted.1),
    xAddTwo_roots, xAddThree_roots]
  grind

private lemma xAddFiveHalves_prec_xAddOne :
    Prec (X + C (5 / 2 : ℝ) : ℝ[X]) (X + 1) := by
  refine
    ⟨xAddFiveHalves_isRealRooted, xAddOne_isRealRooted, [(-(5 / 2 : ℝ))], [(-1 : ℝ)],
      List.pairwise_singleton _ _, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp
  · simpa using xAddOne_roots.symm
  · exact Or.inr ⟨by simp, by norm_num [ListAlternates, ListInterlaces]⟩

private lemma xAddFiveHalves_prec_xSq_add_fiveX_add_six :
    Prec (X + C (5 / 2 : ℝ) : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) := by
  refine
    ⟨xAddFiveHalves_isRealRooted, xSq_add_fiveX_add_six_isRealRooted, [(-(5 / 2 : ℝ))],
      [(-3 : ℝ), (-2 : ℝ)], List.pairwise_singleton _ _, ?_, ?_, ?_, ?_⟩
  · norm_num
  · simp
  · rw [xSq_add_fiveX_add_six_roots]
    rfl
  · exact Or.inl ⟨by simp, by norm_num [ListInterlaces]⟩

/-- A concrete common left interleaver for the linear / quadratic counterexample
to the naive succ-degree orientation target. -/
lemma xAddOne_xSq_add_fiveX_add_six_commonLeftInterleaver :
    ∃ h : ℝ[X], Prec h (X + 1) ∧ Prec h (((X + 2) * (X + 3)) : ℝ[X]) :=
  ⟨X + C (5 / 2 : ℝ), xAddFiveHalves_prec_xAddOne,
    xAddFiveHalves_prec_xSq_add_fiveX_add_six⟩

/-- The quadratic pair `(X + 1, (X + 2)(X + 3))` still satisfies the positive-
combination hypothesis: the common left interleaver `X + 5/2` witnesses the
restricted Obreschkoff condition directly. -/
lemma xAddOne_xSq_add_fiveX_add_six_posComboRealRooted :
    PosComboRealRooted (X + 1 : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) :=
  PosComboRealRooted.of_commonLeftInterleaver
    xAddFiveHalves_prec_xAddOne
    xAddFiveHalves_prec_xSq_add_fiveX_add_six
      xAddOne_hasPosLeadingCoeff
      xSq_add_fiveX_add_six_hasPosLeadingCoeff

private lemma xAddOne_xSq_add_fiveX_add_six_noCommon :
    ∀ r, (X + 1 : ℝ[X]).IsRoot r → ¬ (((X + 2) * (X + 3)) : ℝ[X]).IsRoot r := by
  intro r hroot1 hroot2
  simp_all
  grind

private lemma xAddOne_xSq_add_fiveX_add_six_not_prec :
    ¬ Prec (X + 1 : ℝ[X]) (((X + 2) * (X + 3)) : ℝ[X]) := by
  intro hprec
  rcases hprec with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_card : (X + 1 : ℝ[X]).roots.card = 1 := by
    simpa [xAddOne_natDegree] using card_roots_of_splits hf.2
  have hrs_card : (((X + 2) * (X + 3)) : ℝ[X]).roots.card = 2 := by
    simpa [xSq_add_fiveX_add_six_natDegree] using card_roots_of_splits hg.2
  have hss_len : ss.length = 1 := by
    rw [← Multiset.coe_card, hss_eq, hss_card]
  have hrs_len : rs.length = 2 := by
    rw [← Multiset.coe_card, hrs_eq, hrs_card]
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
                        have hs_mem : (-1 : ℝ) ∈ (X + 1 : ℝ[X]).roots := by
                          simp_all
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
                      have : False := by
                        simp [hs_eq, hr1_eq, hr2_eq, ListInterlaces] at hinter
                      lia
                  | cons r₃ rs''' =>
                      simp at hrs_len
      | cons s₂ ss'' =>
          simp at hss_len

private lemma xAddOne_xAddTwo_linear_combo_eq {lam : ℝ} :
    (C lam * (X + 1) + (X + 2) : ℝ[X]) = X * C (lam + 1) + C (lam + 2) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          norm_num [mul_add, add_assoc, add_left_comm, add_comm, coeff_X, coeff_one]
      | succ n =>
          norm_num [mul_add, add_assoc, add_left_comm, add_comm, coeff_X, coeff_one]

private lemma xAddOne_xAddTwo_posComboRealRooted :
    PosComboRealRooted (X + 1 : ℝ[X]) (X + 2) := by
  refine PosComboRealRooted.of_add_left ?_
  intro lam hlam
  rw [xAddOne_xAddTwo_linear_combo_eq]
  have hdeg : (X * C (lam + 1) + C (lam + 2) : ℝ[X]).natDegree = 1 := by
    simpa [mul_comm] using
      (Polynomial.natDegree_linear (a := lam + 1) (b := lam + 2)
        (by grind : (lam + 1) ≠ 0))
  exact isRealRooted_of_degree_one hdeg

private lemma xAddOne_xAddTwo_noCommon :
    ∀ r, (X + 1 : ℝ[X]).IsRoot r → ¬ (X + 2 : ℝ[X]).IsRoot r := by
  intro r hroot1 hroot2
  simp_all
  linarith

/-- The linear pair used in the counterexamples still satisfies the true
all-combinations conclusion for a simpler reason: every combination remains
linear. -/
lemma xAddOne_xAddTwo_allComboRealRooted :
    AllComboRealRooted (X + 1 : ℝ[X]) (X + 2) :=
  allComboRealRooted_of_natDegree_le_one
    xAddOne_hasPosLeadingCoeff
    xAddTwo_hasPosLeadingCoeff
    (by simp [xAddOne_natDegree])
    (by simp [xAddTwo_natDegree])

private lemma xAddOne_xAddTwo_badAffineSlice_eq :
    ((((C (1 : ℝ) * X + C (1 : ℝ)) * (X + 1)) + (X + 2)) : ℝ[X]) =
      X ^ 2 + C (3 : ℝ) * X + C (3 : ℝ) := by
  ext n
  cases n with
  | zero =>
      norm_num
        [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm, coeff_X, coeff_one]
  | succ n =>
      cases n with
      | zero =>
          norm_num
            [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm, coeff_X, coeff_one]
      | succ n =>
          cases n with
          | zero =>
              norm_num
                [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
                  coeff_X, coeff_one]
          | succ n =>
              norm_num
                [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
                  coeff_X, coeff_one]

private lemma xSq_add_threeX_add_three_not_isRealRooted :
    ¬ ((X ^ 2 + C (3 : ℝ) * X + C (3 : ℝ) : ℝ[X]) ≠ 0 ∧
      (X ^ 2 + C (3 : ℝ) * X + C (3 : ℝ) : ℝ[X]).Splits) := by
  intro hrr
  have hdeg : (X ^ 2 + C (3 : ℝ) * X + C (3 : ℝ) : ℝ[X]).natDegree = 2 := by
    simpa using
      (Polynomial.natDegree_quadratic (a := (1 : ℝ)) (b := (3 : ℝ)) (c := (3 : ℝ))
        (by simp))
  obtain ⟨x, hx⟩ :=
    exists_isRoot_of_isRealRooted_of_not_isUnit hrr.1 hrr.2
      (not_isUnit_of_natDegree_pos _ (by lia))
  have hx_eval : (X ^ 2 + C (3 : ℝ) * X + C (3 : ℝ) : ℝ[X]).eval x = 0 := by
    simp_all
  have hquad : (1 : ℝ) * (x * x) + 3 * x + 3 = 0 := by
    simpa [eval_add, eval_mul, eval_C, eval_X, eval_pow, pow_two] using hx_eval
  have hdisc_sq : discrim (1 : ℝ) 3 3 = (2 * (1 : ℝ) * x + 3) ^ 2 :=
    discrim_eq_sq_of_quadratic_eq_zero hquad
  have hdisc_nonneg : 0 ≤ discrim (1 : ℝ) 3 3 := by
    rw [hdisc_sq]
    positivity
  norm_num [discrim] at hdisc_nonneg

private lemma xAddOne_xAddTwo_badShiftedPair_eq :
    (((X + 2) + X * (X + 1)) : ℝ[X]) =
      X ^ 2 + C (2 : ℝ) * X + C (2 : ℝ) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          norm_num
            [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm, coeff_X, coeff_one]
      | succ n =>
          cases n with
          | zero =>
              norm_num
                [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
                  coeff_X, coeff_one]
          | succ n =>
              norm_num
                [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
                  coeff_X, coeff_one]

private lemma xSq_add_twoX_add_two_not_isRealRooted :
    ¬ ((X ^ 2 + C (2 : ℝ) * X + C (2 : ℝ) : ℝ[X]) ≠ 0 ∧
      (X ^ 2 + C (2 : ℝ) * X + C (2 : ℝ) : ℝ[X]).Splits) := by
  intro hrr
  have hdeg : (X ^ 2 + C (2 : ℝ) * X + C (2 : ℝ) : ℝ[X]).natDegree = 2 := by
    simpa using
      (Polynomial.natDegree_quadratic (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (2 : ℝ))
        (by simp))
  obtain ⟨x, hx⟩ :=
    exists_isRoot_of_isRealRooted_of_not_isUnit hrr.1 hrr.2
      (not_isUnit_of_natDegree_pos _ (by lia))
  have hx_eval : (X ^ 2 + C (2 : ℝ) * X + C (2 : ℝ) : ℝ[X]).eval x = 0 := by
    simp_all
  have hquad : (1 : ℝ) * (x * x) + 2 * x + 2 = 0 := by
    simpa [eval_add, eval_mul, eval_C, eval_X, eval_pow, pow_two] using hx_eval
  have hdisc_sq : discrim (1 : ℝ) 2 2 = (2 * (1 : ℝ) * x + 2) ^ 2 :=
    discrim_eq_sq_of_quadratic_eq_zero hquad
  have hdisc_nonneg : 0 ≤ discrim (1 : ℝ) 2 2 := by
    rw [hdisc_sq]
    positivity
  norm_num [discrim] at hdisc_nonneg

private lemma xAddOne_xAddTwo_not_prec :
    ¬ Prec (X + 1 : ℝ[X]) (X + 2) := by
  intro hprec
  rcases hprec with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_card : (X + 1 : ℝ[X]).roots.card = 1 := by
    simpa [xAddOne_natDegree] using card_roots_of_splits hf.2
  have hrs_card : (X + 2 : ℝ[X]).roots.card = 1 := by
    simpa [xAddTwo_natDegree] using card_roots_of_splits hg.2
  have hss_len : ss.length = 1 := by
    rw [← Multiset.coe_card, hss_eq, hss_card]
  have hrs_len : rs.length = 1 := by
    rw [← Multiset.coe_card, hrs_eq, hrs_card]
  cases ss with
  | nil =>
      simp at hss_len
  | cons s ss' =>
      cases ss' with
      | nil =>
          cases rs with
          | nil =>
              simp at hrs_len
          | cons r rs' =>
              cases rs' with
              | nil =>
                  have hs_mem : s ∈ (X + 1 : ℝ[X]).roots := by
                    rw [← hss_eq]
                    simp
                  have hr_mem : r ∈ (X + 2 : ℝ[X]).roots := by
                    rw [← hrs_eq]
                    simp
                  have hs_root : (X + 1 : ℝ[X]).IsRoot s :=
                    (Polynomial.mem_roots hf.1).mp hs_mem
                  have hr_root : (X + 2 : ℝ[X]).IsRoot r :=
                    (Polynomial.mem_roots hg.1).mp hr_mem
                  have hs_eq : s = -1 := by
                    have hs_eval : s + 1 = 0 := by simp_all
                    linarith
                  have hr_eq : r = -2 := by
                    have hr_eval : r + 2 = 0 := by simp_all
                    linarith
                  have hsame_alt : ListAlternates [s] [r] := by lia
                  have hs_le_r : s ≤ r := by
                    simpa [ListAlternates, ListInterlaces] using hsame_alt
                  linarith
              | cons r₂ rs'' =>
                  simp at hrs_len
      | cons s₂ ss'' =>
          simp at hss_len

/-- The current nonnegative affine-family bridge target is false: the pair
`X + 1, X + 2` satisfies the positive-combo/no-common hypotheses, but the
affine slice at `s = t = 1` is `X^2 + 3 X + 3`, which is not real-rooted. -/
lemma not_posComboNoCommonAffineFamilyStatement :
    ¬ PosComboNoCommonAffineFamilyStatement := by
  intro haff
  have hrr :
      (((((C (1 : ℝ) * X + C (1 : ℝ)) * (X + 1)) + (X + 2)) : ℝ[X]) ≠ 0 ∧
        ((((C (1 : ℝ) * X + C (1 : ℝ)) * (X + 1)) + (X + 2)) : ℝ[X]).Splits) :=
      haff
        xAddOne_hasPosLeadingCoeff
        xAddTwo_hasPosLeadingCoeff
        xAddOne_hasNonnegCoeffs
        xAddTwo_hasNonnegCoeffs
        xAddOne_xAddTwo_posComboRealRooted
        (by simp [xAddOne_natDegree, xAddTwo_natDegree])
        (by simp [xAddOne_natDegree, xAddTwo_natDegree])
        xAddOne_xAddTwo_noCommon
        (show 0 < (1 : ℝ) by simp)
        (show 0 < (1 : ℝ) by simp)
  rw [xAddOne_xAddTwo_badAffineSlice_eq] at hrr
  exact xSq_add_threeX_add_three_not_isRealRooted hrr

/-- The sharper boundary-right-pair target is also false, because it implies
the affine-family target already refuted above. -/
lemma not_posComboNoCommonBoundaryRightPairOrientationStatement :
    ¬ PosComboNoCommonBoundaryRightPairOrientationStatement :=
  fun hboundary =>
    not_posComboNoCommonAffineFamilyStatement
      (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- The fixed-order same-degree shifted-pair target is also false: for
`f = X + 1`, `g = X + 2`, the shifted pair polynomial `g + X * f` is
`X^2 + 2 X + 2`, which is not real-rooted. -/
lemma not_posComboNoCommonSameDegreeShiftedPairOrientationStatement :
    ¬ PosComboNoCommonSameDegreeShiftedPairOrientationStatement := by
  intro hshift
  have hprec : Prec (X + 1 : ℝ[X]) ((X + 2) + X * (X + 1)) :=
      hshift
        xAddOne_hasPosLeadingCoeff
        xAddTwo_hasPosLeadingCoeff
        xAddOne_hasNonnegCoeffs
        xAddTwo_hasNonnegCoeffs
        xAddOne_xAddTwo_posComboRealRooted
        (by simp [xAddOne_natDegree, xAddTwo_natDegree])
        xAddOne_xAddTwo_noCommon
  have hrr : ((((X + 2) + X * (X + 1)) : ℝ[X]) ≠ 0 ∧
    (((X + 2) + X * (X + 1)) : ℝ[X]).Splits) := hprec.2.1
  rw [xAddOne_xAddTwo_badShiftedPair_eq] at hrr
  exact xSq_add_twoX_add_two_not_isRealRooted hrr

/-- The fixed-order same-degree orientation target is false as well: on the
same linear example, the correct orientation is not `Prec (X + 1) (X + 2)`. -/
lemma not_posComboNoCommonSameDegreeOrientationNonnegStatement :
    ¬ PosComboNoCommonSameDegreeOrientationNonnegStatement :=
  fun hsame =>
    xAddOne_xAddTwo_not_prec
      (hsame
        xAddOne_hasPosLeadingCoeff
        xAddTwo_hasPosLeadingCoeff
        xAddOne_hasNonnegCoeffs
        xAddTwo_hasNonnegCoeffs
        xAddOne_xAddTwo_posComboRealRooted
        (by simp [xAddOne_natDegree, xAddTwo_natDegree])
        xAddOne_xAddTwo_noCommon)

/-- The honest succ-degree orientation target is false as well: the pair
`X + 1, (X + 2)(X + 3)` satisfies the positive-combo/no-common hypotheses and
even has a concrete common interleaver `X + 5/2`, but both quadratic roots lie
strictly to the left of `-1`, so `Prec (X + 1) ((X + 2)(X + 3))` fails. -/
lemma not_posComboNoCommonSuccDegreeOrientationNonnegStatement :
    ¬ PosComboNoCommonSuccDegreeOrientationNonnegStatement :=
  fun hsucc =>
    xAddOne_xSq_add_fiveX_add_six_not_prec
      (hsucc
        xAddOne_hasPosLeadingCoeff
        xSq_add_fiveX_add_six_hasPosLeadingCoeff
        xAddOne_hasNonnegCoeffs
        xSq_add_fiveX_add_six_hasNonnegCoeffs
        xAddOne_xSq_add_fiveX_add_six_posComboRealRooted
        (by simp [xAddOne_natDegree, xSq_add_fiveX_add_six_natDegree])
        xAddOne_xSq_add_fiveX_add_six_noCommon)

/-! ### The general no-common orientation statement is false

The named `PosComboNoCommonOrientationStatement` (with the weaker conclusion
`Prec f g ∨ Prec g f`, and no nonnegative-coefficient hypothesis) is also
false.  Witnesses: `f = (X - 1)(X + 1) = X^2 - 1` and
`g = (X - 2)(X + 2) = X^2 - 4`.  Every positive combination
`lambda * f + mu * g = (lambda + mu) * X^2 - (lambda + 4 * mu)` is
real-rooted; the pair has no common roots; but `g`'s roots strictly nest
`f`'s roots, so neither orientation holds. -/

private def orientCexF : ℝ[X] := (X - C (1 : ℝ)) * (X - C (-1 : ℝ))

private def orientCexG : ℝ[X] := (X - C (2 : ℝ)) * (X - C (-2 : ℝ))

private lemma orientCexF_natDegree : orientCexF.natDegree = 2 := by
  unfold orientCexF
  rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    natDegree_X_sub_C, natDegree_X_sub_C]

private lemma orientCexG_natDegree : orientCexG.natDegree = 2 := by
  unfold orientCexG
  rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    natDegree_X_sub_C, natDegree_X_sub_C]

private lemma orientCexF_roots : orientCexF.roots = {1, -1} := by
  unfold orientCexF
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

private lemma orientCexG_roots : orientCexG.roots = {2, -2} := by
  unfold orientCexG
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

private lemma orientCexF_hasPosLeadingCoeff : HasPosLeadingCoeff orientCexF := by
  unfold orientCexF
  exact hasPosLeadingCoeff_X_sub_C_mul (r := (1 : ℝ))
    (hasPosLeadingCoeff_X_sub_C (-1 : ℝ))

private lemma orientCexG_hasPosLeadingCoeff : HasPosLeadingCoeff orientCexG := by
  unfold orientCexG
  exact hasPosLeadingCoeff_X_sub_C_mul (r := (2 : ℝ))
    (hasPosLeadingCoeff_X_sub_C (-2 : ℝ))

private lemma orientCex_noCommon :
    ∀ r, orientCexF.IsRoot r → ¬ orientCexG.IsRoot r := by
  intro r hrF hrG
  simp only [orientCexF, orientCexG, IsRoot.def, eval_mul, eval_sub,
    eval_X, eval_C] at hrF hrG
  rcases mul_eq_zero.mp hrF with h1 | h1 <;>
    rcases mul_eq_zero.mp hrG with h2 | h2 <;> linarith

private lemma orientCex_posComboRealRooted :
    PosComboRealRooted orientCexF orientCexG := by
  intro lam mu hlam hmu
  have hlammu : (0 : ℝ) < lam + mu := by linarith
  have hc : (0 : ℝ) ≤ (lam + 4 * mu) / (lam + mu) := by positivity
  set r : ℝ := Real.sqrt ((lam + 4 * mu) / (lam + mu)) with hr
  have hr2 : r ^ 2 = (lam + 4 * mu) / (lam + mu) := by
    rw [hr]
    exact Real.sq_sqrt hc
  have key : (lam + mu) * r ^ 2 = lam + 4 * mu := by
    rw [hr2]
    field_simp
  have hpoly :
      C lam * orientCexF + C mu * orientCexG =
        C (lam + mu) * (X - C r) * (X - C (-r)) := by
    apply Polynomial.funext
    intro x
    simp only [orientCexF, orientCexG, eval_add, eval_mul, eval_sub, eval_C, eval_X]
    linear_combination key
  refine ⟨?_, ?_⟩
  · rw [hpoly]
    exact mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hlammu.ne')
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  · rw [hpoly]
    exact ((Polynomial.Splits.C _).mul (Polynomial.Splits.X_sub_C _)).mul
      (Polynomial.Splits.X_sub_C _)

private lemma sorted_pair_eq {a b : ℝ} (hab : a < b) {l : List ℝ}
    (hsorted : l.Pairwise (· ≤ ·)) (hcoe : (↑l : Multiset ℝ) = {a, b}) :
    l = [a, b] := by
  have hlen : l.length = 2 := by
    have h := congrArg Multiset.card hcoe
    simpa using h
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  have hxy : x ≤ y := (List.pairwise_cons.mp hsorted).1 y (by simp)
  have hne : a ≠ b := ne_of_lt hab
  have hxab : x = a ∨ x = b := by
    have hx : x ∈ ({a, b} : Multiset ℝ) := by
      rw [← hcoe]
      simp
    simpa [Multiset.mem_cons, Multiset.mem_singleton] using hx
  have hyab : y = a ∨ y = b := by
    have hy : y ∈ ({a, b} : Multiset ℝ) := by
      rw [← hcoe]
      simp
    simpa [Multiset.mem_cons, Multiset.mem_singleton] using hy
  rcases hxab with rfl | rfl <;> rcases hyab with rfl | rfl
  · exfalso
    have hcount := congrArg (Multiset.count b) hcoe
    simp [Ne.symm hne] at hcount
  · rfl
  · exact absurd hxy (by linarith)
  · exfalso
    have hcount := congrArg (Multiset.count a) hcoe
    simp [hne] at hcount

private lemma orientCex_not_prec :
    ¬ (Prec orientCexF orientCexG ∨ Prec orientCexG orientCexF) := by
  rintro (h | h)
  · obtain ⟨-, -, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := h
    rw [orientCexF_roots] at hss_eq
    rw [orientCexG_roots] at hrs_eq
    have hsseq : ss = [-1, 1] :=
      sorted_pair_eq (by norm_num) hss (by rw [hss_eq]; exact Multiset.pair_comm 1 (-1))
    have hrseq : rs = [-2, 2] :=
      sorted_pair_eq (by norm_num) hrs (by rw [hrs_eq]; exact Multiset.pair_comm 2 (-2))
    subst hsseq
    subst hrseq
    rcases hshape with ⟨hlen, _⟩ | ⟨_, halt⟩
    · simp only [List.length_cons, List.length_nil] at hlen
      lia
    · simp only [ListAlternates, ListInterlaces] at halt
      norm_num at halt
  · obtain ⟨-, -, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := h
    rw [orientCexG_roots] at hss_eq
    rw [orientCexF_roots] at hrs_eq
    have hsseq : ss = [-2, 2] :=
      sorted_pair_eq (by norm_num) hss (by rw [hss_eq]; exact Multiset.pair_comm 2 (-2))
    have hrseq : rs = [-1, 1] :=
      sorted_pair_eq (by norm_num) hrs (by rw [hrs_eq]; exact Multiset.pair_comm 1 (-1))
    subst hsseq
    subst hrseq
    rcases hshape with ⟨hlen, _⟩ | ⟨_, halt⟩
    · simp only [List.length_cons, List.length_nil] at hlen
      lia
    · simp only [ListAlternates, ListInterlaces] at halt
      norm_num at halt

/-- The general no-common orientation statement is false. -/
lemma not_posComboNoCommonOrientationStatement :
    ¬ PosComboNoCommonOrientationStatement := by
  intro horient
  refine orientCex_not_prec ?_
  exact horient orientCex_posComboRealRooted
    orientCexF_hasPosLeadingCoeff orientCexG_hasPosLeadingCoeff
    (by have h1 := orientCexF_natDegree; have h2 := orientCexG_natDegree; lia)
    (by have h1 := orientCexF_natDegree; have h2 := orientCexG_natDegree; lia)
    orientCex_noCommon

/-! ### The residual succ-degree orientation target is false

The residual branch of the succ-degree no-common orientation problem
(`PosComboNoCommonSuccDegreeRootCountResidualPrecStatement`) additionally
assumes `f.coeff 0 = 0` and `g.coeff 0 ≠ 0`.  It is false: take `f = X` and
`g = (X + 1)(X + 2)`.  A common left interleaver `X + 3/2` witnesses the
positive-combination condition, but `0`, the only root of `X`, lies strictly to
the right of both roots of `g`, so `Prec X g` fails. -/

private lemma X_isRealRooted : ((X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits) :=
  isRealRooted_X

private lemma X_hasNonnegCoeffs : HasNonnegCoeffs (X : ℝ[X]) :=
  hasNonnegCoeffs_X

private lemma X_hasPosLeadingCoeff : HasPosLeadingCoeff (X : ℝ[X]) :=
  X_hasNonnegCoeffs.pos_leadingCoeff X_ne_zero

private lemma X_roots : (X : ℝ[X]).roots = {(0 : ℝ)} := by
  simp

private lemma X_coeff_zero : (X : ℝ[X]).coeff 0 = 0 := by
  simp

private lemma xAddOne_xAddTwo_isRealRooted :
    ((((X + 1) * (X + 2)) : ℝ[X]) ≠ 0 ∧ (((X + 1) * (X + 2)) : ℝ[X]).Splits) :=
  isRealRooted_mul xAddOne_isRealRooted.1 xAddOne_isRealRooted.2
    xAddTwo_isRealRooted.1 xAddTwo_isRealRooted.2

private lemma xAddOne_xAddTwo_hasNonnegCoeffs :
    HasNonnegCoeffs (((X + 1) * (X + 2)) : ℝ[X]) :=
  xAddOne_hasNonnegCoeffs.mul xAddTwo_hasNonnegCoeffs

private lemma xAddOne_xAddTwo_hasPosLeadingCoeff :
    HasPosLeadingCoeff (((X + 1) * (X + 2)) : ℝ[X]) :=
  xAddOne_xAddTwo_hasNonnegCoeffs.pos_leadingCoeff xAddOne_xAddTwo_isRealRooted.1

private lemma xAddOne_xAddTwo_natDegree :
    (((X + 1) * (X + 2)) : ℝ[X]).natDegree = 2 := by
  rw [natDegree_mul xAddOne_isRealRooted.1 xAddTwo_isRealRooted.1]
  simp [xAddOne_natDegree, xAddTwo_natDegree]

private lemma xAddOne_xAddTwo_roots :
    (((X + 1) * (X + 2)) : ℝ[X]).roots = {(-2 : ℝ)} + {(-1 : ℝ)} := by
  rw [roots_mul (mul_ne_zero xAddOne_isRealRooted.1 xAddTwo_isRealRooted.1),
    xAddOne_roots, xAddTwo_roots, add_comm]

private lemma xAddOne_xAddTwo_coeff_zero_ne :
    (((X + 1) * (X + 2)) : ℝ[X]).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp only [eval_mul, eval_add, eval_X, eval_one, eval_ofNat]
  norm_num

private lemma xAddThreeHalves_isRealRooted :
    ((X + C (3 / 2 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (3 / 2 : ℝ) : ℝ[X]).Splits) := by
  simpa [sub_eq_add_neg, add_comm] using isRealRooted_X_sub_C (-(3 / 2 : ℝ))

private lemma xAddThreeHalves_prec_X :
    Prec (X + C (3 / 2 : ℝ) : ℝ[X]) (X : ℝ[X]) := by
  refine
    ⟨xAddThreeHalves_isRealRooted, X_isRealRooted, [(-(3 / 2 : ℝ))], [(0 : ℝ)],
      List.pairwise_singleton _ _, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Or.inr ⟨by simp, by norm_num [ListAlternates, ListInterlaces]⟩

private lemma xAddThreeHalves_prec_xAddOne_xAddTwo :
    Prec (X + C (3 / 2 : ℝ) : ℝ[X]) (((X + 1) * (X + 2)) : ℝ[X]) := by
  refine
    ⟨xAddThreeHalves_isRealRooted, xAddOne_xAddTwo_isRealRooted,
      [(-(3 / 2 : ℝ))], [(-2 : ℝ), (-1 : ℝ)],
      List.pairwise_singleton _ _, ?_, ?_, ?_, ?_⟩
  · norm_num
  · simp
  · rw [xAddOne_xAddTwo_roots]
    rfl
  · exact Or.inl ⟨by simp, by norm_num [ListInterlaces]⟩

private lemma X_xAddOne_xAddTwo_posComboRealRooted :
    PosComboRealRooted (X : ℝ[X]) (((X + 1) * (X + 2)) : ℝ[X]) :=
  PosComboRealRooted.of_commonLeftInterleaver
    xAddThreeHalves_prec_X
    xAddThreeHalves_prec_xAddOne_xAddTwo
    X_hasPosLeadingCoeff
    xAddOne_xAddTwo_hasPosLeadingCoeff

private lemma X_xAddOne_xAddTwo_noCommon :
    ∀ r, (X : ℝ[X]).IsRoot r → ¬ (((X + 1) * (X + 2)) : ℝ[X]).IsRoot r := by
  intro r hr1 hr2
  have hr0 : r = 0 := by
    have h := hr1
    simp only [IsRoot, eval_X] at h
    exact h
  subst hr0
  simp only [IsRoot, eval_mul, eval_add, eval_X, eval_one, eval_ofNat] at hr2
  norm_num at hr2

private lemma X_not_prec_xAddOne_xAddTwo :
    ¬ Prec (X : ℝ[X]) (((X + 1) * (X + 2)) : ℝ[X]) := by
  intro hprec
  have hg_le : ∀ r ∈ (((X + 1) * (X + 2)) : ℝ[X]).roots, r ≤ (-1 : ℝ) := by
    intro r hr
    rw [xAddOne_xAddTwo_roots] at hr
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hr
    rcases hr with h | h <;> subst h <;> norm_num
  have hf_le := roots_le_of_prec_right hprec hg_le
  have h0 : (0 : ℝ) ∈ (X : ℝ[X]).roots := by
    rw [X_roots]
    simp
  have := hf_le 0 h0
  norm_num at this

/-- The residual succ-degree orientation target
`PosComboNoCommonSuccDegreeRootCountResidualPrecStatement` is false.
Witnessed by `f = X`, `g = (X + 1)(X + 2)`. -/
lemma not_posComboNoCommonSuccDegreeRootCountResidualPrecStatement :
    ¬ PosComboNoCommonSuccDegreeRootCountResidualPrecStatement :=
  fun hres =>
    X_not_prec_xAddOne_xAddTwo
      (hres
        X_hasPosLeadingCoeff
        xAddOne_xAddTwo_hasPosLeadingCoeff
        X_hasNonnegCoeffs
        xAddOne_xAddTwo_hasNonnegCoeffs
        X_xAddOne_xAddTwo_posComboRealRooted
        (by norm_num [xAddOne_xAddTwo_natDegree, natDegree_X])
        X_xAddOne_xAddTwo_noCommon
        X_isRealRooted.2
        X_coeff_zero
        xAddOne_xAddTwo_coeff_zero_ne)

end CommonInterleaverExamples

end RealRooted
