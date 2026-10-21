import RealRooted.CommonInterleaverTwo
import RealRooted.Mathlib.Data.List.Sort.Endpoint

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
  hasNonnegCoeffs_C_mul (by simp) hasNonnegCoeffs_X_add_one

private lemma threeMul_xAddOne_hasNonnegCoeffs :
    HasNonnegCoeffs (C (3 : ℝ) * (X + 1)) :=
  hasNonnegCoeffs_C_mul (by simp) hasNonnegCoeffs_X_add_one

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
  · exact hasNonnegCoeffs_X_add_one
  · exact twoMul_xAddOne_hasNonnegCoeffs
  · exact threeMul_xAddOne_hasNonnegCoeffs

/-- The common interleaver is just `X + 1` itself. -/
lemma scaledLinearFamily_commonInterleaver :
    HasCommonInterleaver scaledLinearFamily := by
  refine ⟨X + 1, ?_⟩
  intro f hf
  simp only [scaledLinearFamily, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact StrictInterl.refl xAddOne_isRealRooted.1 xAddOne_isRealRooted.2
  · exact StrictInterl.C_mul_self xAddOne_isRealRooted.1 xAddOne_isRealRooted.2 (by simp)
  · exact StrictInterl.C_mul_self xAddOne_isRealRooted.1 xAddOne_isRealRooted.2 (by simp)

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
  intro hstrict
  have hcount :=
    (succDegreeRootCountLowerOriented_of_strictInterl hstrict
      (by simp [xSq_add_fiveX_add_six_natDegree]) (-2)).2
  rw [xAddOne_roots, xSq_add_fiveX_add_six_roots] at hcount
  norm_num [Multiset.filter_add, Multiset.filter_singleton] at hcount

private lemma xAddOne_xAddTwo_linear_combo_eq {lam : ℝ} :
    (C lam * (X + 1) + (X + 2) : ℝ[X]) = X * C (lam + 1) + C (lam + 2) := by
  simp only [map_add, map_one, map_ofNat]
  ring

/-- The linear pair used in the counterexamples still satisfies the true
all-combinations conclusion for a simpler reason: every combination remains
linear. -/
lemma xAddOne_xAddTwo_allComboRealRooted :
    AllComboRealRooted (X + 1 : ℝ[X]) (X + 2) :=
  allComboRealRooted_of_natDegree_le_one
    xAddOne_hasPosLeadingCoeff
    xAddTwo_hasPosLeadingCoeff
    (by simp)
    (by simp [xAddTwo_natDegree])

/-- Fixed orientation fails for successor-degree pairs: the pair
`X + 1, (X + 2)(X + 3)` satisfies the positive-combination/no-common hypotheses
and even has a concrete common interleaver `X + 5/2`, but both quadratic roots
lie strictly to the left of `-1`, so `StrictInterl (X + 1) ((X + 2)(X + 3))`
fails. -/
lemma not_forall_posCombo_succDegree_noCommon_strictInterl :
    ¬ ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      g.natDegree = f.natDegree + 1 →
      (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
      StrictInterl f g :=
  fun hsucc =>
    xAddOne_xSq_add_fiveX_add_six_not_strictInterl
      (hsucc
        xAddOne_hasPosLeadingCoeff
        xSq_add_fiveX_add_six_hasPosLeadingCoeff
        hasNonnegCoeffs_X_add_one
        xSq_add_fiveX_add_six_hasNonnegCoeffs
        xAddOne_xSq_add_fiveX_add_six_posComboRealRooted
        (by simp [xSq_add_fiveX_add_six_natDegree])
        xAddOne_xSq_add_fiveX_add_six_noCommon)

/-- The negative half of the right pencil of a compatible successor-degree pair
need not be real-rooted.  The pair `X + 1, (X + 2)(X + 3)` is compatible and has
nonnegative coefficients, but the pencil member at `μ = -1` is a quadratic with
negative discriminant. -/
lemma not_forall_compatible_succDegree_negativeRightFamily_splits :
    ¬ ∀ ⦃f g : ℝ[X]⦄,
      Compatible f g →
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      g.natDegree = f.natDegree + 1 →
      f.Splits →
      ∀ μ : ℝ, μ < 0 → (f + C μ * g).Splits := by
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
      hasNonnegCoeffs_X_add_one
      xSq_add_fiveX_add_six_hasNonnegCoeffs
      (by simp [xSq_add_fiveX_add_six_natDegree])
      xAddOne_isRealRooted.2
      (-1 : ℝ) (by norm_num)
  have hp_eq :
      ((X + 1 : ℝ[X]) + C (-1 : ℝ) * (((X + 2) * (X + 3)) : ℝ[X])) =
        C (-1 : ℝ) * X ^ 2 + C (-4 : ℝ) * X + C (-5 : ℝ) := by
    norm_num only [map_add, map_one, map_ofNat, map_neg]
    ring
  have hdeg :
      ((X + 1 : ℝ[X]) + C (-1 : ℝ) * (((X + 2) * (X + 3)) : ℝ[X])).natDegree = 2 := by
    rw [hp_eq]
    exact Polynomial.natDegree_quadratic (by norm_num : (-1 : ℝ) ≠ 0)
  have hdisc := quadratic_disc_coeff_le_of_splits_natDegree_two hdeg hsplits
  rw [hp_eq] at hdisc
  norm_num [coeff_X, pow_two] at hdisc

/-- Compatible successor-degree pairs need not have all real combinations
real-rooted: this would contain the negative right pencil. -/
lemma not_forall_compatible_succDegree_allComboRealRooted :
    ¬ ∀ ⦃f g : ℝ[X]⦄,
      Compatible f g →
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 →
      f.Splits →
      AllComboRealRooted f g :=
  fun hall =>
    not_forall_compatible_succDegree_negativeRightFamily_splits
      (fun {f g} hcomp hf_pos hg_pos _ _ hdeg hf_split μ _ => by
        simpa using hall (f := f) (g := g) hcomp hf_pos hg_pos hdeg hf_split 1 μ)

/-! ### No-common positive combinations need not be oriented

Even the weaker conclusion `StrictInterl f g ∨ StrictInterl g f`, without a
nonnegative-coefficient hypothesis, fails.  Witnesses: `f = (X - 1)(X + 1) = X^2 - 1` and
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
  simp

private lemma orientCexG_roots : orientCexG.roots = {2, -2} := by
  unfold orientCexG
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  simp

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
  grind

private lemma orientCex_posComboRealRooted :
    PosComboRealRooted orientCexF orientCexG := by
  intro lam mu hlam hmu
  have hlammu : (0 : ℝ) < lam + mu := by linarith
  have hc : (0 : ℝ) ≤ (lam + 4 * mu) / (lam + mu) := by positivity
  set r : ℝ := Real.sqrt ((lam + 4 * mu) / (lam + mu)) with hr
  have hr2 : r ^ 2 = (lam + 4 * mu) / (lam + mu) := by simp_all
  have : (lam + mu) * r ^ 2 = lam + 4 * mu := by grind
  have hpoly :
      C lam * orientCexF + C mu * orientCexG =
        C (lam + mu) * (X - C r) * (X - C (-r)) := by
    apply Polynomial.funext
    intro x
    simp only [orientCexF, orientCexG, eval_add, eval_mul, eval_sub, eval_C, eval_X]
    grind
  refine ⟨?_, ?_⟩
  · rw [hpoly]
    exact mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hlammu.ne')
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  · rw [hpoly]
    exact ((Polynomial.Splits.C _).mul (Polynomial.Splits.X_sub_C _)).mul
      (Polynomial.Splits.X_sub_C _)

private lemma orientCex_not_strictInterl :
    ¬ (StrictInterl orientCexF orientCexG ∨ StrictInterl orientCexG orientCexF) := by
  rintro (hfg | hgf)
  · have hcount :=
      (sameDegreeRootCountOriented_of_strictInterl hfg
        (by simp [orientCexF_natDegree, orientCexG_natDegree])
        (-(3 / 2 : ℝ))).1
    rw [orientCexF_roots, orientCexG_roots] at hcount
    rw [show ({(2 : ℝ), -2} : Multiset ℝ) = {2} + {-2} by rfl,
      show ({(1 : ℝ), -1} : Multiset ℝ) = {1} + {-1} by rfl] at hcount
    norm_num [Multiset.filter_add, Multiset.filter_singleton] at hcount
  · have hcount :=
      (sameDegreeRootCountOriented_of_strictInterl hgf
        (by simp [orientCexF_natDegree, orientCexG_natDegree])
        (3 / 2 : ℝ)).1
    rw [orientCexG_roots, orientCexF_roots] at hcount
    rw [show ({(1 : ℝ), -1} : Multiset ℝ) = {1} + {-1} by rfl,
      show ({(2 : ℝ), -2} : Multiset ℝ) = {2} + {-2} by rfl] at hcount
    norm_num [Multiset.filter_add, Multiset.filter_singleton] at hcount

/-- Positive-combination real-rootedness without common roots does not force
either interlacing orientation, even in equal degree. -/
lemma not_forall_posCombo_noCommon_strictInterl_or :
    ¬ ∀ ⦃f g : ℝ[X]⦄,
      PosComboRealRooted f g →
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      f.natDegree ≤ g.natDegree →
      g.natDegree ≤ f.natDegree + 1 →
      (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
      StrictInterl f g ∨ StrictInterl g f :=
  fun horient =>
    orientCex_not_strictInterl
      (horient orientCex_posComboRealRooted
        orientCexF_hasPosLeadingCoeff orientCexG_hasPosLeadingCoeff
        (by simp [orientCexF_natDegree, orientCexG_natDegree])
        (by simp [orientCexF_natDegree, orientCexG_natDegree])
        orientCex_noCommon)

/-! ### Successor-degree orientation fails even with `f.coeff 0 = 0`

Adding the hypotheses `f.coeff 0 = 0` and `g.coeff 0 ≠ 0` to the
successor-degree orientation problem does not help: take `f = X` and
`g = (X + 1)(X + 2)`.  A common left interleaver `X + 3/2` witnesses the
positive-combination condition, but `0`, the only root of `X`, lies strictly to
the right of both roots of `g`, so `StrictInterl X g` fails. -/

private lemma X_hasPosLeadingCoeff : HasPosLeadingCoeff (X : ℝ[X]) :=
  hasNonnegCoeffs_X.pos_leadingCoeff X_ne_zero

private lemma X_coeff_zero : (X : ℝ[X]).coeff 0 = 0 := by simp

private lemma xAddOne_xAddTwo_isRealRooted :
    ((((X + 1) * (X + 2)) : ℝ[X]) ≠ 0 ∧ (((X + 1) * (X + 2)) : ℝ[X]).Splits) :=
  isRealRooted_mul xAddOne_isRealRooted.1 xAddOne_isRealRooted.2
    xAddTwo_isRealRooted.1 xAddTwo_isRealRooted.2

private lemma xAddOne_xAddTwo_hasNonnegCoeffs :
    HasNonnegCoeffs (((X + 1) * (X + 2)) : ℝ[X]) :=
  hasNonnegCoeffs_X_add_one.mul xAddTwo_hasNonnegCoeffs

private lemma xAddOne_xAddTwo_hasPosLeadingCoeff :
    HasPosLeadingCoeff (((X + 1) * (X + 2)) : ℝ[X]) :=
  xAddOne_xAddTwo_hasNonnegCoeffs.pos_leadingCoeff xAddOne_xAddTwo_isRealRooted.1

private lemma xAddOne_xAddTwo_natDegree :
    (((X + 1) * (X + 2)) : ℝ[X]).natDegree = 2 := by
  simp [natDegree_mul xAddOne_isRealRooted.1 xAddTwo_isRealRooted.1,
    xAddTwo_natDegree]

private lemma xAddOne_xAddTwo_roots :
    (((X + 1) * (X + 2)) : ℝ[X]).roots = {(-2 : ℝ)} + {(-1 : ℝ)} := by
  rw [roots_mul (mul_ne_zero xAddOne_isRealRooted.1 xAddTwo_isRealRooted.1),
    xAddOne_roots, xAddTwo_roots, add_comm]

private lemma xAddOne_xAddTwo_coeff_zero_ne :
    (((X + 1) * (X + 2)) : ℝ[X]).coeff 0 ≠ 0 := by simp

private lemma xAddThreeHalves_isRealRooted :
    ((X + C (3 / 2 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (3 / 2 : ℝ) : ℝ[X]).Splits) := by
  simpa [sub_eq_add_neg, add_comm] using isRealRooted_X_sub_C (-(3 / 2 : ℝ))

private lemma xAddThreeHalves_strictInterl_X :
    StrictInterl (X + C (3 / 2 : ℝ) : ℝ[X]) (X : ℝ[X]) := by
  refine
    ⟨xAddThreeHalves_isRealRooted, isRealRooted_X, [(-(3 / 2 : ℝ))], [(0 : ℝ)],
      List.pairwise_singleton _ _, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Or.inr ⟨by simp, by norm_num [ListAlternates, ListInterlaces]⟩

private lemma xAddThreeHalves_strictInterl_xAddOne_xAddTwo :
    StrictInterl (X + C (3 / 2 : ℝ) : ℝ[X]) (((X + 1) * (X + 2)) : ℝ[X]) := by
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
    xAddThreeHalves_strictInterl_X
    xAddThreeHalves_strictInterl_xAddOne_xAddTwo
    X_hasPosLeadingCoeff
    xAddOne_xAddTwo_hasPosLeadingCoeff

private lemma X_xAddOne_xAddTwo_noCommon :
    ∀ r, (X : ℝ[X]).IsRoot r → ¬ (((X + 1) * (X + 2)) : ℝ[X]).IsRoot r := by simp

private lemma X_not_strictInterl_xAddOne_xAddTwo :
    ¬ StrictInterl (X : ℝ[X]) (((X + 1) * (X + 2)) : ℝ[X]) := by
  intro hstrictInterl
  have hg_le : ∀ r ∈ (((X + 1) * (X + 2)) : ℝ[X]).roots, r ≤ (-1 : ℝ) := by
    intro r hr
    rw [xAddOne_xAddTwo_roots] at hr
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hr
    grind
  have hf_le := hstrictInterl.roots_le_of_right hg_le
  have h0 : (0 : ℝ) ∈ (X : ℝ[X]).roots := by simp
  grind

/-- Fixed orientation fails for successor-degree pairs even when the
lower-degree polynomial vanishes at `0` and the higher-degree one does not. -/
lemma not_forall_posCombo_succDegree_noCommon_coeff_zero_strictInterl :
    ¬ ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      PosComboRealRooted f g →
      g.natDegree = f.natDegree + 1 →
      (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
      f.Splits →
      f.coeff 0 = 0 →
      g.coeff 0 ≠ 0 →
      StrictInterl f g :=
  fun hresid =>
    X_not_strictInterl_xAddOne_xAddTwo
      (hresid X_hasPosLeadingCoeff xAddOne_xAddTwo_hasPosLeadingCoeff
        hasNonnegCoeffs_X xAddOne_xAddTwo_hasNonnegCoeffs
        X_xAddOne_xAddTwo_posComboRealRooted
        (by simp [xAddOne_xAddTwo_natDegree])
        X_xAddOne_xAddTwo_noCommon isRealRooted_X.2 X_coeff_zero
        xAddOne_xAddTwo_coeff_zero_ne)

end CommonInterleaverExamples

end RealRooted
