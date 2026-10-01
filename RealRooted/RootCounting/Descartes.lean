module

public import Mathlib.Analysis.Polynomial.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Descartes' rule of signs

This file strengthens Mathlib's positive-root bound with the classical parity
conclusion and derives the negative-root version by reflection.
-/

@[expose] public section

open Filter SignType

namespace Polynomial

/-- The number of positive real roots of a real polynomial, counted with
multiplicity. -/
noncomputable def positiveRootCount (p : ℝ[X]) : ℕ :=
  p.roots.countP (0 < ·)

/-- The number of negative real roots of a real polynomial, counted with
multiplicity. -/
noncomputable def negativeRootCount (p : ℝ[X]) : ℕ :=
  p.roots.countP (· < 0)

private theorem exists_pos_isRoot_of_eval_zero_neg_of_leadingCoeff_pos
    {p : ℝ[X]} (hzero : p.eval 0 < 0) (hlead : 0 < p.leadingCoeff) :
    ∃ x, 0 < x ∧ p.IsRoot x := by
  have hdeg : 0 < p.degree := by
    by_contra h
    have hpC : p = C (p.coeff 0) :=
      eq_C_of_degree_le_zero (le_of_not_gt h)
    have : p.leadingCoeff = p.eval 0 := by
      rw [hpC]
      simp
    linarith
  have ht : Tendsto (fun x => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead.le
  have hpos : ∀ᶠ x in atTop, 0 < p.eval x :=
    ht.eventually (Ioi_mem_atTop 0)
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  obtain ⟨x, hx, hpx⟩ := (hxpos.and hpos).exists
  have h0mem : (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval x) :=
    ⟨hzero.le, hpx.le⟩
  obtain ⟨u, hu, hroot⟩ :=
    intermediate_value_Icc hx.le p.continuous.continuousOn h0mem
  refine ⟨u, lt_of_le_of_ne hu.1 ?_, hroot⟩
  rintro rfl
  exact hzero.ne hroot

private theorem exists_pos_isRoot_of_sign_endpoints_ne
    {p : ℝ[X]} (hp : p ≠ 0)
    (hsign : sign p.leadingCoeff ≠ sign p.trailingCoeff) :
    ∃ x, 0 < x ∧ p.IsRoot x := by
  let q := p /ₘ (X - C 0) ^ p.rootMultiplicity 0
  have hfactor : (X - C 0) ^ p.rootMultiplicity 0 * q = p := by
    simpa [q] using p.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, mul_zero] at hfactor
    exact hp hfactor.symm
  have hqzero : q.eval 0 = p.trailingCoeff := by
    simpa [q] using (eval_divByMonic_eq_trailingCoeff_comp (p := p) (t := 0))
  have hmonic : ((X - C 0) ^ p.rootMultiplicity 0 : ℝ[X]).Monic :=
    (monic_X_sub_C 0).pow _
  have hdegree : ((X - C 0) ^ p.rootMultiplicity 0 : ℝ[X]).degree ≤ p.degree :=
    degree_le_of_dvd (pow_rootMultiplicity_dvd p 0) hp
  have hqlead : q.leadingCoeff = p.leadingCoeff :=
    leadingCoeff_divByMonic_of_monic hmonic hdegree
  have hpLead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hpTrail : p.trailingCoeff ≠ 0 :=
    trailingCoeff_nonzero_iff_nonzero.mpr hp
  rcases lt_or_gt_of_ne hpLead with hpLeadNeg | hpLeadPos
  · have hpTrailPos : 0 < p.trailingCoeff := by
      rcases lt_or_gt_of_ne hpTrail with hpTrailNeg | hpTrailPos
      · exact (hsign (by simp [sign_neg hpLeadNeg, sign_neg hpTrailNeg])).elim
      · exact hpTrailPos
    obtain ⟨x, hx, hroot⟩ :=
      exists_pos_isRoot_of_eval_zero_neg_of_leadingCoeff_pos
        (p := -q) (by simp [hqzero, hpTrailPos]) (by simp [hqlead, hpLeadNeg])
    have hqroot : q.IsRoot x := by
      rw [IsRoot, eval_neg, neg_eq_zero] at hroot
      exact hroot
    refine ⟨x, hx, ?_⟩
    rw [← hfactor, IsRoot, eval_mul, hqroot, mul_zero]
  · have hpTrailNeg : p.trailingCoeff < 0 := by
      rcases lt_or_gt_of_ne hpTrail with hpTrailNeg | hpTrailPos
      · exact hpTrailNeg
      · exact (hsign (by simp [sign_pos hpLeadPos, sign_pos hpTrailPos])).elim
    obtain ⟨x, hx, hroot⟩ :=
      exists_pos_isRoot_of_eval_zero_neg_of_leadingCoeff_pos
        (p := q) (by simpa [hqzero]) (by simpa [hqlead])
    refine ⟨x, hx, ?_⟩
    rw [← hfactor, IsRoot, eval_mul, hroot, mul_zero]

/-- If a nonzero real polynomial has no positive roots, then its coefficient
sign-variation count is even. -/
theorem even_signVariations_of_positiveRootCount_eq_zero
    {p : ℝ[X]} (hp : p ≠ 0) (hroots : p.positiveRootCount = 0) :
    Even p.signVariations := by
  rw [even_signVariations_iff_sign_leadingCoeff_eq_sign_trailingCoeff hp]
  by_contra hsign
  obtain ⟨x, hx, hroot⟩ := exists_pos_isRoot_of_sign_endpoints_ne hp hsign
  have hxmem : x ∈ p.roots := (mem_roots hp).2 hroot
  have : 0 < p.positiveRootCount :=
    Multiset.countP_pos_of_mem hxmem hx
  lia

/-- The parity form of Descartes' rule of signs for positive roots. -/
theorem even_signVariations_sub_positiveRootCount (p : ℝ[X]) :
    Even (p.signVariations - p.positiveRootCount) := by
  generalize hcount : p.positiveRootCount = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hn : n = 0
      · rw [hn]
        by_cases hp : p = 0
        · simp [hp]
        · exact even_signVariations_of_positiveRootCount_eq_zero hp (hcount.trans hn)
      · have hp : p ≠ 0 := by
          intro hpzero
          apply hn
          subst p
          simpa [positiveRootCount] using hcount.symm
        obtain ⟨r, hrmem, hrpos⟩ : ∃ r, r ∈ p.roots ∧ 0 < r := by
          have : 0 < p.positiveRootCount := by lia
          simpa [positiveRootCount] using
            (Multiset.countP_pos.mp this)
        obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots hrmem)
        have hq : q ≠ 0 := right_ne_zero_of_mul hp
        have hrootCount :
            ((X - C r) * q).positiveRootCount = q.positiveRootCount + 1 := by
          simp [positiveRootCount, roots_mul (ne_zero_of_mem_roots hrmem), hrpos]
        have hqCount : q.positiveRootCount < n := by lia
        have hi := ih q.positiveRootCount hqCount q rfl
        have hodd := odd_signVariations_sub_of_X_sub_C_mul hrpos hq
        have htransition := succ_signVariations_le_X_sub_C_mul hrpos hq
        have hbound := roots_countP_pos_le_signVariations q
        change q.positiveRootCount ≤ q.signVariations at hbound
        rcases hi with ⟨a, ha⟩
        rcases hodd with ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        rw [hrootCount] at hcount
        lia

/-- Descartes' rule of signs: positive roots are counted with multiplicity,
and the difference from the coefficient sign-variation count is even. -/
theorem descartes_rule_of_signs (p : ℝ[X]) :
    p.positiveRootCount ≤ p.signVariations ∧
      Even (p.signVariations - p.positiveRootCount) :=
  ⟨roots_countP_pos_le_signVariations p,
    even_signVariations_sub_positiveRootCount p⟩

/-- Descartes' rule of signs for negative roots, obtained by applying the
positive-root theorem to `p(-X)`. -/
theorem descartes_rule_of_signs_negative (p : ℝ[X]) :
    p.negativeRootCount ≤ (p.comp (-X)).signVariations ∧
      Even ((p.comp (-X)).signVariations - p.negativeRootCount) := by
  simpa [positiveRootCount, negativeRootCount, roots_comp_neg_X,
    Multiset.countP_eq_card_filter, Multiset.filter_map,
    Function.comp_def] using
      descartes_rule_of_signs (p.comp (-X))

end Polynomial
