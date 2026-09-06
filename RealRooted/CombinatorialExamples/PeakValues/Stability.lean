import RealRooted.CombinatorialExamples.PeakValues.TranslatedRecurrence
import RealRooted.HomogeneousStability

/-!
# Stability of the peak-value polynomial

This file proves multivariate real stability of the peak-value enumerator.
The proof lifts the translated insertion recurrence to homogeneous stable
polynomials and alternates two derivative constructions according to parity.
-/

open scoped BigOperators

namespace RealRooted

noncomputable section

open MvPolynomial

/-- The translated insertion recurrence after complexifying coefficients. -/
theorem complexify_identifyLast_peakValueTranslated_succ
    (n : ℕ) (hn : 2 ≤ n) :
    complexifyMv (identifyLast n (peakValueTranslated (n + 1))) =
      (C (n + 1 : ℂ) + C (n - 1 : ℂ) * X none) *
          rename some (complexifyMv (peakValueTranslated n)) -
        C 2 * (1 + X none) *
          ∑ j : Fin n, X (some j) *
            pderiv (some j)
              (rename some (complexifyMv (peakValueTranslated n))) := by
  have h := congrArg complexifyMv
    (identifyLast_peakValueTranslated_succ n hn)
  unfold complexifyMv at h ⊢
  have hpderiv (j : Fin n) :
      map Complex.ofRealHom
          (pderiv (some j) (liftOld (peakValueTranslated n))) =
        pderiv (some j)
          (rename some (map Complex.ofRealHom (peakValueTranslated n))) := by
    rw [liftOld]
    rw [← MvPolynomial.pderiv_map, MvPolynomial.map_rename]
  simp only [map_add, map_mul, map_sub, map_sum] at h
  simp_rw [hpderiv] at h
  simpa [liftOld, MvPolynomial.map_rename] using h

theorem coeff_zero_complexify_peakValueTranslated (n : ℕ) :
    coeff 0 (complexifyMv (peakValueTranslated n)) =
      ((n.factorial : ℝ) : ℂ) := by
  rw [complexifyMv, coeff_map]
  change ((constantCoeff (peakValueTranslated n) : ℝ) : ℂ) = _
  rw [← eval_zero', eval_zero_peakValueTranslated]

/-- Up to rank two, no permutation has an interior peak. -/
theorem peakValueTranslated_eq_C_factorial_of_le_two
    {n : ℕ} (hn : n ≤ 2) :
    peakValueTranslated n = C (n.factorial : ℝ) := by
  classical
  have hempty (π : Equiv.Perm (Fin n)) : peakValues π = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hv2 := two_le_value_of_mem_peakValues hv
    have hvlt := v.isLt
    lia
  simp [peakValueTranslated, hempty, Fintype.card_perm]

theorem rename_some_eulerOperator {σ R : Type*}
    [Fintype σ] [CommRing R] (P : MvPolynomial σ R) :
    rename some (eulerOperator P) =
      ∑ i : σ, X (some i) * pderiv (some i) (rename some P) := by
  rw [eulerOperator, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, rename_X,
    ← MvPolynomial.pderiv_rename (Option.some_injective σ) i P]

/-- A homogeneous stable lift of the translated peak-value enumerator. -/
def PeakHomogeneousStable (n : ℕ) : Prop :=
  ∃ Q : MvPolynomial (Option (Fin n)) ℂ,
    Q.IsHomogeneous ((n - 1) / 2) ∧
      MvUpperHalfPlaneStable Q ∧
      dehomogenize Q = complexifyMv (peakValueTranslated n)

theorem peakHomogeneousStable_of_le_two {n : ℕ} (hn : n ≤ 2) :
    PeakHomogeneousStable n := by
  let c : ℂ := ((n.factorial : ℝ) : ℂ)
  refine ⟨C c, ?_, ?_, ?_⟩
  · have hd : (n - 1) / 2 = 0 := by lia
    rw [hd]
    exact isHomogeneous_C (Option (Fin n)) c
  · have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast Nat.factorial_ne_zero n
    simpa using (MvUpperHalfPlaneStable.one.C_mul hc)
  · rw [peakValueTranslated_eq_C_factorial_of_le_two hn]
    simp [complexifyMv, c]

private theorem even_degree (k : ℕ) :
    (2 * k - 1) / 2 = k - 1 := by
  cases k with
  | zero => simp
  | succ k =>
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by lia]
      rw [show 2 * k + 1 = 1 + 2 * k by lia,
        Nat.add_mul_div_left 1 k (by decide : 0 < 2)]
      simp

private theorem odd_degree (k : ℕ) : (2 * k + 1) / 2 = k := by
  rw [show 2 * k + 1 = 1 + 2 * k by lia,
    Nat.add_mul_div_left 1 k (by decide : 0 < 2)]
  simp

private theorem dehomogenize_evenStep_eq_recurrence
    (n d : ℕ) (hn : 2 ≤ n) (hnd : n = 2 * d + 1)
    (Q : MvPolynomial (Option (Fin n)) ℂ)
    (hhom : Q.IsHomogeneous d)
    (hdehom : dehomogenize Q =
      complexifyMv (peakValueTranslated n)) :
    dehomogenize (homogeneousEvenStep Q) =
      complexifyMv (identifyLast n (peakValueTranslated (n + 1))) := by
  have hderiv := hhom.dehomogenize_pderiv_none
  rw [hdehom] at hderiv
  have hrec := complexify_identifyLast_peakValueTranslated_succ n hn
  rw [homogeneousEvenStep, map_mul,
    dehomogenize_homogeneousFactorDerivative, hdehom, hderiv]
  simp only [map_sub, map_mul, rename_C, map_ofNat]
  rw [rename_some_eulerOperator]
  have htwo : (2 : MvPolynomial (Option (Fin n)) ℂ) = C (2 : ℂ) := by
    symm
    exact map_ofNat (C : ℂ →+* MvPolynomial (Option (Fin n)) ℂ) 2
  rw [← htwo] at hrec
  rw [hrec]
  subst n
  norm_num [map_add, map_sub, map_natCast]
  rw [← htwo]
  ring

private theorem dehomogenize_oddStep_eq_recurrence
    (n d : ℕ) (hn : 2 ≤ n) (hnd : n = 2 * d + 2)
    (Q : MvPolynomial (Option (Fin n)) ℂ)
    (hhom : Q.IsHomogeneous d)
    (hdehom : dehomogenize Q =
      complexifyMv (peakValueTranslated n)) :
    dehomogenize (homogeneousOddStep Q) =
      complexifyMv (identifyLast n (peakValueTranslated (n + 1))) := by
  have hderiv := hhom.dehomogenize_pderiv_none
  rw [hdehom] at hderiv
  have hrec := complexify_identifyLast_peakValueTranslated_succ n hn
  rw [dehomogenize_homogeneousOddStep, hdehom, hderiv]
  simp only [map_sub, map_mul, rename_C]
  rw [rename_some_eulerOperator]
  have htwo : (2 : MvPolynomial (Option (Fin n)) ℂ) = C (2 : ℂ) := by
    symm
    exact map_ofNat (C : ℂ →+* MvPolynomial (Option (Fin n)) ℂ) 2
  rw [← htwo] at hrec
  rw [hrec]
  subst n
  norm_num [map_add, map_sub, map_natCast]
  rw [← htwo]
  ring

private theorem unidentify_complexified (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℝ) :
    rename (finSuccEquiv' (Fin.last n)).symm
        (complexifyMv (identifyLast n P)) =
      complexifyMv P := by
  simp [identifyLast, complexifyMv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.map_rename, MvPolynomial.rename_rename]

private def unidentifyHomogeneous (n : ℕ)
    (Q : MvPolynomial (Option (Option (Fin n))) ℂ) :
    MvPolynomial (Option (Fin (n + 1))) ℂ :=
  rename (Option.map (finSuccEquiv' (Fin.last n)).symm) Q

private theorem dehomogenize_unidentifyHomogeneous (n : ℕ)
    {Q : MvPolynomial (Option (Option (Fin n))) ℂ}
    (hQ : dehomogenize Q =
      complexifyMv (identifyLast n (peakValueTranslated (n + 1)))) :
    dehomogenize (unidentifyHomogeneous n Q) =
      complexifyMv (peakValueTranslated (n + 1)) := by
  rw [unidentifyHomogeneous, dehomogenize_rename_option_map, hQ,
    unidentify_complexified]

/-- Every translated peak-value enumerator admits a homogeneous stable lift. -/
theorem peakHomogeneousStable (n : ℕ) : PeakHomogeneousStable n := by
  induction n with
  | zero => exact peakHomogeneousStable_of_le_two (by lia)
  | succ n ih =>
      by_cases hsmall : n + 1 ≤ 2
      · exact peakHomogeneousStable_of_le_two hsmall
      have hn : 2 ≤ n := by lia
      obtain ⟨Q, hhom, hstable, hdehom⟩ := ih
      have htop :
          (optionEquivLeft ℂ (Fin n) Q).coeff ((n - 1) / 2) =
            C (((n.factorial : ℝ) : ℂ)) := by
        rw [hhom.optionEquivLeft_coeff_eq_C_coeff_zero_dehomogenize,
          hdehom, coeff_zero_complexify_peakValueTranslated]
      have hc : ((n.factorial : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
      · subst n
        have hkpos : 0 < k := by lia
        have hhom' : Q.IsHomogeneous (k - 1) := by
          simpa [even_degree] using hhom
        have htop' :
            (optionEquivLeft ℂ (Fin (2 * k)) Q).coeff (k - 1) =
              C (((2 * k).factorial : ℝ) : ℂ) := by
          simpa [even_degree] using htop
        let Qid := homogeneousOddStep Q
        refine ⟨unidentifyHomogeneous (2 * k) Qid, ?_, ?_, ?_⟩
        · have hQid := homogeneousOddStep_isHomogeneous hhom'
          have hdegree : k - 1 + 1 = k := by lia
          rw [unidentifyHomogeneous]
          simpa [hdegree] using hQid.rename_isHomogeneous
        · apply MvUpperHalfPlaneStable.rename
          exact hstable.homogeneousOddStep hhom' htop' hc
        · apply dehomogenize_unidentifyHomogeneous
          apply dehomogenize_oddStep_eq_recurrence (2 * k) (k - 1) hn
          · lia
          · exact hhom'
          · exact hdehom
      · subst n
        have hhom' : Q.IsHomogeneous k := by
          simpa using hhom
        have htop' :
            (optionEquivLeft ℂ (Fin (2 * k + 1)) Q).coeff k =
              C ((((2 * k + 1).factorial : ℝ) : ℂ)) := by
          simpa using htop
        let Qid := homogeneousEvenStep Q
        refine ⟨unidentifyHomogeneous (2 * k + 1) Qid, ?_, ?_, ?_⟩
        · rw [unidentifyHomogeneous]
          have htarget : (2 * k + 1 + 1 - 1) / 2 = k := by
            rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by lia,
              odd_degree]
          rw [htarget]
          exact (homogeneousEvenStep_isHomogeneous hhom').rename_isHomogeneous
        · apply MvUpperHalfPlaneStable.rename
          exact hstable.homogeneousEvenStep hhom' htop' hc
        · apply dehomogenize_unidentifyHomogeneous
          exact dehomogenize_evenStep_eq_recurrence
            (2 * k + 1) k hn (by rfl) Q hhom' hdehom

/-- The translated peak-value enumerator is multivariate real stable. -/
theorem peakValueTranslated_mvRealStable (n : ℕ) :
    MvRealStable (peakValueTranslated n) := by
  obtain ⟨Q, hhom, hstable, hdehom⟩ := peakHomogeneousStable n
  change MvUpperHalfPlaneStable (complexifyMv (peakValueTranslated n))
  rw [← hdehom]
  exact hstable.dehomogenize hhom

theorem complexify_translateVariablesByOne {σ : Type*}
    (P : MvPolynomial σ ℝ) :
    complexifyMv (translateVariablesByOne P) =
      MvPolynomial.aeval
        (fun i => MvPolynomial.C (1 : ℂ) + MvPolynomial.X i)
        (complexifyMv P) := by
  unfold complexifyMv translateVariablesByOne
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
      simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      rw [map_mul, map_mul, map_mul, hP]
      simp

/-- The peak-value enumerator is multivariate real stable in every rank. -/
theorem peakValuePolynomial_mvRealStable (n : ℕ) :
    MvRealStable (peakValuePolynomial n) := by
  have htranslated := peakValueTranslated_mvRealStable n
  rw [peakValueTranslated_eq_translateVariablesByOne] at htranslated
  change MvUpperHalfPlaneStable
    (complexifyMv (translateVariablesByOne (peakValuePolynomial n)))
      at htranslated
  rw [complexify_translateVariablesByOne] at htranslated
  exact MvUpperHalfPlaneStable.of_translate_add_real (fun _ => 1)
    htranslated

end

end RealRooted
