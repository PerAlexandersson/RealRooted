import RealRooted.CombinatorialExamples.PeakValues.InsertionSum

/-!
# Translated peak-value recurrence

This file transports the insertion recurrence through the coordinate
translation `x ↦ 1 + x` used in the stability proof.
-/

namespace RealRooted

noncomputable section

open MvPolynomial

theorem translateVariablesByOne_rename {σ τ : Type*} (f : σ → τ)
    (P : MvPolynomial σ ℝ) :
    translateVariablesByOne (MvPolynomial.rename f P) =
      MvPolynomial.rename f (translateVariablesByOne P) := by
  unfold translateVariablesByOne
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
      simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      rw [map_mul, map_mul, hP]
      simp

theorem translateVariablesByOne_pderiv {σ : Type*} (i : σ)
    (P : MvPolynomial σ ℝ) :
    translateVariablesByOne (MvPolynomial.pderiv i P) =
      MvPolynomial.pderiv i (translateVariablesByOne P) := by
  classical
  unfold translateVariablesByOne
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
      simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
      by_cases hij : i = j
      · subst j
        rw [MvPolynomial.pderiv_mul]
        simp only [map_add, map_mul]
        rw [hP, MvPolynomial.pderiv_mul]
        simp
      · rw [MvPolynomial.pderiv_mul]
        simp only [map_add, map_mul]
        rw [hP, MvPolynomial.pderiv_mul]
        simp [hij]

theorem translateVariablesByOne_liftOld {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    translateVariablesByOne (liftOld P) =
      liftOld (translateVariablesByOne P) :=
  translateVariablesByOne_rename some P

theorem translateVariablesByOne_identifyLast (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℝ) :
    translateVariablesByOne (identifyLast n P) =
      identifyLast n (translateVariablesByOne P) :=
  translateVariablesByOne_rename (finSuccEquiv' (Fin.last n)) P

/-- The insertion recurrence after translating every variable by one. -/
theorem identifyLast_peakValueTranslated_succ (n : ℕ) (hn : 2 ≤ n) :
    identifyLast n (peakValueTranslated (n + 1)) =
      (C (n + 1 : ℝ) + C (n - 1 : ℝ) * X none) *
          liftOld (peakValueTranslated n) -
        C 2 * (1 + X none) *
          ∑ j : Fin n,
            X (some j) *
              pderiv (some j) (liftOld (peakValueTranslated n)) := by
  have h := congrArg translateVariablesByOne
    (identifyLast_peakValuePolynomial_succ n hn)
  rw [translateVariablesByOne_identifyLast,
    ← peakValueTranslated_eq_translateVariablesByOne] at h
  have hlift :
      MvPolynomial.aeval (fun i => 1 + X i)
          (liftOld (peakValuePolynomial n)) =
        liftOld (peakValueTranslated n) := by
    change translateVariablesByOne (liftOld (peakValuePolynomial n)) = _
    rw [translateVariablesByOne_liftOld,
      ← peakValueTranslated_eq_translateVariablesByOne]
  have hpderiv (j : Fin n) :
      MvPolynomial.aeval (fun i => 1 + X i)
          (pderiv (some j) (liftOld (peakValuePolynomial n))) =
        pderiv (some j) (liftOld (peakValueTranslated n)) := by
    change translateVariablesByOne
      (pderiv (some j) (liftOld (peakValuePolynomial n))) = _
    rw [translateVariablesByOne_pderiv,
      translateVariablesByOne_liftOld,
      ← peakValueTranslated_eq_translateVariablesByOne]
  unfold translateVariablesByOne at h
  simp only [map_add, map_mul, map_sub, map_sum, map_one, map_ofNat,
    map_natCast, aeval_X] at h
  simp_rw [hpderiv] at h
  rw [hlift] at h
  rw [h]
  simp only [map_add, map_sub, map_natCast, map_one, map_ofNat]
  have hterm (j : Fin n) :
      (1 - (1 + X (some j))) *
          pderiv (some j) (liftOld (peakValueTranslated n)) =
        -(X (some j) *
          pderiv (some j) (liftOld (peakValueTranslated n))) := by
    ring
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  ring

end

end RealRooted
