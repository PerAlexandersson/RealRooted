import RealRooted.Applications.OEIS.A144438.LayerTotalCompanionDataRecurrence

/-!
# Stability induction for the Deco layer recurrence

This file packages the all-rank induction supplied by the lower two-rank
companion certificate.  It uses only the recurrence-defined layer totals and
their exact one-step Rayleigh criterion; no combinatorial model is involved.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- Stability at every rank is equivalent to the companion Rayleigh
certificate at every recurrence step. -/
theorem decoLayerTotal_mvRealStable_iff_forall_companionRayleighData :
    (∀ n, MvRealStable (decoLayerTotal n)) ↔
      ∀ n, DecoBottomTotalCompanionRayleighData n := by
  constructor
  · intro hstable n
    have hbottom : MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) :=
      (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh (n + 2)).mp
        (hstable (n + 2))
    exact
      (decoBottomTotal_add_two_isRayleigh_iff_stable_companionData
        n (hstable (n + 1))).mp hbottom
  · intro hdata
    have hsucc : ∀ n, MvRealStable (decoLayerTotal (n + 1)) := by
      intro n
      induction n with
      | zero => exact decoLayerTotal_one_mvRealStable
      | succ n ih =>
          have hbottom :=
            decoBottomTotal_add_two_isRayleigh_of_stable_companionData
              n ih (hdata n)
          exact
            (decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh
              (n + 2)).mpr hbottom
    intro n
    cases n with
    | zero => exact decoLayerTotal_zero_mvRealStable
    | succ n => exact hsucc n

/-- A one-step preservation theorem for the companion certificate propagates
stability and companion data simultaneously through the recurrence. -/
theorem decoLayerTotal_stable_and_companionData_of_preserved
    (hpreserve : ∀ n,
      MvRealStable (decoLayerTotal (n + 1)) →
        DecoBottomTotalCompanionRayleighData n →
          DecoBottomTotalCompanionRayleighData (n + 1)) :
    ∀ n, MvRealStable (decoLayerTotal (n + 1)) ∧
      DecoBottomTotalCompanionRayleighData n := by
  intro n
  induction n with
  | zero =>
      exact ⟨decoLayerTotal_one_mvRealStable,
        decoBottomTotalCompanionRayleighData_zero⟩
  | succ n ih =>
      have hbottom :=
        decoBottomTotal_add_two_isRayleigh_of_stable_companionData
          n ih.1 ih.2
      exact
        ⟨(decoLayerTotal_mvRealStable_iff_bottomTotal_isRayleigh
            (n + 2)).mpr hbottom,
          hpreserve n ih.1 ih.2⟩

/-- Consequently, preservation of the exact companion certificate is a
complete recurrence-level route to all-rank multivariate stability. -/
theorem decoLayerTotal_mvRealStable_of_companionData_preserved
    (hpreserve : ∀ n,
      MvRealStable (decoLayerTotal (n + 1)) →
        DecoBottomTotalCompanionRayleighData n →
          DecoBottomTotalCompanionRayleighData (n + 1)) :
    ∀ n, MvRealStable (decoLayerTotal n) := by
  intro n
  cases n with
  | zero => exact decoLayerTotal_zero_mvRealStable
  | succ n =>
      exact (decoLayerTotal_stable_and_companionData_of_preserved
        hpreserve n).1

/-- Thus all-rank stability is exactly the assertion that the companion
certificate is preserved by one recurrence step, under the current stability
and certificate invariants supplied by the induction. -/
theorem decoLayerTotal_mvRealStable_iff_companionData_preserved :
    (∀ n, MvRealStable (decoLayerTotal n)) ↔
      ∀ n, MvRealStable (decoLayerTotal (n + 1)) →
        DecoBottomTotalCompanionRayleighData n →
          DecoBottomTotalCompanionRayleighData (n + 1) := by
  constructor
  · intro hstable n _ _
    exact
      (decoLayerTotal_mvRealStable_iff_forall_companionRayleighData.mp
        hstable) (n + 1)
  · exact decoLayerTotal_mvRealStable_of_companionData_preserved

end

end RealRooted.Applications.OEIS
