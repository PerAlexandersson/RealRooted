import RealRooted.DerivativeRecurrence.SecondDerivativeDegree
import RealRooted.GammaTransform.TwoStep

/-!
# Gamma-conjugated second-derivative families

Target module: `RealRooted.DerivativeRecurrence.SecondOrder.GammaFamily`.

This consolidates the generic transport layer developed downstream in
`ProofsOeis/SecondDerivativeTop.lean`, `ProofsOeis/EulerPencil.lean`, and
`ProofsOeis/SecondDerivativeA157Port.lean` for issue #1061. Credit for those
modules goes to Per Alexandersson and the downstream ProofsOeis/Claude Code
contributors.

The recurrence is used through `IsSecondDerivativeFamily`, which supplies the
ambient degree and the nonzero constant terms of the gamma polynomials. The
family-specific work remains the hypothesis `hpair`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A second-derivative family represented in gamma coordinates splits and
has interlacing adjacent rows once its gamma rows form strict interlacing
pairs. The explicit degree bound is essential because `gammaTransform d`
discards coefficients above `d / 2`.

On odd-to-even steps the proof uses
`strictInterl_gammaTransform_two_step`; even-to-odd steps use its underlying
adjacent-degree equivalence because the gamma row changes at every index. -/
theorem secondDerivativeGammaFamily
    {P G : ℕ → ℝ[X]} {b : ℝ}
    (hrec : IsSecondDerivativeFamily P b)
    (hgamma : ∀ n, P n = gammaTransform n (G n))
    (hdeg : ∀ n, (G n).natDegree ≤ n / 2)
    (hG : ∀ n, HasNonnegCoeffs (G n))
    (hpair : ∀ n, StrictInterl (G n) (G (n + 1))) :
    (∀ n, (P n).Splits) ∧
      (∀ n, Interlaces (P n) (P (n + 1))) := by
  have hcoeff (n : ℕ) : (G n).coeff 0 ≠ 0 := by
    have htop := (hrec.top_and_above n).1
    rw [hgamma n, coeff_ambient_gammaTransform] at htop
    grind
  have hstrict (n : ℕ) : StrictInterl (P n) (P (n + 1)) := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [hgamma (m + m), hgamma (m + m + 1)]
      exact
        (strictInterl_gammaTransform_succ_iff
          (hdeg (m + m)) (hdeg (m + m + 1))
          (hG (m + m)) (hG (m + m + 1))
          (hcoeff (m + m)) (hcoeff (m + m + 1))).2
            (hpair (m + m))
    · rw [hgamma (2 * m + 1), hgamma (2 * m + 1 + 1)]
      have hleft : (G (2 * m + 1)).natDegree ≤ m := by
        have h := hdeg (2 * m + 1)
        grind
      have hright : (G (2 * m + 1 + 1)).natDegree ≤ m + 1 := by
        have h := hdeg (2 * m + 1 + 1)
        grind
      have htwo := strictInterl_gammaTransform_two_step
        hleft hright (hG (2 * m + 1)) (hG (2 * m + 1 + 1))
        (hcoeff (2 * m + 1)) (hcoeff (2 * m + 1 + 1))
        (hpair (2 * m + 1))
      have hleftPad : (G (2 * m + 1)).natDegree ≤ (2 * m) / 2 := by
        grind
      rw [← gammaTransform_pad_one hleftPad] at htwo
      exact htwo.2
  refine ⟨fun n ↦ (hstrict n).1.2, fun n ↦ (hstrict n).toInterlaces ?_⟩
  rw [hrec.natDegree n, hrec.natDegree (n + 1)]

end RealRooted
