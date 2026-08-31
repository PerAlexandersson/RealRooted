import RealRooted.AffineFamily.Basic
import RealRooted.PosCombo

/-!
# Affine family: positive-family packaging

The affine two-parameter family induces a one-parameter
`PosComboRealRooted` certificate.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem posComboRealRooted_of_affine_family {f g : ℝ[X]}
    (h :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    {t : ℝ} (ht : 0 < t) :
    PosComboRealRooted (C t * f + g) (X * f) := by
  intro lam μ hlam hμ
  have hbase :
      ((((C (μ / lam) * X + C t) * f) + g) ≠ 0 ∧
        (((C (μ / lam) * X + C t) * f) + g).Splits) :=
    h (by positivity) ht
  have hscaled :
      ((C lam * ((((C (μ / lam) * X + C t) * f) + g))) ≠ 0 ∧
        (C lam * ((((C (μ / lam) * X + C t) * f) + g))).Splits) :=
    isRealRooted_C_mul hbase.1 hbase.2 hlam.ne'
  have hEq :
      C lam * ((((C (μ / lam) * X + C t) * f) + g))
        = C lam * (C t * f + g) + C μ * (X * f) := by
    have hmain : C lam * ((C (μ / lam) * X) * f) = C μ * (X * f) := by
      calc
        C lam * ((C (μ / lam) * X) * f)
            = C lam * (C (μ / lam) * (X * f)) := by grind
        _ = (C lam * C (μ / lam)) * (X * f) := by grind
        _ = C (lam * (μ / lam)) * (X * f) := by simp
        _ = C μ * (X * f) := by grind
    grind
  lia

end RealRooted
