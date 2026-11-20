module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Uniqueness of normalized formal first-order equations

Invertible formal series allow a Wronskian proof of uniqueness, avoiding
coefficient recursions or analytic initial-value theorems.
-/

public section

namespace RealRooted.TuranHurwitz

/-- Unit solutions of a common first-order formal equation with the same constant term agree. -/
theorem eq_of_mul_derivative_eq {A : Type*} [CommRing A] [HasUniqueDiv A]
    {U V f g : PowerSeries A} (hU : IsUnit U) (hg : IsUnit g)
    (hf : U * PowerSeries.derivative f = V * f)
    (hgdiff : U * PowerSeries.derivative g = V * g)
    (hconst : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) : f = g := by
  obtain ⟨u, rfl⟩ := hg
  have hW : PowerSeries.derivative f * (u : PowerSeries A) -
      f * PowerSeries.derivative (u : PowerSeries A) = 0 := by
    apply hU.mul_left_cancel
    linear_combination (u : PowerSeries A) * hf - f * hgdiff
  have hQ : PowerSeries.derivative (f * (↑(u⁻¹) : PowerSeries A)) = 0 := by
    rw [PowerSeries.derivative.leibniz, PowerSeries.derivative_inv]
    simp only [smul_eq_mul]
    calc
      _ = ((↑(u⁻¹) : PowerSeries A)) ^ 2 *
          (PowerSeries.derivative f * (u : PowerSeries A) -
            f * PowerSeries.derivative (u : PowerSeries A)) := by
              linear_combination -(PowerSeries.derivative f *
                (↑(u⁻¹) : PowerSeries A)) * u.mul_inv
      _ = 0 := by rw [hW]; ring
  have hc : PowerSeries.constantCoeff (f * (↑(u⁻¹) : PowerSeries A)) = 1 := by
    rw [map_mul, hconst, ← map_mul, u.mul_inv, map_one]
  have heq : f * (↑(u⁻¹) : PowerSeries A) = 1 :=
    PowerSeries.derivative.ext (by rw [hQ, PowerSeries.derivative_one]) (by simpa using hc)
  calc
    f = (f * (↑(u⁻¹) : PowerSeries A)) * (u : PowerSeries A) := by
      rw [mul_assoc, u.inv_mul, mul_one]
    _ = u := by rw [heq, one_mul]

end RealRooted.TuranHurwitz
