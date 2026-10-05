import RealRooted.Applications.OEIS.A144438.IntervalPreserver.SuccessorResidues
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.SuccessorBlock

/-! # Polynomial residue identities at a weighted insertion successor -/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDeco_insertion_lag_at_root
    {p k : ℝ[X]} (hp : p.Splits) (hpnd : p.roots.Nodup)
    (hpdeg : 1 ≤ p.natDegree) (hkdeg : k.degree < p.natDegree)
    {a ρ : ℝ} (hpρ : p.eval ρ ≠ 0) :
    (p + C a * k).eval ρ =
      p.eval ρ * (1 + a * ∑ r ∈ p.roots.toFinset,
        (k.eval r / p.derivative.eval r) / (ρ - r)) := by
  have hpartial := a144438_sum_companion_residue_div
    hp hpnd hpdeg hkdeg hpρ
  have hkEval :
      k.eval ρ = p.eval ρ * ∑ r ∈ p.roots.toFinset,
        (k.eval r / p.derivative.eval r) / (ρ - r) := by
    have := (div_eq_iff hpρ).mp hpartial
    simpa only [mul_comm] using this
  simp only [eval_add, eval_mul, eval_C]
  rw [hkEval]
  ring

theorem weightedDeco_insertion_companion_at_root
    {p q kplus hplus : ℝ[X]} {a w n ρ D L A : ℝ}
    (hρ : q.IsRoot ρ)
    (hqDerivative : q.derivative.eval ρ = p.eval ρ * D)
    (hkplus : kplus.eval ρ = p.eval ρ * L)
    (hcompanion : hplus =
      (1 - X) * q.derivative + C (n + 1) * q -
        C ((n + 1) * a) * p + C w * kplus)
    (hblock : A = (1 - ρ) * D + w * L - (n + 1) * a) :
    hplus.eval ρ = p.eval ρ * A := by
  rw [hcompanion]
  have hqEval : q.eval ρ = 0 := hρ
  simp only [eval_add, eval_sub, eval_mul, eval_one, eval_X, eval_C,
    hqDerivative, hkplus, hqEval, mul_zero]
  rw [hblock]
  ring

theorem weightedDeco_insertion_residue_ratios
    {p q kplus hplus : ℝ[X]} {ρ D L A : ℝ}
    (hpρ : p.eval ρ ≠ 0)
    (hD : D ≠ 0)
    (hqDerivative : q.derivative.eval ρ = p.eval ρ * D)
    (hkplus : kplus.eval ρ = p.eval ρ * L)
    (hhplus : hplus.eval ρ = p.eval ρ * A) :
    p.eval ρ / q.derivative.eval ρ = 1 / D ∧
      kplus.eval ρ / q.derivative.eval ρ = L / D ∧
      hplus.eval ρ / q.derivative.eval ρ = A / D := by
  rw [hqDerivative, hkplus, hhplus]
  constructor
  · field_simp [hpρ, hD]
  constructor <;> field_simp [hpρ, hD]

end RealRooted.Applications.OEIS
