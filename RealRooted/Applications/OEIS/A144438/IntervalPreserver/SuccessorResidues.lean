import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ResidueDerivative

/-!
# Residues at an A144438 insertion successor

We differentiate the finite partial-fraction expansion directly.  At a new
root `ρ`, this identifies `q'(ρ)/p(ρ)` with the positive secular norm
`1 + ∑ (-r)w_r/(ρ-r)²`.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The derivative of an insertion successor at one of its roots, in terms
of the old companion residues. -/
theorem a144438_insertion_derivative_at_root
    {p h : ℝ[X]} (hp : p.Splits) (hpnd : p.roots.Nodup)
    (hpdeg : 1 ≤ p.natDegree) (hhdeg : h.degree < p.natDegree)
    {a ρ : ℝ}
    (hρ : ((1 + X + C a) * p + X * h).IsRoot ρ)
    (hpρ : p.eval ρ ≠ 0) :
    ((1 + X + C a) * p + X * h).derivative.eval ρ =
      p.eval ρ *
        (1 + ∑ r ∈ p.roots.toFinset,
          (-r) * (h.eval r / p.derivative.eval r) / (ρ - r) ^ 2) := by
  let S₁ : ℝ := ∑ r ∈ p.roots.toFinset,
    (h.eval r / p.derivative.eval r) / (ρ - r)
  let S₂ : ℝ := ∑ r ∈ p.roots.toFinset,
    (h.eval r / p.derivative.eval r) / (ρ - r) ^ 2
  have hpartial := a144438_sum_companion_residue_div hp hpnd hpdeg hhdeg hpρ
  have hevalh : h.eval ρ = p.eval ρ * S₁ := by
    have := (div_eq_iff hpρ).mp hpartial
    simpa only [S₁, mul_comm] using this
  have hderivative := eval_derivative_eq_residue_sums
    hp hpnd hpdeg hhdeg hpρ
  have hevalhDerivative :
      h.derivative.eval ρ = p.derivative.eval ρ * S₁ - p.eval ρ * S₂ := by
    simpa only [S₁, S₂] using hderivative
  have hrootEval :
      (1 + ρ + a) * p.eval ρ + ρ * h.eval ρ = 0 := by
    simpa [Polynomial.IsRoot.def] using hρ
  have hrootFactor : 1 + ρ + a + ρ * S₁ = 0 := by
    rw [hevalh] at hrootEval
    apply (mul_eq_zero.mp ?_).resolve_right hpρ
    calc
      (1 + ρ + a + ρ * S₁) * p.eval ρ =
          (1 + ρ + a) * p.eval ρ + ρ * (p.eval ρ * S₁) := by ring
      _ = 0 := hrootEval
  have hsum :
      S₁ - ρ * S₂ =
        ∑ r ∈ p.roots.toFinset,
          (-r) * (h.eval r / p.derivative.eval r) / (ρ - r) ^ 2 := by
    dsimp [S₁, S₂]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrroot : p.IsRoot r :=
      isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    have hρr : ρ - r ≠ 0 := by
      intro hzero
      have : ρ = r := sub_eq_zero.mp hzero
      subst r
      exact hpρ hrroot
    field_simp [hρr]
    ring
  simp only [derivative_add, derivative_mul, derivative_one, derivative_X,
    derivative_C, zero_add, add_zero, one_mul, eval_add, eval_mul, eval_one,
    eval_X, eval_C]
  rw [hevalh, hevalhDerivative, ← hsum]
  calc
    _ = p.eval ρ * (1 + S₁ - ρ * S₂) +
        p.derivative.eval ρ * (1 + ρ + a + ρ * S₁) := by ring
    _ = p.eval ρ * (1 + S₁ - ρ * S₂) := by rw [hrootFactor]; ring
    _ = p.eval ρ * (1 + (S₁ - ρ * S₂)) := by ring

end RealRooted.Applications.OEIS
