import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Endpoints
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ScalarBounds
import RealRooted.Interlacing.ResidueCriterion

/-!
# Residue energy for the A144438 diagonal family

The energy is indexed by the distinct roots of the denominator polynomial.
This matches the original-variable weight `1 / ((-r) * (1-r))` in the
diagonal induction.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The weighted residue energy of a numerator `k`, with positive companion
`h`, over the simple roots of `p`. -/
def a144438ResidueEnergy (p h k : ℝ[X]) : ℝ :=
  ∑ r ∈ p.roots.toFinset,
    (k.eval r / p.derivative.eval r) ^ 2 /
      ((h.eval r / p.derivative.eval r) * (-r) * (1 - r))

/-- The unweighted companion residue sum at a point outside the roots. -/
theorem a144438_sum_companion_residue_div
    {p h : ℝ[X]} (hp : p.Splits) (hpnd : p.roots.Nodup)
    (hpdeg : 1 ≤ p.natDegree) (hhdeg : h.degree < p.natDegree)
    {x : ℝ} (hpx : p.eval x ≠ 0) :
    h.eval x / p.eval x =
      ∑ r ∈ p.roots.toFinset,
        (h.eval r / p.derivative.eval r) / (x - r) :=
  eval_div_eq_sum_residue_div hp hpnd hpdeg hhdeg hpx

/-- The base residue energy has the value stated in the diagonal proof. -/
theorem a144438ResidueEnergy_base (a : ℝ) :
    a144438ResidueEnergy (a144438Diagonal 1 a)
      (a144438DiagonalCompanion 1 a) (a144438DiagonalLag 1 a) =
        1 / (3 * (1 + a) * (2 + a)) := by
  rw [a144438Diagonal_one, a144438DiagonalCompanion_one,
    a144438DiagonalLag_one]
  have hpoly : X + C (1 + a) = X - C (-(1 + a)) := by
    simp only [map_add, map_one, map_neg]
    ring
  rw [hpoly, a144438ResidueEnergy, roots_X_sub_C]
  simp only [neg_add_rev, Multiset.toFinset_singleton, eval_one, map_add,
    map_neg, map_one, derivative_sub, derivative_X, derivative_C, neg_zero,
    derivative_one, add_zero, sub_zero, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, one_pow, eval_ofNat, div_one, mul_neg,
    neg_mul, one_div, inv_neg, mul_inv_rev, Finset.sum_neg_distrib,
    Finset.sum_singleton]
  rw [show 1 - (-a + -1) = 2 + a by ring,
    show -a + -1 = -(1 + a) by ring, inv_neg]
  ring

/-- On `a ∈ [0,1]`, the base energy is at most one sixth. -/
theorem a144438ResidueEnergy_base_le_one_sixth {a : ℝ}
    (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) :
    a144438ResidueEnergy (a144438Diagonal 1 a)
      (a144438DiagonalCompanion 1 a) (a144438DiagonalLag 1 a) ≤ 1 / 6 := by
  rw [a144438ResidueEnergy_base]
  have hden : 0 < 3 * (1 + a) * (2 + a) := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- In particular, the base residue energy is at most one. -/
theorem a144438ResidueEnergy_base_le_one {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a144438ResidueEnergy (a144438Diagonal 1 a)
      (a144438DiagonalCompanion 1 a) (a144438DiagonalLag 1 a) ≤ 1 := by
  linarith [a144438ResidueEnergy_base_le_one_sixth ha0 ha1]

end RealRooted.Applications.OEIS
