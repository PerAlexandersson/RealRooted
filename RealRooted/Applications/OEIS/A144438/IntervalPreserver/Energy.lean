module

public import RealRooted.Interlacing.ResidueCriterion

/-!
# Residue energy for the A144438 diagonal family

The energy is indexed by the distinct roots of the denominator polynomial.
This matches the original-variable weight `1 / ((-r) * (1-r))` in the
diagonal induction.
-/

@[expose] public section

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The weighted residue energy of a numerator `k`, with positive companion
`h`, over the simple roots of `p`. -/
def a144438ResidueEnergy (p h k : ℝ[X]) : ℝ :=
  ∑ r ∈ p.roots.toFinset,
    (k.eval r / p.derivative.eval r) ^ 2 /
      ((h.eval r / p.derivative.eval r) * (-r) * (1 - r))

/-- The residue energy is nonnegative when the companion residues are
positive and all denominator roots are negative. -/
theorem a144438ResidueEnergy_nonneg {p h k : ℝ[X]}
    (hw : ∀ r ∈ p.roots, 0 < h.eval r / p.derivative.eval r)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    0 ≤ a144438ResidueEnergy p h k := by
  unfold a144438ResidueEnergy
  apply Finset.sum_nonneg
  intro r hr
  have hr' : r ∈ p.roots := Multiset.mem_toFinset.mp hr
  have hden : 0 < (h.eval r / p.derivative.eval r) * (-r) * (1 - r) := by
    have hrneg := hneg r hr'
    exact mul_pos (mul_pos (hw r hr') (neg_pos.mpr hrneg)) (by linarith)
  exact div_nonneg (sq_nonneg _) hden.le

end RealRooted.Applications.OEIS
