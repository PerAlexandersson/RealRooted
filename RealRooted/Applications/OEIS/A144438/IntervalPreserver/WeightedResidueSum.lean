import RealRooted.Applications.OEIS.A144438.IntervalPreserver.SuccessorResidues

/-!
# The original-variable weighted residue sum

Subtracting the Lagrange expansions at zero and one produces exactly the
weight `1 / ((-r)(1-r))` used by the residue-energy contraction.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The weighted residue sum is the difference of the quotient evaluations
at zero and one. -/
theorem a144438_weighted_residue_sum_sub_eval
    {q p : ℝ[X]} (hq : q.Splits) (hqnd : q.roots.Nodup)
    (hqdeg : 1 ≤ q.natDegree) (hpdeg : p.degree < q.natDegree)
    (hq0 : q.eval 0 ≠ 0) (hq1 : q.eval 1 ≠ 0) :
    ∑ r ∈ q.roots.toFinset,
        (p.eval r / q.derivative.eval r) / ((-r) * (1 - r)) =
      p.eval 0 / q.eval 0 - p.eval 1 / q.eval 1 := by
  have hzero := eval_div_eq_sum_residue_div hq hqnd hqdeg hpdeg hq0
  have hone := eval_div_eq_sum_residue_div hq hqnd hqdeg hpdeg hq1
  rw [hzero, hone, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hrroot : q.IsRoot r :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    exact hq0 hrroot
  have hr1 : 1 - r ≠ 0 := by
    intro hr
    have : r = 1 := by linarith
    subst r
    exact hq1 hrroot
  field_simp [hr0, hr1]
  ring

end RealRooted.Applications.OEIS
