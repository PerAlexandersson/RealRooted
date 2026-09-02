import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Linarith

/-!
# Derivatives at simple roots of split polynomials

An upstream-shaped formula for the derivative at a root of multiplicity one,
without requiring the polynomial to be monic.
-/

namespace Polynomial

/-- At a simple member `s`, every summand indexed by another member contains the
zero factor `s - s`. -/
theorem derivative_sum_collapse {K : Type*} [Field K] [DecidableEq K]
    (M : Multiset K) (s : K)
    (hroot : s ∈ M) (hmultiplicity : M.count s = 1) :
    (M.map (fun r : K => ((M.erase r).map (fun t : K => s - t)).prod)).sum
      = ((M.erase s).map (fun t : K => s - t)).prod := by
  rw [← Multiset.cons_erase hroot, Multiset.map_cons, Multiset.sum_cons,
    Multiset.erase_cons_head]
  have hnot_mem : s ∉ M.erase s := by
    intro hmem
    rw [← Multiset.count_pos, Multiset.count_erase_self] at hmem
    lia
  have hrest : ((M.erase s).map (fun r : K =>
      (((s ::ₘ M.erase s).erase r).map (fun t : K => s - t)).prod)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro y hy
    simp only [Multiset.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    have hrs : r ≠ s := fun heq => hnot_mem (heq ▸ hr)
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨s, ?_, sub_self s⟩
    rw [Multiset.erase_cons_tail (M.erase s) (Ne.symm hrs)]
    simp
  simp_all

/-- The derivative at a root of multiplicity one is the leading coefficient
times the product of its differences from all the other roots. -/
theorem Splits.eval_derivative_at_root_of_roots_count_one {K : Type*} [Field K] [DecidableEq K]
    {p : K[X]} (hsplits : p.Splits) (s : K) (hroot : s ∈ p.roots)
    (hmultiplicity : p.roots.count s = 1) :
    p.derivative.eval s = p.leadingCoeff * ((p.roots.erase s).map (fun r => s - r)).prod := by
  rw [hsplits.eval_derivative, derivative_sum_collapse p.roots s hroot hmultiplicity]

end Polynomial
