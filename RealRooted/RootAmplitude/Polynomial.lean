import RealRooted.Mathlib.Algebra.Polynomial.Splits.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial root-amplitude identities

The normalized derivative at a simple nonzero root equals a product over the
other roots.  This is the polynomial bridge for finite root-amplitude bounds.
-/

open Polynomial

namespace RealRooted.RootAmplitude

noncomputable section

/-- A root of a polynomial with nonzero constant term is nonzero. -/
theorem root_ne_zero {p : ℝ[X]} (hzero : p.eval 0 ≠ 0) {r : ℝ} (hroot : r ∈ p.roots) :
    r ≠ 0 := by
  rintro rfl
  exact hzero (Polynomial.mem_roots'.1 hroot).2

/-- The constant term of a split polynomial, with one root split off. -/
theorem eval_zero_eq_of_mem_roots {p : ℝ[X]} (hsplits : p.Splits) {s : ℝ}
    (hroot : s ∈ p.roots) :
    p.eval 0
      = p.leadingCoeff * ((-s) * ((p.roots.erase s).map (fun r : ℝ => -r)).prod) := by
  classical
  rw [hsplits.eval_eq_prod_roots 0]
  conv_lhs => rw [← Multiset.cons_erase hroot]
  rw [Multiset.map_cons, Multiset.prod_cons]
  ring_nf

/-- At a simple root of a split polynomial with nonzero constant term, the
normalized derivative equals minus the product of the factors from all other
roots. -/
theorem eval_deriv_root_div_eval_zero {p : ℝ[X]} (hsplits : p.Splits) {s : ℝ}
    (hroot : s ∈ p.roots) (hmultiplicity : p.roots.count s = 1) (hzero : p.eval 0 ≠ 0) :
    s * p.derivative.eval s / p.eval 0
      = -(((p.roots.erase s).map (fun r : ℝ => 1 - s / r)).prod) := by
  classical
  have hleading : p.leadingCoeff ≠ 0 := by
    intro hleading_zero
    exact hzero (by simp [Polynomial.leadingCoeff_eq_zero.mp hleading_zero])
  have hs_nonzero : s ≠ 0 := root_ne_zero hzero hroot
  have hroots_nonzero : ∀ r ∈ p.roots.erase s, r ≠ 0 := fun r hr =>
    root_ne_zero hzero (Multiset.mem_of_mem_erase hr)
  have hproduct_nonzero : (((p.roots.erase s).map (fun r : ℝ => -r)).prod) ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨r, hr, heq⟩ := hmem
    exact hroots_nonzero r hr (by linarith)
  have hderivative :=
    hsplits.eval_derivative_at_root_of_roots_count_one s hroot hmultiplicity
  have hconstant := eval_zero_eq_of_mem_roots hsplits hroot
  have hfactorization : ((p.roots.erase s).map (fun r : ℝ => s - r)).prod
      = (((p.roots.erase s).map (fun r : ℝ => 1 - s / r)).prod)
        * (((p.roots.erase s).map (fun r : ℝ => -r)).prod) := by
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl ?_
    intro r hr
    have hr_nonzero : r ≠ 0 := hroots_nonzero r hr
    field_simp
    ring
  rw [hderivative, hconstant, hfactorization]
  field_simp

end

end RealRooted.RootAmplitude
