import RealRooted.IteratedDerivativeShift

/-!
# Simplicity after differentiating double-root-bounded polynomials

For a split real polynomial whose root multiplicities are at most two, a
derivative root is either inherited from an exact double root or lies away from
the roots of the original polynomial.  The latter case is ruled out by the
strict logarithmic-derivative inequality.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- A nonconstant split real polynomial with no root of multiplicity above two
has a nonzero, split derivative with simple roots. -/
theorem derivative_ne_zero_splits_hasSimpleRoots_of_rootMultiplicity_le_two
    {f : ℝ[X]} (hf : f.Splits) (hdeg : f.natDegree ≠ 0)
    (hmult : ∀ x : ℝ, f.rootMultiplicity x ≤ 2) :
    f.derivative ≠ 0 ∧ f.derivative.Splits ∧ HasSimpleRoots f.derivative := by
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hdeg
    simp [hf0]
  have hfder0 : f.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero hdeg
  have hfder_splits : f.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hf with hzero | hsplit
    · exact (hfder0 hzero).elim
    · exact hsplit.2
  refine ⟨hfder0, hfder_splits, ?_⟩
  intro x hx
  have hxpos : 0 < f.derivative.rootMultiplicity x :=
    (rootMultiplicity_pos hfder0).mpr hx
  apply Nat.le_antisymm
  · by_contra hle
    have hxmult : 2 ≤ f.derivative.rootMultiplicity x := by
      lia
    have hxder : f.derivative.derivative.IsRoot x :=
      isRoot_derivative_of_rootMultiplicity_ge_two hxmult
    by_cases hfx : f.IsRoot x
    · have hfmulti : 1 < f.rootMultiplicity x :=
        (one_lt_rootMultiplicity_iff_isRoot hf0).2 ⟨hfx, hx⟩
      have hfmulti_eq : f.rootMultiplicity x = 2 := by
        have hbound := hmult x
        lia
      have hsecond_ne :=
        eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two hf0 hfmulti_eq
      exact hsecond_ne (by simpa [Polynomial.IsRoot.def] using hxder)
    · have hfx_eval : f.eval x ≠ 0 := by
        simpa [Polynomial.IsRoot.def] using hfx
      have hx_eval : f.derivative.eval x = 0 := by
        simpa [Polynomial.IsRoot.def] using hx
      have hxder_eval : f.derivative.derivative.eval x = 0 := by
        simpa [Polynomial.IsRoot.def] using hxder
      have hstrict := deriv2_mul_lt_deriv_sq_at_non_root hf (by lia) hfx_eval
      nlinarith
  · lia

end RealRooted.JacobiDeformation
