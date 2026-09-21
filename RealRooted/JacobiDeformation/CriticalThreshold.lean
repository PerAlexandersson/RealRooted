import RealRooted.SameDegreeDerivative

/-!
# Strict derivative bounds at a simple upper endpoint

Differentiation keeps roots below a closed upper bound strictly below it when
the only possible endpoint root of the original polynomial is simple.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- If a nonconstant split polynomial has all roots at most `B`, and its root
at `B` (when present) is simple, every root of its derivative is below `B`. -/
theorem derivative_roots_lt_of_roots_le_of_root_simple_at_upper
    {f : ℝ[X]} {B : ℝ} (hf : f.Splits) (hdeg : f.natDegree ≠ 0)
    (hbound : ∀ r ∈ f.roots, r ≤ B)
    (hBsimple : f.IsRoot B → f.rootMultiplicity B = 1) :
    ∀ r ∈ f.derivative.roots, r < B := by
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hdeg
    simp [hf0]
  have hfder0 : f.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero hdeg
  by_cases hdeg1 : f.natDegree = 1
  · have hfder_splits : f.derivative.Splits := by
      rcases derivative_eq_zero_or_ne_zero_and_splits hf with hzero | hsplit
      · exact (hfder0 hzero).elim
      · exact hsplit.2
    have hcard : f.derivative.roots.card = 0 := by
      rw [card_roots_of_splits hfder_splits, f.natDegree_derivative, hdeg1]
      simp
    intro r hr
    have hroots : f.derivative.roots = 0 := Multiset.card_eq_zero.mp hcard
    simp [hroots] at hr
  have hdeg2 : 2 ≤ f.natDegree := by
    lia
  by_cases hBroot : f.IsRoot B
  · intro r hr
    have hrle : r ≤ B := roots_derivative_le_of_roots_le hf hdeg2 hbound r hr
    apply lt_of_le_of_ne hrle
    intro hrB
    subst r
    have hBder_root : f.derivative.IsRoot B :=
      (mem_roots hfder0).mpr hr
    have hBder_ne : f.derivative.eval B ≠ 0 :=
      eval_derivative_ne_zero_of_rootMultiplicity_eq_one hBroot (hBsimple hBroot)
    exact hBder_ne (by simpa [Polynomial.IsRoot.def] using hBder_root)
  · have hstrict : ∀ r ∈ f.roots, r < B := by
      intro r hr
      apply lt_of_le_of_ne (hbound r hr)
      intro hrB
      subst r
      exact hBroot ((mem_roots hf0).mpr hr)
    exact roots_derivative_lt_of_roots_lt hf hdeg2 hstrict

end RealRooted.JacobiDeformation
