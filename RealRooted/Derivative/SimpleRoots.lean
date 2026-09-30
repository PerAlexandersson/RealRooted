import RealRooted.IteratedDerivativeShift
import RealRooted.SameDegreeDerivative

/-!
# Simple roots and strict bounds for derivatives

This file records two root facts for derivatives of split real polynomials.

* If no root has multiplicity above two, the derivative is nonzero, split, and
  has simple roots: a derivative root is either inherited from an exact double
  root or lies away from the roots of the original polynomial, and the latter
  case is ruled out by the strict logarithmic-derivative inequality.
* If all roots are at most `B` and a root at `B` is simple, every derivative
  root is strictly below `B`.
-/

open Polynomial

noncomputable section

namespace RealRooted

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
      rw [hx_eval, hxder_eval] at hstrict
      norm_num at hstrict
  · lia

/-- If a nonconstant split polynomial has all roots at most `B`, and its root
at `B` (when present) is simple, every root of its derivative is below `B`. -/
theorem roots_derivative_lt_of_roots_le_of_rootMultiplicity_eq_one
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
      calc
        f.derivative.roots.card = f.derivative.natDegree :=
          card_roots_of_splits hfder_splits
        _ = f.natDegree - 1 := f.natDegree_derivative
        _ = 0 := by simp [hdeg1]
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
      (mem_roots hfder0).mp hr
    have hBder_ne : f.derivative.eval B ≠ 0 :=
      eval_derivative_ne_zero_of_rootMultiplicity_eq_one hBroot (hBsimple hBroot)
    exact hBder_ne (by simpa [Polynomial.IsRoot.def] using hBder_root)
  · have hstrict : ∀ r ∈ f.roots, r < B := by
      intro r hr
      apply lt_of_le_of_ne (hbound r hr)
      intro hrB
      subst r
      exact hBroot ((mem_roots hf0).mp hr)
    exact roots_derivative_lt_of_roots_lt hf hdeg2 hstrict

end RealRooted
