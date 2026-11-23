module

public import RealRooted.SimpleRoots
public import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.Ring

/-!
# Affine invariance of simple real roots
-/

public section

open Polynomial

namespace RealRooted

/-- Translating a polynomial preserves simple real-rootedness. -/
theorem IsSimpleRealRooted.comp_X_add_C {P : ℝ[X]}
    (hP : IsSimpleRealRooted P) (a : ℝ) :
    IsSimpleRealRooted (P.comp (X + C a)) := by
  refine ⟨comp_X_add_C_ne_zero_iff.mpr hP.1, hP.2.1.comp_X_add_C a, ?_⟩
  simpa only [C_1, one_mul] using hP.2.2.comp_C_mul_X_add_C (b := a) one_ne_zero

/-- A nonzero root scaling preserves simple real-rootedness. -/
theorem IsSimpleRealRooted.scaleRoots {P : ℝ[X]}
    (hP : IsSimpleRealRooted P) {r : ℝ} (hr : r ≠ 0) :
    IsSimpleRealRooted (P.scaleRoots r) := by
  refine ⟨P.scaleRoots_ne_zero hP.1 r, hP.2.1.scaleRoots r, ?_⟩
  apply HasSimpleRoots.of_roots_nodup (P.scaleRoots_ne_zero hP.1 r)
  rw [roots_scaleRoots P (isUnit_iff_ne_zero.mpr hr)]
  exact hP.2.2.roots_nodup.map (mul_right_injective₀ hr)

/-- Simple real-rootedness is invariant under a nonzero root scaling. -/
theorem isSimpleRealRooted_scaleRoots_iff {P : ℝ[X]} {r : ℝ} (hr : r ≠ 0) :
    IsSimpleRealRooted (P.scaleRoots r) ↔ IsSimpleRealRooted P := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.scaleRoots hr⟩
  simpa only [← scaleRoots_mul, mul_inv_cancel₀ hr, scaleRoots_one] using
    h.scaleRoots (inv_ne_zero hr)

/-- Simple real-rootedness is invariant under translation. -/
theorem isSimpleRealRooted_comp_X_add_C_iff (P : ℝ[X]) (a : ℝ) :
    IsSimpleRealRooted (P.comp (X + C a)) ↔ IsSimpleRealRooted P := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_X_add_C a⟩
  have heq : (X + C a).comp (X + C (-a)) = (X : ℝ[X]) := by simp
  simpa only [comp_assoc, heq, comp_X] using h.comp_X_add_C (-a)

end RealRooted
