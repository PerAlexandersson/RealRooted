module

public import RealRooted.SimpleRoots
public import Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Simple roots under degree reflection

Reflection can add a multiple zero when the degree bound exceeds the actual
degree. Simplicity away from that zero is sufficient to recover simplicity of
the original polynomial when its constant coefficient is nonzero.
-/

public section

open Polynomial

namespace RealRooted

/-- Simplicity away from zero after reflection implies simplicity before
reflection, provided the original polynomial has nonzero constant coefficient. -/
theorem HasSimpleRootsExcept.of_reflect {p : ℝ[X]} {d : ℕ}
    (hsimple : HasSimpleRootsExcept (reflect d p) 0)
    (hp0 : p.coeff 0 ≠ 0) (hp : p.Splits) (hd : p.natDegree ≤ d) :
    HasSimpleRoots p := by
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hp0
  have hrevne : p.reverse ≠ 0 := fun h => hpne (reverse_eq_zero.mp h)
  have hprod : X ^ (d - p.natDegree) * p.reverse ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hrevne
  apply HasSimpleRoots.of_roots_nodup hpne
  apply (Multiset.nodup_map_iff_of_injective inv_injective).mp
  rw [← roots_reverse_eq_map_inv hp hp0, Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_cases hr : p.reverse.IsRoot r
  · have hr0 : r ≠ 0 := by
      intro hz
      subst r
      apply leadingCoeff_ne_zero.mpr hpne
      simpa only [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_zero_reverse] using hr
    have hroot : (reflect d p).IsRoot r := by
      rw [reflect_eq_X_pow_mul_reverse p hd, IsRoot.def, eval_mul, hr.eq_zero, mul_zero]
    have hmult := hsimple r hr0 hroot
    rw [reflect_eq_X_pow_mul_reverse p hd, rootMultiplicity_mul hprod,
      rootMultiplicity_eq_zero (p := X ^ (d - p.natDegree))
        (by simpa only [IsRoot.def, eval_pow, eval_X] using pow_ne_zero (d - p.natDegree) hr0),
      zero_add] at hmult
    exact hmult.le
  · simp [rootMultiplicity_eq_zero hr]

/-- Simple reflected roots transfer back even when the reflection bound is not exact. -/
theorem HasSimpleRoots.of_reflect {p : ℝ[X]} {d : ℕ}
    (hsimple : HasSimpleRoots (reflect d p))
    (hp0 : p.coeff 0 ≠ 0) (hp : p.Splits) (hd : p.natDegree ≤ d) :
    HasSimpleRoots p :=
  (hsimple.hasSimpleRootsExcept 0).of_reflect hp0 hp hd

end RealRooted
