module

public import RealRooted.Interlacing.Euclid
public import RealRooted.Interlacing.Reversal

/-!
# Reversal transport with rescaling and common factors

This module packages the standard transports needed when a normalized model is positively
rescaled, reversed, and given a fixed real-rooted factor.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Independent nonzero scalar multiples of an interlacing pair still interlace. -/
theorem Interlaces.C_mul_both {g f : ℝ[X]} (h : Interlaces g f) {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) : Interlaces (C c * g) (C d * f) := by
  apply (h.toStrictInterl.C_mul_left hc).C_mul_right hd |>.toInterlaces
  rw [natDegree_mul (C_ne_zero.mpr hc) h.2.1.1,
    natDegree_mul (C_ne_zero.mpr hd) h.1.1]
  simpa only [natDegree_C, zero_add] using h.2.2.1

/-- Positive rescaling of the variable preserves interlacing. -/
theorem Interlaces.comp_C_mul_X {g f : ℝ[X]} (h : Interlaces g f) {a : ℝ}
    (ha : 0 < a) : Interlaces (g.comp (C a * X)) (f.comp (C a * X)) := by
  apply (h.toStrictInterl.comp_C_mul_X ha).toInterlaces
  rw [natDegree_comp, natDegree_comp, Polynomial.natDegree_C_mul_X a ha.ne']
  simpa only [mul_one] using h.2.2.1

/-- After reversal at negative roots, a common nonzero real-rooted factor preserves
interlacing. -/
theorem interlaces_mul_reverse_of_roots_neg {g f q : ℝ[X]} (h : Interlaces g f)
    (hf : ∀ t ∈ f.roots, t < 0) (hg : ∀ t ∈ g.roots, t < 0)
    (hq : q.Splits) (hq0 : q ≠ 0) : Interlaces (q * g.reverse) (q * f.reverse) := by
  exact (interlaces_reverse_of_roots_neg h hf hg).mul_both_of_splits hq hq0

/-- A common power of `X` may be attached after reversing an interlacing pair with
negative roots. -/
theorem interlaces_X_pow_mul_reverse_of_roots_neg {g f : ℝ[X]} (h : Interlaces g f)
    (hf : ∀ t ∈ f.roots, t < 0) (hg : ∀ t ∈ g.roots, t < 0) (k : ℕ) :
    Interlaces (X ^ k * g.reverse) (X ^ k * f.reverse) := by
  exact interlaces_mul_reverse_of_roots_neg h hf hg (Splits.X_pow k)
    (pow_ne_zero k X_ne_zero)

end RealRooted
