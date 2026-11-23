module

public import RealRooted.Hermite.Generalized.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
import RealRooted.Hermite.Generalized.PositiveFactor
import RealRooted.Mathlib.Algebra.Polynomial.Expand.PowerRoots

/-!
# Root counts and multiplicities for generalized Hermite polynomials

For `d = s + p*q`, `p >= 2` and `s < p`, the origin has multiplicity `s`.
There are exactly `q` distinct positive roots. Every nonzero complex root
is simple. These are the multiplicity assertions in Kim--Kim (2015), Theorem 2.2.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- A positive-root polynomial does not vanish at zero. -/
private theorem eval_zero_ne_zero_of_roots_pos {Q : ℝ[X]} (hQ : Q ≠ 0)
    (hpos : ∀ a ∈ Q.roots, 0 < a) : Q.eval 0 ≠ 0 := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (hpos 0 ((mem_roots hQ).mpr h))

/-- The origin multiplicity is the remainder modulo the derivative stride. -/
theorem rootMultiplicity_zero_generalizedHermite {p s : ℕ}
    (hp : 2 ≤ p) (hs : s < p) (q : ℕ) :
    (generalizedHermite p (s + p * q)).rootMultiplicity 0 = s := by
  obtain ⟨c, Q, hc, hfactor, hQ, _, hpos⟩ :=
    generalizedHermite_eq_C_mul_X_pow_comp hp hs q
  rw [hfactor, rootMultiplicity_C_mul hc]
  exact rootMultiplicity_zero_X_pow_mul_comp
    (eval_zero_ne_zero_of_roots_pos hQ.1 hpos) (by lia) s

/-- The number of distinct positive roots is the quotient by the derivative stride. -/
theorem card_pos_roots_generalizedHermite {p s : ℕ}
    (hp : 2 ≤ p) (hs : s < p) (q : ℕ) :
    ((generalizedHermite p (s + p * q)).roots.toFinset.filter (0 < ·)).card = q := by
  obtain ⟨c, Q, hc, hfactor, hQ, hdeg, hpos⟩ :=
    generalizedHermite_eq_C_mul_X_pow_comp hp hs q
  rw [hfactor, roots_C_mul _ hc,
    card_pos_roots_X_pow_mul_comp hQ.1 hpos (by lia) s,
    Multiset.toFinset_card_of_nodup hQ.2.2.roots_nodup,
    hQ.2.1.natDegree_eq_card_roots.symm, hdeg]

/-- The complexification of a simple real-rooted polynomial has no multiple root. -/
private theorem map_eval_derivative_ne_zero {Q : ℝ[X]} (hQ : IsSimpleRealRooted Q)
    {z : ℂ} (hz : (Q.map ofRealHom).IsRoot z) :
    (Q.map ofRealHom).derivative.eval z ≠ 0 := by
  obtain ⟨a, ha⟩ := hQ.2.1.mem_range_of_isRoot hQ.1 hz
  have hreal : Q.IsRoot a := by
    apply ofRealHom.injective
    simpa only [← ha, IsRoot.def, eval_map_apply, map_zero] using hz
  have hder := hQ.2.2.eval_derivative_ne_zero hreal
  rw [← ha, derivative_map, eval_map_apply]
  exact ofReal_ne_zero.mpr hder

/-- Every nonzero complex root is simple, even when the stride exceeds two. -/
theorem rootMultiplicity_generalizedHermite_of_ne_zero {p s : ℕ}
    (hp : 2 ≤ p) (hs : s < p) (q : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hroot : ((generalizedHermite p (s + p * q)).map ofRealHom).IsRoot z) :
    ((generalizedHermite p (s + p * q)).map ofRealHom).rootMultiplicity z = 1 := by
  obtain ⟨c, Q, hc, hfactor, hQ, _, _⟩ :=
    generalizedHermite_eq_C_mul_X_pow_comp hp hs q
  have hcC : ofRealHom c ≠ 0 := (_root_.map_ne_zero ofRealHom).mpr hc
  have hpower : (Q.map ofRealHom).IsRoot (z ^ p) := by
    simpa only [hfactor, IsRoot.def, Polynomial.map_mul, map_C, Polynomial.map_pow,
      map_X, map_comp, eval_mul, eval_C, eval_pow, eval_X, eval_comp,
      mul_eq_zero, hcC, pow_ne_zero s hz, false_or] using hroot
  rw [hfactor, Polynomial.map_mul, map_C, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_comp, Polynomial.map_pow, map_X, rootMultiplicity_C_mul hcC]
  exact rootMultiplicity_X_pow_mul_comp_of_simple (by lia) s hz hpower
    (map_eval_derivative_ne_zero hQ hpower)

end RealRooted
