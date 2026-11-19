module

public import RealRooted.EffectiveBKW.Certificate.Positivity
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Rational isolating intervals

Opposite endpoint signs give existence, and a Bernstein certificate for a
signed derivative gives uniqueness. No Sturm computation is used.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open Polynomial BigDescents321.SmallCases Set

private theorem polynomial_derivativeFrom (p : IntPoly) (n : ℕ) :
    (ofList (IntPoly.derivativeFrom n p) : ℝ[X]) =
      C (n : ℝ) * ofList p + X * (ofList p).derivative := by
  induction p generalizing n with
  | nil => simp [IntPoly.derivativeFrom]
  | cons a p ih =>
    simp only [IntPoly.derivativeFrom, ofList_cons, ih, Int.cast_mul, Int.cast_natCast,
      Nat.cast_add, Nat.cast_one, derivative_add, derivative_C, derivative_mul,
      derivative_X, zero_add, one_mul, C_mul, C_add, C_1]
    ring

/-- The executable derivative agrees with the polynomial derivative. -/
theorem IntPoly.polynomial_derivative (p : IntPoly) :
    p.derivative.polynomial = p.polynomial.derivative := by
  cases p with
  | nil => simp [derivative, derivativeFrom, polynomial]
  | cons a p =>
    simp [derivative, polynomial, polynomial_derivativeFrom, ofList_cons, derivative_mul]

/-- Choose the sign of a polynomial using a Boolean. -/
def IntPoly.signed (neg : Bool) (p : IntPoly) : IntPoly :=
  p.scale (if neg then -1 else 1)

/-- Evaluation of a signed integer polynomial. -/
theorem IntPoly.eval_signed (neg : Bool) (p : IntPoly) (x : ℝ) :
    (p.signed neg).eval x = (if neg then -1 else 1 : ℝ) * p.eval x := by
  cases neg <;> simp [signed, eval_scale]

/-- Positivity of a signed derivative gives strict monotonicity of the signed polynomial. -/
theorem IntPoly.strictMonoOn_of_posOn_derivative {p : IntPoly} {lo hi : QNum} {neg : Bool}
    (h : (p.signed neg).derivative.posOn lo hi = true) :
    StrictMonoOn (p.signed neg).eval (Icc lo.val hi.val) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (p.signed neg).polynomial.continuous.continuousOn
  intro x hx
  rw [Polynomial.deriv, ← polynomial_derivative]
  exact IntPoly.posOn_sound h (interior_subset hx)

/-- A polynomial with a rational isolating interval and a derivative orientation. -/
structure IsolatedRoot where
  /-- Integer polynomial. -/
  p : IntPoly
  /-- Lower endpoint. -/
  lo : QNum
  /-- Upper endpoint. -/
  hi : QNum
  /-- Whether the derivative is negative. -/
  neg : Bool := false
  deriving Repr

/-- Check strict opposite signs and a strictly signed derivative. -/
def IsolatedRoot.check (c : IsolatedRoot) : Bool :=
  c.lo.valid && c.hi.valid && c.lo.lt c.hi &&
    decide (c.p.evalScaled c.lo.num c.lo.den * c.p.evalScaled c.hi.num c.hi.den < 0) &&
    (c.p.signed c.neg).derivative.posOn c.lo c.hi

/-- The interval of a checked certificate contains exactly one root, in its interior. -/
theorem IsolatedRoot.check_sound {c : IsolatedRoot} (h : c.check = true) :
    ∃! y : ℝ, y ∈ Ioo c.lo.val c.hi.val ∧ c.p.eval y = 0 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, hhi⟩, hlt⟩, hs⟩, hd⟩ := h
  have hlo' : (0 : ℝ) < c.lo.den := by
    exact_mod_cast (of_decide_eq_true hlo : 0 < c.lo.den)
  have hhi' : (0 : ℝ) < c.hi.den := by
    exact_mod_cast (of_decide_eq_true hhi : 0 < c.hi.den)
  have hs' : c.p.eval c.lo.val * c.p.eval c.hi.val < 0 := by
    have hsreal : (c.p.evalScaled c.lo.num c.lo.den : ℝ) *
        (c.p.evalScaled c.hi.num c.hi.den : ℝ) < 0 := by exact_mod_cast hs
    rw [IntPoly.evalScaled_eq _ _ hlo, IntPoly.evalScaled_eq _ _ hhi] at hsreal
    have hf := mul_pos (pow_pos hlo' c.p.length) (pow_pos hhi' c.p.length)
    have heq :
        ((c.lo.den : ℝ) ^ c.p.length * c.p.eval c.lo.val) *
            ((c.hi.den : ℝ) ^ c.p.length * c.p.eval c.hi.val) =
          ((c.lo.den : ℝ) ^ c.p.length * (c.hi.den : ℝ) ^ c.p.length) *
            (c.p.eval c.lo.val * c.p.eval c.hi.val) := by ring
    rw [heq] at hsreal
    rcases mul_neg_iff.mp hsreal with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hb
    · exact (not_lt_of_gt hf ha).elim
  have hab := (QNum.lt_sound hlo hhi hlt).le
  have hex : ∃ y ∈ Ioo c.lo.val c.hi.val, c.p.eval y = 0 := by
    rcases mul_neg_iff.mp hs' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact intermediate_value_Ioo' hab c.p.polynomial.continuous.continuousOn ⟨hb, ha⟩
    · exact intermediate_value_Ioo hab c.p.polynomial.continuous.continuousOn ⟨ha, hb⟩
  obtain ⟨y, hy, he⟩ := hex
  refine ⟨y, ⟨hy, he⟩, ?_⟩
  intro z hz
  apply (IntPoly.strictMonoOn_of_posOn_derivative hd).injOn
    ⟨hz.1.1.le, hz.1.2.le⟩ ⟨hy.1.le, hy.2.le⟩
  simp [IntPoly.eval_signed, hz.2, he]

end RealRooted.EffectiveBKW
