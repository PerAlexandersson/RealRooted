module

public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Algebra of polynomial differential operators

Polynomial symbols compose by multiplication on entire complex functions.
Linear factors act as derivative shifts, and every finite differential symbol
commutes with every iterated derivative.
-/

public section

namespace Polynomial

/-- A finite differential operator may be summed over the support of its symbol. -/
theorem differentialApply_eq_sum (p : ℂ[X]) (f : ℂ → ℂ) (z : ℂ) :
    p.differentialApply f z = p.sum (fun k a => a * iteratedDeriv k f z) := by
  rw [sum_over_range _ (fun _ => zero_mul _)]
  simp only [differentialApply, smul_eq_mul]

/-- Differential symbols add pointwise. -/
theorem differentialApply_add (p q : ℂ[X]) (f : ℂ → ℂ) :
    (p + q).differentialApply f = p.differentialApply f + q.differentialApply f := by
  ext z
  simp only [Pi.add_apply, differentialApply_eq_sum]
  exact sum_add_index p q _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- A monomial symbol is a scalar multiple of one iterated derivative. -/
@[simp] theorem differentialApply_monomial (n : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    (monomial n a).differentialApply f = fun z => a * iteratedDeriv n f z := by
  ext z
  rw [differentialApply_eq_sum]
  exact sum_monomial_index a (fun k b => b * iteratedDeriv k f z) (zero_mul _)

/-- A constant symbol acts by multiplication by that constant. -/
@[simp] theorem differentialApply_C (a : ℂ) (f : ℂ → ℂ) :
    (C a).differentialApply f = fun z => a * f z := by
  simpa only [monomial_zero_left, iteratedDeriv_zero] using
    differentialApply_monomial 0 a f

/-- The variable symbol acts by differentiation. -/
@[simp] theorem differentialApply_X (f : ℂ → ℂ) :
    (X : ℂ[X]).differentialApply f = deriv f := by
  simpa only [monomial_one_one_eq_X, iteratedDeriv_one, one_mul] using
    differentialApply_monomial 1 1 f

/-- The unit symbol acts as the identity. -/
@[simp] theorem differentialApply_one (f : ℂ → ℂ) :
    (1 : ℂ[X]).differentialApply f = f := by
  simpa only [C_1, one_mul] using differentialApply_C 1 f

/-- A finite differential operator sends the zero function to zero. -/
@[simp] theorem differentialApply_zero_input (p : ℂ[X]) :
    p.differentialApply (0 : ℂ → ℂ) = 0 := by
  ext z
  simp [differentialApply]

/-- A polynomial differential operator sends entire functions to entire functions. -/
theorem differentiable_differentialApply (p : ℂ[X]) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ (p.differentialApply f) := by
  unfold differentialApply
  apply Differentiable.fun_sum
  intro k _
  exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k
    (WithTop.coe_lt_top _)).const_smul (p.coeff k)

/-- Multiplication of symbols composes their actions on entire functions. -/
theorem differentialApply_mul (p q : ℂ[X]) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    (p * q).differentialApply f = p.differentialApply (q.differentialApply f) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [add_mul, differentialApply_add, hp, hr, differentialApply_add]
  | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add q r hq hr =>
          rw [mul_add, differentialApply_add, hq, hr, differentialApply_add,
            differentialApply_monomial, differentialApply_monomial,
            differentialApply_monomial]
          ext z
          rw [iteratedDeriv_add
            ((q.differentiable_differentialApply hf).contDiff.contDiffAt)
            ((r.differentiable_differentialApply hf).contDiff.contDiffAt)]
          simp only [Pi.add_apply, mul_add]
      | monomial m b =>
          rw [monomial_mul_monomial, differentialApply_monomial,
            differentialApply_monomial, differentialApply_monomial]
          ext z
          rw [iteratedDeriv_const_mul_field]
          simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply, mul_assoc]

/-- Multiplying the symbol by `X + C a` takes a derivative shift of its output. -/
theorem differentialApply_mul_X_add_C (p : ℂ[X]) (a : ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    (p * (X + C a)).differentialApply f =
      fun z => deriv (p.differentialApply f) z + a * p.differentialApply f z := by
  rw [mul_comm, differentialApply_mul _ _ hf, differentialApply_add,
    differentialApply_X, differentialApply_C]
  rfl

/-- Every finite differential symbol commutes with every iterated derivative. -/
theorem iteratedDeriv_differentialApply (p : ℂ[X]) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (p.differentialApply f) = p.differentialApply (iteratedDeriv n f) := by
  have hleft := differentialApply_mul (monomial n 1) p hf
  have hright := differentialApply_mul p (monomial n 1) hf
  rw [mul_comm] at hleft
  simpa only [differentialApply_monomial, one_mul] using hleft.symm.trans hright

/-- A derivative shift commutes with all iterated derivatives. -/
theorem iteratedDeriv_linear_differential {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => deriv f z + a * f z) =
      fun z => iteratedDeriv (n + 1) f z + a * iteratedDeriv n f z := by
  have h := iteratedDeriv_differentialApply (X + C a) hf n
  simpa only [differentialApply_add, differentialApply_X, differentialApply_C,
    ← iteratedDeriv_succ, Pi.add_def] using h

end Polynomial
