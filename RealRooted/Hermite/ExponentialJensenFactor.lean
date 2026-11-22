module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Hermite.PoulainExponential
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# The exceptional exponential factor of Jensen polynomials

For a polynomial symbol times `exp(a z)`, the Jensen polynomial of degree
bound `d ≥ deg q` has the factor `(1 + a X)^(d-deg q)` and an explicit residual
sum. The identity is algebraic: no real-rootedness or nonzero constant term
is needed. It is the factor formula in Craven–Csordas (1994), Proposition 4.1(2).
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- Translation commutes with every iterated formal derivative. -/
private theorem iterate_derivative_comp_translate (p : ℝ[X]) (a : ℝ) (k : ℕ) :
    (derivative^[k]) (p.comp (X + C a)) = ((derivative^[k]) p).comp (X + C a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, derivative_comp, derivative_X_add_C,
        one_mul, Function.iterate_succ_apply']

/-- Reflection distributes over finite polynomial sums. -/
private theorem reflect_finset_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) (d : ℕ) :
    reflect d (∑ k ∈ s, p k) = ∑ k ∈ s, reflect d (p k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp only [Finset.sum_insert hk, reflect_add, ih]

/-- Exact-degree reflection reverses each translated linear factor. -/
private theorem reflect_translate_power (a : ℝ) (m : ℕ) :
    reflect m ((X + C a) ^ m) = (1 + C a * X) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, reflect_mul _ _ (by simp) (by simp), ih]
      simp [pow_succ]

/-- A larger reflection bound contributes the extra power of the variable. -/
private theorem reflect_translate_power_of_le (a : ℝ) {m d : ℕ} (hm : m ≤ d) :
    reflect d ((X + C a) ^ m) = X ^ (d - m) * (1 + C a * X) ^ m := by
  have he : d = (d - m) + m := by lia
  rw [he]
  conv_lhs => rw [← one_mul ((X + C a) ^ m)]
  rw [reflect_mul _ _ (by simp) (by simp), reflect_one, reflect_translate_power]
  congr 2
  lia

/-- Reflecting the finite differential sum gives the unfactored Jensen expansion. -/
private theorem jensen_polynomial_exp_sum (q : ℝ[X]) (a : ℝ) (d : ℕ)
    (hd : q.natDegree ≤ d) :
    jensenPolynomial d (fun k =>
      (iteratedDeriv k (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re) =
      ∑ k ∈ Finset.range (q.natDegree + 1),
        C (q.coeff k * (d.descFactorial k : ℝ)) * (X ^ k * (1 + C a * X) ^ (d - k)) := by
  have h := taylor_polynomial_exp_eq_operator q (X ^ d) a
  rw [taylorDifferentialOperator_X_pow] at h
  have heq := congrArg (reflect d) h
  rw [reflect_reflect, applyAsDifferentialOperator, reflect_finset_sum] at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hd
  rw [iterate_derivative_comp_translate, iterate_derivative_X_pow_eq_C_mul,
    mul_comp, C_comp, pow_comp, X_comp, ← mul_assoc, ← C_mul,
    reflect_C_mul, reflect_translate_power_of_le a (Nat.sub_le _ _),
    Nat.sub_sub_self hkd]

/-- Exact exceptional factor formula for polynomial–exponential Jensen
polynomials. The descending factorial is `d! / (d-k)!` in this degree range. -/
theorem jensen_polynomial_exp_factor (q : ℝ[X]) (a : ℝ) (d : ℕ)
    (hd : q.natDegree ≤ d) :
    jensenPolynomial d (fun k =>
      (iteratedDeriv k (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re) =
      (1 + C a * X) ^ (d - q.natDegree) *
        ∑ k ∈ Finset.range (q.natDegree + 1),
          C (q.coeff k * (d.descFactorial k : ℝ)) *
            (X ^ k * (1 + C a * X) ^ (q.natDegree - k)) := by
  rw [jensen_polynomial_exp_sum q a d hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ q.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have he : d - k = (d - q.natDegree) + (q.natDegree - k) := by lia
  rw [he, pow_add]
  ring

end RealRooted
