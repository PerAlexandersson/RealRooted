module

public import RealRooted.LaguerreInequalities.Analytic
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Derivative formula for generalized Laguerre coefficients

The even Taylor coefficient of the opposite imaginary translates is the
alternating binomial sum of derivatives in the generalized Laguerre inequalities.
See Cardon, *Extended Laguerre inequalities and a criterion for real zeros*,
Theorem 1.1, https://arxiv.org/abs/0911.1122.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

private theorem iteratedDeriv_affine_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (a b : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => f (a + z * b)) 0 = b ^ n * iteratedDeriv n f a := by
  have h := congrFun (iteratedDeriv_comp_const_mul
    ((hf.comp (by fun_prop)).contDiff : ContDiff ℂ n (fun z => f (a + z))) b) 0
  change iteratedDeriv n (fun z => f (a + b * z)) 0 =
    b ^ n * iteratedDeriv n (fun z => f (a + z)) (b * 0) at h
  rw [iteratedDeriv_comp_const_add] at h
  simpa only [mul_zero, add_zero, mul_comm] using h

private theorem imaginary_phase {n j : ℕ} (hj : j ≤ 2 * n) :
    I ^ j * (-I) ^ (2 * n - j) = (-1 : ℂ) ^ (j + n) := by
  have h : I ^ j = (-1 : ℂ) ^ j * (-I) ^ j := by
    rw [← mul_pow]
    simp
  rw [h, mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  simp [pow_mul, pow_add]

private theorem iteratedDeriv_laguerreProduct_even {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (x : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (laguerreProduct f x) 0 =
      ∑ j ∈ Finset.range (2 * n + 1),
        (-1 : ℂ) ^ (j + n) * (2 * n).choose j *
          iteratedDeriv j f x * iteratedDeriv (2 * n - j) f x := by
  have hminus : (fun z : ℂ => f ((x : ℂ) - z * I)) =
      (fun z => f ((x : ℂ) + z * (-I))) := by
    ext z
    congr 1
    ring
  change iteratedDeriv (2 * n) (fun z => f ((x : ℂ) + z * I) *
    f ((x : ℂ) - z * I)) 0 = _
  have hp : ContDiffAt ℂ (2 * n) (fun z => f ((x : ℂ) + z * I)) 0 :=
    (hf.comp (by fun_prop)).contDiff.contDiffAt
  have hm : ContDiffAt ℂ (2 * n) (fun z => f ((x : ℂ) - z * I)) 0 :=
    (hf.comp (by fun_prop)).contDiff.contDiffAt
  rw [iteratedDeriv_fun_mul hp hm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hminus, iteratedDeriv_affine_zero hf, iteratedDeriv_affine_zero hf]
  have hphase := imaginary_phase (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc
    _ = (I ^ j * (-I) ^ (2 * n - j)) * (2 * n).choose j *
        iteratedDeriv j f x * iteratedDeriv (2 * n - j) f x := by ring
    _ = _ := by rw [hphase]

/-- The alternating binomial derivative formula for the generalized Laguerre
coefficient of a real entire function. -/
theorem laguerreCoefficient_eq_sum {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (x : ℝ) (n : ℕ) :
    laguerreCoefficient f x n =
      (∑ j ∈ Finset.range (2 * n + 1),
        (-1 : ℝ) ^ (j + n) * (2 * n).choose j *
          (iteratedDeriv j f x).re * (iteratedDeriv (2 * n - j) f x).re) /
        (2 * n).factorial := by
  have hreal (k : ℕ) : ((iteratedDeriv k f x).re : ℂ) = iteratedDeriv k f x := by
    apply conj_eq_iff_re.mp
    simpa using (iteratedDeriv_conj hc k (x : ℂ)).symm
  rw [laguerreCoefficient, iteratedDeriv_laguerreProduct_even hf]
  congr 1
  change Complex.reCLM (∑ j ∈ Finset.range (2 * n + 1), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hreal j, ← hreal (2 * n - j)]
  norm_cast

/-- The order-zero generalized Laguerre coefficient is the square of the
value on the real axis. -/
theorem laguerreCoefficient_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (x : ℝ) :
    laguerreCoefficient f x 0 = (f x).re ^ 2 := by
  rw [laguerreCoefficient_eq_sum hf hc]
  simp [pow_two]

/-- The order-one generalized coefficient has the classical Laguerre
normalization `f'² - f f''`. -/
theorem laguerreCoefficient_one {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (x : ℝ) :
    laguerreCoefficient f x 1 =
      (iteratedDeriv 1 f x).re ^ 2 - (f x).re * (iteratedDeriv 2 f x).re := by
  rw [laguerreCoefficient_eq_sum hf hc]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero]
  ring

/-- The order-two generalized coefficient agrees with the second Laguerre
form, including its factor `1 / 12`. -/
theorem laguerreCoefficient_two {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (x : ℝ) :
    laguerreCoefficient f x 2 =
      (3 * (iteratedDeriv 2 f x).re ^ 2 -
        4 * (iteratedDeriv 1 f x).re * (iteratedDeriv 3 f x).re +
        (f x).re * (iteratedDeriv 4 f x).re) / 12 := by
  rw [laguerreCoefficient_eq_sum hf hc]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, Nat.choose_succ_succ]
  ring

end RealRooted
