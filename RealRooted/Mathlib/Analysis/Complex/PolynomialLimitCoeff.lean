module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Basic

/-!
# Coefficients of locally uniform limits of polynomials

If real polynomials converge locally uniformly on `ℂ` to `f`, then their iterated derivatives
converge locally uniformly (Weierstrass), and their `k`-th coefficients converge to the
`k`-th Taylor coefficient `f⁽ᵏ⁾(0) / k!` of `f`.
-/

public section

open Filter Topology

namespace Polynomial

/-- The `k`-th iterated derivative of a polynomial function is the polynomial function of the
`k`-th iterated formal derivative. -/
theorem iteratedDeriv_fun_eval {𝕜 : Type*} [NontriviallyNormedField 𝕜] (q : 𝕜[X]) (k : ℕ) :
    iteratedDeriv k (fun z => q.eval z) = fun z => (derivative^[k] q).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-- Evaluating the `k`-th formal derivative at `0` gives `k! * q.coeff k`. -/
theorem eval_zero_iterate_derivative {R : Type*} [CommSemiring R] (q : R[X]) (k : ℕ) :
    (derivative^[k] q).eval 0 = k.factorial * q.coeff k := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

end Polynomial

/-- Weierstrass: if entire functions converge locally uniformly on `ℂ`, then so do all their
iterated derivatives. -/
theorem TendstoLocallyUniformly.iteratedDeriv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) (hd : ∀ n, Differentiable ℂ (F n)) (k : ℕ) :
    TendstoLocallyUniformly (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f) atTop := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    rw [← tendstoLocallyUniformlyOn_univ] at ih ⊢
    simp only [iteratedDeriv_succ]
    exact ih.deriv (Eventually.of_forall fun n =>
      (((hd n).contDiff (n := ⊤)).differentiable_iteratedDeriv k
        (WithTop.coe_lt_top _)).differentiableOn) isOpen_univ

namespace Polynomial

/-- If real polynomials converge locally uniformly on `ℂ` to `f`, then their `k`-th
coefficients converge (in `ℂ`) to the `k`-th Taylor coefficient of `f` at `0`. -/
theorem tendsto_coeff_ofReal_of_tendstoLocallyUniformly {p : ℕ → ℝ[X]} {f : ℂ → ℂ}
    (hf : TendstoLocallyUniformly
      (fun n (z : ℂ) => ((p n).map Complex.ofRealHom).eval z) f atTop) (k : ℕ) :
    Tendsto (fun n => ((p n).coeff k : ℂ)) atTop
      (𝓝 (iteratedDeriv k f 0 / k.factorial)) := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hd : ∀ n, Differentiable ℂ fun z : ℂ => ((p n).map Complex.ofRealHom).eval z :=
    fun n => ((p n).map Complex.ofRealHom).differentiable
  have h := (tendstoLocallyUniformlyOn_univ.mpr (hf.iteratedDeriv hd k)).tendsto_at
    (Set.mem_univ (0 : ℂ))
  simp only [iteratedDeriv_fun_eval, eval_zero_iterate_derivative, coeff_map,
    Complex.ofRealHom_eq_coe] at h
  convert h.div_const (k.factorial : ℂ) using 2 with n
  rw [mul_div_cancel_left₀ _ hk]

/-- If real polynomials converge locally uniformly on `ℂ` to `f`, then their `k`-th
coefficients converge to the real part of the `k`-th Taylor coefficient of `f` at `0`. -/
theorem tendsto_coeff_of_tendstoLocallyUniformly {p : ℕ → ℝ[X]} {f : ℂ → ℂ}
    (hf : TendstoLocallyUniformly
      (fun n (z : ℂ) => ((p n).map Complex.ofRealHom).eval z) f atTop) (k : ℕ) :
    Tendsto (fun n => (p n).coeff k) atTop
      (𝓝 ((iteratedDeriv k f 0 / k.factorial).re)) := by
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp
    (tendsto_coeff_ofReal_of_tendstoLocallyUniformly hf k)

end Polynomial
