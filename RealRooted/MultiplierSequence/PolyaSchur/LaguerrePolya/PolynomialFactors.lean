module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hadamard
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Zero.Nonempty
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Factorization

/-!
# Large polynomial factors of real entire functions

A nonpolynomial real entire function of order below one and having only real
zeros has real-rooted polynomial factors of arbitrarily large degree. Removing
these factors leaves a Laguerre–Pólya cofactor. Nonvanishing at the origin keeps
the factors and cofactor nonzero there.
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

/-- A zero-free entire function of order below one is constant, hence polynomial. -/
private theorem exists_zero_of_nonpolynomial {f : ℂ → ℂ} {rho : ℝ}
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) (hf : Differentiable ℂ f)
    (hnp : ∀ p : ℂ[X], f ≠ fun z => p.eval z) : ∃ z, f z = 0 := by
  exact horder.exists_zero_of_nonconstant hrho hf
    (by simpa only [eval_C] using hnp (C (f 0)))

/-- Conjugation symmetry descends through a power of a real linear factor. -/
private theorem conj_of_real_factor {f g : ℂ → ℂ} {r : ℝ} {m : ℕ}
    (hg : Continuous g) (hf : ∀ z, f (conj z) = conj (f z))
    (hfactor : ∀ z, f z = (z - r) ^ m * g z) :
    ∀ z, g (conj z) = conj (g z) := by
  have heq : (fun z => g (conj z)) = fun z => conj (g z) := by
    apply Continuous.ext_on (dense_compl_singleton (r : ℂ))
      (hg.comp continuous_conj) (continuous_conj.comp hg)
    intro z hz
    have hzr : z ≠ (r : ℂ) := by simpa using hz
    have hconjne : conj z - (r : ℂ) ≠ 0 := by
      intro hzero
      have h := congrArg conj (sub_eq_zero.mp hzero)
      exact hzr (by simpa using h)
    have h := hf z
    rw [hfactor, hfactor] at h
    simp only [map_mul, map_pow, map_sub, conj_ofReal] at h
    exact mul_left_cancel₀ (pow_ne_zero _ hconjne) h
  exact fun z => congrFun heq z

/-- Remove a full real zero while preserving all hypotheses needed for further extraction. -/
private theorem exists_real_root_factor {f : ℂ → ℂ} {rho : ℝ}
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0)
    (hnp : ∀ p : ℂ[X], f ≠ fun z => p.eval z) :
    ∃ (r : ℝ) (m : ℕ) (g : ℂ → ℂ), r ≠ 0 ∧ 0 < m ∧
      Differentiable ℂ g ∧ g 0 ≠ 0 ∧ TauCeti.OrderLE g rho ∧
      (∀ z, g (conj z) = conj (g z)) ∧ (∀ z, g z = 0 → z.im = 0) ∧
      (∀ p : ℂ[X], g ≠ fun z => p.eval z) ∧ ∀ z, f z = (z - r) ^ m * g z := by
  obtain ⟨z, hz⟩ := exists_zero_of_nonpolynomial horder hrho hf hnp
  have hreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzeros z hz]
  have hr0 : z.re ≠ 0 := by
    intro hr
    have : z = 0 := by rw [← hreal, hr]; simp
    exact hf0 (this ▸ hz)
  obtain ⟨g, hg, hgroot, hgorder, hfactor⟩ :=
    horder.exists_eq_sub_pow_mul hf ⟨0, hf0⟩ (z.re : ℂ)
  let m := analyticOrderNatAt f (z.re : ℂ)
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by lia
    have he := hfactor (z.re : ℂ)
    change f (z.re : ℂ) = _ ^ m * _ at he
    rw [hm0, pow_zero, one_mul, hreal, hz] at he
    apply hgroot
    rw [hreal]
    exact he.symm
  have hg0 : g 0 ≠ 0 := by
    intro hzero
    exact hf0 (by rw [hfactor, hzero, mul_zero])
  refine ⟨z.re, m, g, hr0, hm, hg, hg0, hgorder,
    conj_of_real_factor hg.continuous hconj hfactor, ?_, ?_, hfactor⟩
  · intro w hw
    exact hzeros w (by rw [hfactor, hw, mul_zero])
  · intro p hp
    apply hnp ((X - C (z.re : ℂ)) ^ m * p)
    funext w
    rw [hfactor, hp]
    simp [m]

/-- A nonpolynomial real entire function of order below one with only real
zeros has arbitrarily large real-rooted polynomial factors and LP cofactors. -/
theorem exists_polynomial_factor_of_order_lt_one {f : ℂ → ℂ} {rho : ℝ}
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0)
    (hnp : ∀ p : ℂ[X], f ≠ fun z => p.eval z) (N : ℕ) :
    ∃ (q : ℝ[X]) (g : ℂ → ℂ), q.Splits ∧ q.coeff 0 ≠ 0 ∧ N ≤ q.natDegree ∧
      IsLaguerrePolya g ∧ g 0 ≠ 0 ∧ ∀ z, f z = (q.map ofRealHom).eval z * g z := by
  induction N generalizing f with
  | zero =>
      refine ⟨1, f, Splits.one, by simp, Nat.zero_le _,
        isLaguerrePolya_of_orderLE_one (horder.mono hrho.le) hf hf0 hconj hzeros, hf0, ?_⟩
      intro z
      simp
  | succ N ih =>
      obtain ⟨r, m, g, hr, hm, hg, hg0, hgorder, hgconj, hgzeros, hgnp, hfactor⟩ :=
        exists_real_root_factor horder hrho hf hf0 hconj hzeros hnp
      obtain ⟨q, t, hq, hq0, hdegree, ht, ht0, hgt⟩ :=
        ih hgorder hg hg0 hgconj hgzeros hgnp
      have hqne : q ≠ 0 := by intro hz; simp [hz] at hq0
      refine ⟨(X - C r) ^ m * q, t, ((Splits.X_sub_C r).pow m).mul hq, ?_, ?_, ht, ht0, ?_⟩
      · rw [coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
          zero_sub, ← coeff_zero_eq_eval_zero]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hr)) hq0
      · rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hqne,
          natDegree_pow, natDegree_X_sub_C, mul_one]
        lia
      · intro z
        rw [hfactor, hgt]
        simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, mul_assoc]

end RealRooted
