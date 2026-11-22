module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteZerosOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.Mathlib.MeasureTheory.Integral.Hankel
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Strict positivity of logarithmic-derivative moment matrices

A nonpolynomial Type-I entire function of order below one has infinitely many
distinct negative zeros. Its logarithmic-derivative measure consequently has
infinitely many distinct positive atoms. This makes every shifted Hankel
moment matrix positive definite and every such determinant strictly positive.

This is a consequence of the moment representation associated with Sokal's
Appendix A, Proposition 6. Simplicity of the entire function's zeros is not
required. The function is assumed nonzero at zero to define its Taylor data.
-/

public section

open Complex Polynomial MeasureTheory

namespace RealRooted

private theorem infinite_positive_slopes_of_infinite_zeros
    {f : ℂ → ℂ} (h0 : f 0 ≠ 0) {gamma : ℝ} {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (heq : f = fun z => f 0 * Complex.exp (gamma * z) * ∏' i, (1 + (a i : ℂ) * z))
    (hinf : Set.Infinite {x : ℝ | f x = 0}) :
    Set.Infinite {x : ℝ | 0 < x ∧ x ∈ Set.range a} := by
  by_contra hfin
  apply hinf
  apply ((Set.not_infinite.mp hfin).image (fun x : ℝ => -x⁻¹)).subset
  intro x hx
  have hz : (∏' i, (1 + (a i : ℂ) * (x : ℂ))) = 0 := by
    have hh := congrFun heq x
    rw [hx] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero h0 (Complex.exp_ne_zero _))
  have hsum : Summable (fun i => ‖(a i : ℂ) * (x : ℂ)‖) := by
    simpa only [norm_mul, norm_real] using hs.norm.mul_right ‖(x : ℂ)‖
  obtain ⟨i, hi⟩ := (TauCeti.tprod_one_add_eq_zero_iff hsum).mp hz
  have hreal : 1 + a i * x = 0 := by
    exact_mod_cast hi
  have hai : a i ≠ 0 := by intro h; rw [h, zero_mul, add_zero] at hreal; norm_num at hreal
  refine ⟨a i, ⟨lt_of_le_of_ne (ha i) (Ne.symm hai), Set.mem_range_self i⟩, ?_⟩
  change -(a i)⁻¹ = x
  field_simp
  nlinarith

private theorem infinite_positive_atoms_of_slopes {gamma : ℝ} {a : ℕ → ℝ}
    (hinf : Set.Infinite {x : ℝ | 0 < x ∧ x ∈ Set.range a}) :
    Set.Infinite {x : ℝ | 0 < x ∧ 0 <
      (ENNReal.ofReal gamma • Measure.dirac 0 +
        Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) : Measure ℝ) {x}} := by
  apply hinf.mono
  rintro x ⟨hx, i, rfl⟩
  refine ⟨hx, ?_⟩
  have hle := Measure.le_sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) i
  have hle' := Measure.le_iff.mp hle {a i} (measurableSet_singleton _)
  have hpos : 0 < (ENNReal.ofReal (a i) • Measure.dirac (a i)) {a i} := by
    simpa using (ENNReal.ofReal_pos.mpr hx)
  exact (hpos.trans_le hle').trans_le (by simp only [add_apply]; exact le_add_left le_rfl)

/-- Logarithmic-derivative moment matrices of nonpolynomial Type-I functions
of order below one are positive definite in every size and natural shift. -/
theorem IsLaguerrePolyaTypeI.posDef_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hnp : ∀ p : ℂ[X], f ≠ fun z => p.eval z) (n r : ℕ) :
    Matrix.PosDef (fun i j : Fin n =>
      let k := i.val + j.val + r
      (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv f) 0).re / k.factorial) := by
  obtain ⟨gamma, a, mu, _, ha, hs, heq, hmu, _, hsupport, hmom⟩ :=
    hf.exists_logDeriv_moment_measure_factorization h0
  have hi := infinite_positive_slopes_of_infinite_zeros h0 ha hs heq
    (hf.toLaguerrePolya.infinite_real_zeros_of_order_lt_one h0 horder hrho hnp)
  have hatoms : Set.Infinite {x : ℝ | 0 < x ∧ 0 < mu {x}} := by
    rw [hmu]
    exact infinite_positive_atoms_of_slopes hi
  have hnonneg : ∀ᵐ x ∂mu, 0 ≤ x :=
    (ae_iff.mpr hsupport).mono fun x hx => hx.1
  have hPD := MeasureTheory.posDef_integral_pow_hankel_of_infinite_atoms
    (fun k => (hmom k).1) hnonneg hatoms n r
  convert hPD using 1
  apply Iff.of_eq
  apply congrArg Matrix.PosDef
  funext i j
  have hsign : (-1 : ℂ) ^ (i.val + j.val + r) =
      Complex.ofReal ((-1 : ℝ) ^ (i.val + j.val + r)) := by norm_cast
  have hre : ((-1 : ℂ) ^ (i.val + j.val + r)).re =
      (-1 : ℝ) ^ (i.val + j.val + r) := by rw [hsign]; rfl
  have him : ((-1 : ℂ) ^ (i.val + j.val + r)).im = 0 := by rw [hsign]; rfl
  simpa [Complex.mul_re, hre, him] using congrArg Complex.re (hmom (i.val + j.val + r)).2

/-- Every shifted logarithmic-derivative Hankel determinant is strictly
positive for a nonpolynomial Type-I function of order below one. -/
theorem IsLaguerrePolyaTypeI.det_logDeriv_hankel_pos
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hnp : ∀ p : ℂ[X], f ≠ fun z => p.eval z) (n r : ℕ) :
    0 < Matrix.det (fun i j : Fin n =>
      let k := i.val + j.val + r
      (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv f) 0).re / k.factorial) :=
  (hf.posDef_logDeriv h0 horder hrho hnp n r).det_pos

end RealRooted
