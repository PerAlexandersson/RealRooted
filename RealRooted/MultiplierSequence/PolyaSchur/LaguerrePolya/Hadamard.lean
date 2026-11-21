module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.Analysis.Complex.Hadamard.OrderOne
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Hadamard factorization and the Laguerre–Pólya class

A real entire function of order at most one, nonzero at the origin and having only
real zeros, belongs to the Laguerre–Pólya class. Tau Ceti's Hadamard theorem supplies
the factorization; finite products of its real elementary factors belong to the class,
and locally uniform convergence passes this property to the full product.
-/

public section

open Complex Polynomial Filter Metric Topology
open scoped ComplexConjugate

namespace RealRooted

private theorem isLaguerrePolya_eval_map {p : ℝ[X]} (hp : p.Splits) :
    IsLaguerrePolya (fun z => (p.map ofRealHom).eval z) := by
  apply IsLaguerrePolya.of_forall_approx
  intro R ε hε
  exact ⟨p, Or.inr hp, fun _ _ => by simpa using hε⟩

private theorem isLaguerrePolya_one : IsLaguerrePolya (fun _ : ℂ => 1) := by
  simpa using isLaguerrePolya_eval_map (p := 1) Splits.one

private theorem isLaguerrePolya_pow {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (n : ℕ) :
    IsLaguerrePolya (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using isLaguerrePolya_one
  | succ n ih => simpa [pow_succ, Pi.mul_def] using ih.mul hf

private theorem isLaguerrePolya_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsLaguerrePolya (f i)) :
    IsLaguerrePolya (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLaguerrePolya_one
  | @insert i s hi ih =>
      simpa [Finset.prod_insert hi, Pi.mul_def] using (hf i (by simp)).mul
        (ih fun j hj => hf j (by simp [hj]))

private theorem isLaguerrePolya_weierstrassFactor (a : ℝ) :
    IsLaguerrePolya (fun z => weierstrassFactor 1 ((a : ℂ) * z)) := by
  have hlin : IsLaguerrePolya (fun z : ℂ => 1 - (a : ℂ) * z) := by
    have hp : (1 - C a * X : ℝ[X]).Splits :=
      Splits.of_natDegree_le_one ((natDegree_sub_le _ _).trans
        (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))))
    simpa using isLaguerrePolya_eval_map hp
  simpa [weierstrassFactor_one_left, Pi.mul_def] using hlin.mul
    (isLaguerrePolya_exp.comp_affine_real a 0)

private theorem isLaguerrePolya_of_uniform_products {ι : Type*} (g : ι → ℂ → ℂ)
    (f : ℂ → ℂ) (hg : ∀ i, IsLaguerrePolya (g i))
    (hprod : HasProdLocallyUniformlyOn g f Set.univ) : IsLaguerrePolya f := by
  classical
  apply IsLaguerrePolya.of_forall_approx
  intro R ε hε
  have hlim := tendstoLocallyUniformlyOn_univ.mp
    (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim _
    (isCompact_closedBall (0 : ℂ) R)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨s, hs⟩ := (hU (ε / 2) (half_pos hε)).exists
  obtain ⟨p, hp, hpd⟩ := (isLaguerrePolya_prod s g (fun i _ => hg i)).exists_approx
    R (half_pos hε)
  refine ⟨p, hp, fun z hz => ?_⟩
  calc dist (f z) ((p.map ofRealHom).eval z)
      ≤ dist (f z) (∏ i ∈ s, g i z) +
        dist (∏ i ∈ s, g i z) ((p.map ofRealHom).eval z) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs z (mem_closedBall_zero_iff.mpr hz)) (hpd z hz)
    _ = ε := add_halves ε

/-- A real entire function of order at most one, nonzero at zero and with only real
zeros, is a locally uniform limit of real-rooted real polynomials. -/
theorem isLaguerrePolya_of_orderLE_one {f : ℂ → ℂ} (horder : TauCeti.OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0) : IsLaguerrePolya f := by
  have hsum := horder.summable_divisor_toNat_mul_norm_inv_sq hf (by norm_num)
  have hprod : IsLaguerrePolya (TauCeti.divisorProductOne f) := by
    rw [TauCeti.divisorProductOne_eq]
    apply isLaguerrePolya_of_uniform_products _ _ ?_
      (hasProdLocallyUniformlyOn_weierstrassFactor_one_pow _ _ hsum)
    intro ρ
    have hroot : f ρ = 0 := by
      by_contra hn
      exact ((hf.analyticAt _).notMem_divisor_support_of_ne_zero hn) ρ.property
    have hρ : ((ρ : ℂ).re : ℂ) = ρ :=
      conj_eq_iff_re.mp (conj_eq_iff_im.mpr (hzeros ρ hroot))
    have hinv : (((ρ : ℂ).re)⁻¹ : ℝ) = (ρ : ℂ)⁻¹ := by
      rw [ofReal_inv, hρ]
    rw [← hinv]
    exact isLaguerrePolya_pow (isLaguerrePolya_weierstrassFactor _) _
  have hzero : ((f 0).re : ℂ) = f 0 := by
    simpa using ofReal_re_iteratedDeriv_zero hconj 0
  have hderiv : ((deriv f 0).re : ℂ) = deriv f 0 := by
    simpa using ofReal_re_iteratedDeriv_zero hconj 1
  have hlog : (((deriv f 0).re / (f 0).re : ℝ) : ℂ) = logDeriv f 0 := by
    rw [ofReal_div, hderiv, hzero, logDeriv_apply]
  have h := ((isLaguerrePolya_exp.comp_affine_real
    ((deriv f 0).re / (f 0).re) 0).const_mul_real (f 0).re).mul hprod
  convert h using 1
  funext z
  simpa only [Pi.mul_apply, ofReal_zero, add_zero, hlog, hzero] using
    horder.eq_mul_cexp_logDeriv_mul_divisorProductOne hf hf0 z

end RealRooted
