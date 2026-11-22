module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.ForwardDifference
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeICriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.PolynomialFactors
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Signed forward differences for Type-I functions below order one

A nonpolynomial positive Type-I function of order below one has a negative real
zero. Consequently its Taylor derivatives have a negative signed forward
difference of some positive order. This is a derived consequence of the Taylor
expansion and the zero-free growth theorem. It concerns all orders at a fixed
shift, and does not contradict eventual positivity in the shift at each fixed
order.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- A nonpolynomial positive Type-I function of order below one and with a
positive value at zero has a negative real zero. -/
theorem IsLaguerrePolyaTypeI.exists_neg_real_zero_of_order_lt_one
    {f : ℂ → ℂ} {rho : ℝ} (hf : IsLaguerrePolyaTypeI f)
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) (h0 : 0 < (f 0).re)
    (hnp : ∀ q : ℂ[X], f ≠ fun z => q.eval z) :
    ∃ x : ℝ, x < 0 ∧ f x = 0 := by
  have hf0 : f 0 ≠ 0 := by intro hz; simp [hz] at h0
  have hfn : f ≠ 0 := fun hz => hf0 (by simp [hz])
  have hlp := hf.toLaguerrePolya
  obtain ⟨q, g, hq, _, hdegree, _, _, hfactor⟩ :=
    exists_polynomial_factor_of_order_lt_one horder hrho hlp.differentiable hf0 hlp.conj
      (fun z hz => hlp.im_eq_zero_of_eq_zero hfn hz) hnp 1
  have hqdegree : q.natDegree ≠ 0 := Nat.ne_of_gt hdegree
  obtain ⟨x, hx⟩ := hq.exists_eval_eq_zero (degree_ne_of_natDegree_ne hqdegree)
  have hroot : f x = 0 := by
    rw [hfactor]
    have heq : (q.map ofRealHom).eval (x : ℂ) = 0 := by
      rw [show (x : ℂ) = ofRealHom x from rfl, eval_map, eval₂_at_apply]
      simp [hx]
    rw [heq, zero_mul]
  refine ⟨x, ?_, hroot⟩
  by_contra! hxnonneg
  have hpos := (isLaguerrePolyaTypeI_iff_isLaguerrePolya_nonneg.mp hf).2
  have hb := hlp.differentiable.re_apply_le_of_iteratedDeriv_nonneg
    (fun n _ => hpos n) hxnonneg
  rw [hroot, zero_re] at hb
  exact (not_le_of_gt h0) hb

/-- A nonpolynomial positive Type-I function of order below one has a negative
signed forward difference of some positive order in its Taylor derivatives. -/
theorem IsLaguerrePolyaTypeI.exists_signed_fwdDiff_iter_neg
    {f : ℂ → ℂ} {rho : ℝ} (hf : IsLaguerrePolyaTypeI f)
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) (h0 : 0 < (f 0).re)
    (hnp : ∀ q : ℂ[X], f ≠ fun z => q.eval z) :
    ∃ n : ℕ, n ≠ 0 ∧
      (-1 : ℝ) ^ n * ((fwdDiff 1)^[n] (fun k => (iteratedDeriv k f 0).re)) 0 < 0 := by
  obtain ⟨x, hx, hroot⟩ := hf.exists_neg_real_zero_of_order_lt_one horder hrho h0 hnp
  exact Complex.exists_signed_fwdDiff_iter_neg_of_neg_zero
    hf.toLaguerrePolya.differentiable h0 hx hroot

end RealRooted
