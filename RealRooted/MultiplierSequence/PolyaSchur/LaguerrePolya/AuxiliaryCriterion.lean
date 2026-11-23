module

public import Mathlib.RingTheory.SimpleRing.Principal
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GenusOne
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AuxiliaryInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GenusOne
import RealRooted.LaguerreInequalities.AuxiliaryRealZeros
import RealRooted.LaguerreInequalities.AuxiliaryZeroFactors
import RealRooted.Mathlib.Algebra.Polynomial.EvenCoefficients

/-!
# Cardon's fixed-auxiliary Laguerre--Pólya criterion

The same single auxiliary is used at every real center and every Taylor
index. Zero auxiliary roots are allowed. The growth hypothesis is exactly
genus one star; the real-zero consequence itself has no growth hypothesis.
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

private theorem exists_nonreal_root_of_X_pow_mul {g q : ℝ[X]} {m : ℕ}
    (hq : q.Monic) (hgq : g = X ^ m * q)
    (ha : ∃ a ∈ (g.map ofRealHom).roots, a.im ≠ 0) :
    ∃ a ∈ (q.map ofRealHom).roots, a.im ≠ 0 := by
  obtain ⟨a, ha, him⟩ := ha
  have ha0 : a ≠ 0 := fun h ↦ him (by simp [h])
  have hv : (g.map ofRealHom).eval a = 0 := isRoot_of_mem_roots ha
  rw [hgq, Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X] at hv
  refine ⟨a, (mem_roots (hq.map ofRealHom).ne_zero).mpr ?_, him⟩
  exact (mul_eq_zero.mp hv).resolve_left (pow_ne_zero m ha0)

/-- A fixed monic even auxiliary with a nonreal root detects all nonreal
zeros from its full family of inequalities. Zero auxiliary roots are allowed. -/
theorem im_eq_zero_of_auxiliaryCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hne : f ≠ 0)
    {g : ℝ[X]} (hg : g.Monic) (he : ∀ k, Odd k → g.coeff k = 0)
    (ha : ∃ a ∈ (g.map ofRealHom).roots, a.im ≠ 0)
    (h : ∀ x k, 0 ≤ auxiliaryCoefficient g f x k) {z : ℂ} (hz : f z = 0) :
    z.im = 0 := by
  obtain ⟨m, q, hm, hq, hq0, hqe, hgq⟩ := hg.exists_even_X_pow_mul he
  have hroot := exists_nonreal_root_of_X_pow_mul hq hgq ha
  have hqnonneg (x : ℝ) (k : ℕ) : 0 ≤ auxiliaryCoefficient q f x k :=
    auxiliaryCoefficient_nonneg_of_X_pow_mul hf hc hne hq hm
      (by simpa only [hgq] using h) x k
  exact im_eq_zero_of_auxiliary_nonneg_of_coeff_zero_ne_zero
    hf hc hne hqe hq0 hroot hqnonneg hz

/-- Cardon's Theorem 2.1: for a real genus-one-star entire function, any
fixed admissible auxiliary gives a complete Laguerre--Pólya criterion. -/
theorem isLaguerrePolya_iff_auxiliaryCoefficient_nonneg {f : ℂ → ℂ}
    (hf : HasGenusOneStar f) (hc : ∀ z, f (conj z) = conj (f z))
    {g : ℝ[X]} (hg : g.Monic) (he : ∀ k, Odd k → g.coeff k = 0)
    (hgn : HasNonnegCoeffs g) (ha : ∃ a ∈ (g.map ofRealHom).roots, a.im ≠ 0) :
    IsLaguerrePolya f ↔ ∀ x k, 0 ≤ auxiliaryCoefficient g f x k := by
  constructor
  · exact fun h x k ↦ h.auxiliaryCoefficient_nonneg hg he hgn x k
  · intro h
    exact isLaguerrePolya_of_hasGenusOneStar hf hc fun _ hz ↦
      im_eq_zero_of_auxiliaryCoefficient_nonneg hf.differentiable hc hf.ne_zero hg he ha h hz

end RealRooted
