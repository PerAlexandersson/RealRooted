module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.LaguerreInequalities.Analytic
import RealRooted.LaguerreInequalities.GeneratingPolynomial
import RealRooted.Mathlib.Analysis.Complex.Polynomial.CoefficientMajorant
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct

/-!
# Modulus bounds for symmetric products

The product of opposite translates of a Laguerre--Pólya function is bounded on
a complex disk by its value at the imaginary endpoints of the diameter.
This follows from the nonnegative coefficients of the generalized Laguerre
generating polynomial and passage to locally uniform polynomial limits.
-/

public section

open Complex Polynomial Filter Topology

namespace RealRooted

private theorem norm_laguerreProduct_polynomial_le {p : ℝ[X]} (hp : p.Splits)
    (x : ℝ) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖laguerreProduct (fun w => (p.map ofRealHom).eval w) x z‖ ≤
      ‖(p.map ofRealHom).eval (x + (R : ℂ) * I)‖ ^ 2 := by
  let q := laguerreGeneratingPolynomial p x
  have hq : ∀ k, 0 ≤ q.coeff k :=
    (isPFPolynomial_laguerreGeneratingPolynomial p x).hasNonnegCoeffs
  have hbound := Polynomial.norm_eval_map_le_of_coeff_nonneg hq
    (z := z ^ 2) (R := R ^ 2)
    (by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg z) hz 2)
  have hqR : q.eval (R ^ 2) = ‖(p.map ofRealHom).eval (x + (R : ℂ) * I)‖ ^ 2 := by
    apply ofReal_injective
    rw [← ofRealHom_eq_coe, ← Polynomial.eval_map_apply]
    change ((laguerreGeneratingPolynomial p x).map ofRealHom).eval (ofRealHom (R ^ 2)) = _
    rw [ofRealHom_eq_coe, ofReal_pow, eval_laguerreGeneratingPolynomial hp]
    exact laguerreProduct_ofReal (f := fun w => (p.map ofRealHom).eval w)
      (isLaguerrePolya_eval_map hp).conj x R
  rw [hqR] at hbound
  simpa only [q, eval_laguerreGeneratingPolynomial hp, laguerreProduct] using hbound

/-- Symmetric products of Laguerre--Pólya functions have a radial majorant
provided by their squared modulus above the real axis. -/
theorem IsLaguerrePolya.norm_laguerreProduct_le {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (x : ℝ) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖laguerreProduct f x z‖ ≤ ‖f (x + (R : ℂ) * I)‖ ^ 2 := by
  obtain ⟨p, hp, ht⟩ := hf
  have hpoint (w : ℂ) := ht.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ w)
  apply le_of_tendsto_of_tendsto'
    (((hpoint (x + z * I)).mul (hpoint (x - z * I))).norm)
    ((hpoint (x + (R : ℂ) * I)).norm.pow 2)
  intro n
  exact norm_laguerreProduct_polynomial_le
    ((hp n).elim (fun h => h ▸ Splits.zero) id) x hz

/-- The opposite-translate product is bounded on a disk by the value on its
imaginary diameter. The zero function is included. -/
theorem IsLaguerrePolya.norm_mul_add_sub_le {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    (x : ℝ) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖f (x + z) * f (x - z)‖ ≤ ‖f (x + (R : ℂ) * I)‖ ^ 2 := by
  have h := hf.norm_laguerreProduct_le x (z := z * (-I)) (by simpa using hz)
  have hi : z * (-I) * I = z := by simp [mul_assoc, neg_mul]
  simpa only [laguerreProduct, hi] using h

end RealRooted
